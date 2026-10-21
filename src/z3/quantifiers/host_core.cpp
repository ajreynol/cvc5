/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The ported core under cvc5's propositional engine.
 */

#include "z3/quantifiers/host_core.h"

#include <algorithm>
#include <cstdint>

#include "base/output.h"
#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "options/z3_options.h"
#include "prop/prop_engine.h"
#include "smt/env.h"
#include "theory/decision_manager.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/skolem_lemma.h"
#include "theory/theory_engine.h"
#include "z3/relevancy/prop_core.h"
#include "z3/quantifiers/lemma_proof_generator.h"
#include "z3/quantifiers/shadow_feed.h"
#include "z3/quantifiers/smt_context.h"

namespace cvc5::internal {
namespace z3 {

namespace {

/**
 * How many times in a row a full check retries the final check of the
 * theory side when it asks to continue without telling cvc5 anything new.
 */
constexpr size_t s_maxSilentFinalChecks = 10;

}  // namespace

HostCore::HostCore(Env& env,
                   theory::quantifiers::QuantifiersInferenceManager& qim,
                   Skolemizer skolemizer)
    : EnvObj(env),
      d_ctx(nullptr),
      d_te(nullptr),
      d_qim(qim),
      d_skolemizer(std::move(skolemizer)),
      d_setup(false),
      d_inConflict(false),
      d_conflictLevel(0),
      d_needCheck(false),
      d_popLevel(UINT32_MAX)
{
  d_params.initialize(env.getOptions());
  d_popNotify = std::make_unique<PopNotify>(context(), *this);
  d_feed = std::make_unique<ShadowFeed>(env, *this);
  d_splitStrategy = std::make_unique<SplitStrategy>(env, d_te);
  d_pg = std::make_unique<LemmaProofGenerator>(env);
}

HostCore::~HostCore() {}

void HostCore::reset(TheoryEngine* te)
{
  d_ctx.reset(new SmtContext(d_env, d_params));
  d_te = te;
  d_setup = false;
  d_inConflict = false;
  d_needCheck = false;
  d_popLevel = UINT32_MAX;
  d_preregistered.clear();
  d_lemmasSent.clear();
  d_hostAtom.clear();
  d_pg = std::make_unique<LemmaProofGenerator>(d_env);
  d_lemmaIds.clear();
  d_splitAtoms.clear();
  d_splitStrategy->clear();
  d_ctx->setInstanceMaker(
      [this](TNode q, const std::vector<Node>& terms, std::vector<Node>& defs) {
        return mkInstance(q, terms, defs);
      });
  d_ctx->setSkolemizer([this](TNode q, std::vector<Node>& defs) {
    return mkSkolemization(q, defs);
  });
}

SmtContext& HostCore::getContext()
{
  Assert(d_ctx != nullptr);
  return *d_ctx;
}

PropCore& HostCore::getPropCore() { return getContext().getPropCore(); }

void HostCore::lemma(const Node& lem, theory::LemmaProperty p)
{
  if (lem.isConst())
  {
    return;
  }
  auto it = d_lemmaIds.find(lem);
  Assert(it != d_lemmaIds.end());
  theory::InferenceId id = it == d_lemmaIds.end()
                               ? theory::InferenceId::QUANTIFIERS_INST_Z3
                               : it->second;
  // an instance, sent as cvc5's instantiation lemma, or the definition of a
  // skolem, with their proofs
  TrustNode trn = d_pg->getLemmaFor(lem);
  if (!trn.isNull())
  {
    d_qim.trustedLemma(trn, id, p);
    return;
  }
  if (d_pg->hasProofFor(lem))
  {
    // a lemma weakened by delayUnit
    d_qim.trustedLemma(TrustNode::mkTrustLemma(lem, d_pg.get()), id, p);
    return;
  }
  d_qim.lemma(lem, id, p);
}

Node HostCore::preprocessForTheories(TNode n,
                                     std::vector<Node>& defs,
                                     TrustNode& pp,
                                     theory::InferenceId id)
{
  // cvc5 preprocesses the lemmas the core sends as it does any other, so the
  // core takes them in the same form: cvc5's preprocessing of their form for
  // cvc5, renamed back to the core's. cvc5 gives the definition of a skolem
  // only when it introduces it, here, so the core sends the definitions,
  // with their proofs.
  std::vector<theory::SkolemLemma> sks;
  Node h = toHost(n);
  TrustNode trn = d_te->getPropEngine()->preprocess(h, sks);
  for (const theory::SkolemLemma& sk : sks)
  {
    Node d = toCore(sk.getProven());
    Node hd = toHost(d);
    if (hd == sk.getProven())
    {
      d_pg->notifyPreprocessed(sk.getProven(), sk.d_lemma, TrustNode::null());
    }
    d_lemmaIds.emplace(hd, id);
    defs.push_back(d);
  }
  pp = trn;
  return toCore(trn.isNull() ? h : trn.getNode());
}

Node HostCore::mkInstance(TNode q,
                          const std::vector<Node>& terms,
                          std::vector<Node>& defs)
{
  // cvc5's instantiation lemma of q, in cvc5's form, which the core sends,
  // and which cvc5 preprocesses into the form the core takes
  Node lem = d_pg->mkInstance(toHost(q), terms);
  bool proofs = d_env.isTheoryProofProducing();
  return preprocessLemma(
      TrustNode::mkTrustLemma(lem, proofs ? d_pg.get() : nullptr),
      defs,
      theory::InferenceId::QUANTIFIERS_INST_Z3);
}

Node HostCore::mkSkolemization(TNode q, std::vector<Node>& defs)
{
  return preprocessLemma(d_skolemizer(toHost(q)),
                         defs,
                         theory::InferenceId::QUANTIFIERS_SKOLEMIZE);
}

Node HostCore::preprocessLemma(const TrustNode& trn,
                               std::vector<Node>& defs,
                               theory::InferenceId id)
{
  Node lem = trn.getProven();
  TrustNode pp;
  Node norm = preprocessForTheories(lem, defs, pp, id);
  Node form = pp.isNull() ? lem : pp.getNode();
  Node hnorm = toHost(norm);
  // the core sends norm as form, and cvc5 is sent lem for it
  if (hnorm == form)
  {
    d_pg->notifyPreprocessed(form, trn, pp);
  }
  d_lemmaIds.emplace(hnorm, id);
  return norm;
}

void HostCore::assertInput(const std::vector<Node>& assertions)
{
  PropCore& core = getPropCore();
  for (const Node& a : assertions)
  {
    core.assertFormula(toCore(a));
  }
}

void HostCore::preRegister(TNode atom)
{
  // The atoms of the input are internalized with the asserted formulas when
  // the search starts; the others are internalized at the next check.
  Trace("z3-host") << "preregister " << atom << std::endl;
  Node a = toCore(atom);
  if (d_setup)
  {
    d_preregistered.push_back(a);
  }
}

void HostCore::assertFact(TNode literal)
{
  if (d_inConflict)
  {
    return;
  }
  PropCore& core = getPropCore();
  syncLevel();
  Trace("z3-host") << "assert " << literal << std::endl;
  Literal l = core.hostLiteral(toCore(literal));
  if (!core.hostAssign(l))
  {
    enterConflict();
  }
}

void HostCore::check(theory::Theory::Effort effort)
{
  d_needCheck = false;
  Statistics& stats = getContext().getStats();
  stats.d_numHostChecks++;
  if (theory::Theory::fullEffort(effort))
  {
    stats.d_numHostFullChecks++;
  }
  Trace("z3-host") << "check " << effort << " at level "
                   << context()->getLevel() << " inConflict "
                   << d_inConflict << std::endl;
  if (d_inConflict)
  {
    // The core's conflict is for cvc5's theories to find, and they have not
    // yet. A full check must then not let the model through.
    if (theory::Theory::fullEffort(effort))
    {
      d_qim.setModelUnsound(theory::IncompleteId::UNKNOWN);
    }
    return;
  }
  PropCore& core = getPropCore();
  syncLevel();
  // the equalities cvc5's theories derived since the last check
  d_feed->apply();
  if (context()->getLevel() <= 1 && !d_delayedUnits.empty())
  {
    // As Z3 asserts its delayed units after a restart, the lemmas weakened
    // by delayUnit are sent as they are near the base level, where CaDiCaL
    // backtracks at most one level for them.
    for (const Node& du : d_delayedUnits)
    {
      if (d_lemmasSent.insert(du).second)
      {
        lemma(du, theory::LemmaProperty::NONE);
        d_needCheck = true;
      }
    }
    d_delayedUnits.clear();
  }
  for (const Node& atom : d_preregistered)
  {
    core.hostLiteral(atom);
  }
  d_preregistered.clear();
  if (!propagateAndReport())
  {
    return;
  }
  if (!theory::Theory::fullEffort(effort) || d_needCheck)
  {
    Trace("z3-host") << "check returns: needCheck " << d_needCheck << std::endl;
    return;
  }
  for (size_t i = 0; i < s_maxSilentFinalChecks; ++i)
  {
    FinalCheckStatus st = core.hostFinalCheck();
    Trace("z3-host") << "final check " << st << " at level "
                     << context()->getLevel() << std::endl;
    if (st == FC_DONE)
    {
      // The core's own search reaches a final check only once every relevant
      // variable is assigned, while cvc5 may stop on a partial assignment.
      // The relevant variables left are decided first, through splitting
      // lemmas that cvc5's decision heuristic must justify.
      splitPendingAtoms();
      if (d_needCheck)
      {
        return;
      }
      // The ground part of the model is cvc5's theories'; the quantified
      // formulas are not checked against it.
      if (getContext().hasQuantifiers())
      {
        d_qim.setModelUnsound(theory::IncompleteId::QUANTIFIERS);
      }
      return;
    }
    // FC_CONTINUE: the theory side made progress
    if (!propagateAndReport())
    {
      return;
    }
    splitPendingAtoms();
    if (d_needCheck)
    {
      return;
    }
  }
  d_qim.setModelUnsound(theory::IncompleteId::UNKNOWN);
}

void HostCore::presolve()
{
  if (!d_setup)
  {
    getPropCore().hostInit();
    d_setup = true;
  }
  // The strategies of the decision manager are cleared after each check-sat.
  d_te->getDecisionManager()->registerStrategy(
      theory::DecisionManager::STRAT_QUANT_Z3_SPLIT, d_splitStrategy.get());
}

void HostCore::notifyPop()
{
  // The core follows when it is next asked something (syncLevel): a
  // backjump pops the SAT context one level at a time, and the core pops
  // all of them at once, down to the lowest level reached, even if the SAT
  // context has pushed again since.
  uint32_t lvl = context()->getLevel();
  if (lvl < d_popLevel)
  {
    d_popLevel = lvl;
  }
  d_feed->notifyPop();
  if (!d_setup)
  {
    return;
  }
  // The core's conflict, at d_conflictLevel, holds until the SAT context
  // pops below it; cvc5 may pop to shallower levels that still hold it.
  if (lvl < d_conflictLevel)
  {
    d_inConflict = false;
  }
}

void HostCore::syncLevel()
{
  PropCore& core = getPropCore();
  uint32_t lvl = context()->getLevel();
  // The scopes above the lowest level the SAT context reached since the last
  // call belong to a branch it left, even if it is now as deep again.
  uint32_t popTo = std::min(lvl, d_popLevel);
  d_popLevel = UINT32_MAX;
  if (core.getScopeLevel() > popTo)
  {
    Statistics& stats = getContext().getStats();
    stats.d_numHostPops++;
    stats.d_numHostScopesPopped += core.getScopeLevel() - popTo;
    if (popTo == 0)
    {
      stats.d_numHostRestarts++;
    }
    core.hostSyncLevel(popTo);
  }
  core.hostSyncLevel(lvl);
}

void HostCore::enterConflict()
{
  // The conflict follows from the facts cvc5 asserted and the lemmas it was
  // sent, so cvc5's theories find it themselves. Until cvc5 backtracks below
  // the current level, the core does nothing.
  getContext().getStats().d_numShadowConflicts++;
  d_inConflict = true;
  d_conflictLevel = context()->getLevel();
}

void HostCore::sendLemmas()
{
  std::vector<Node> lems;
  std::vector<Node> insts;
  getPropCore().hostTakeLemmas(lems, insts);
  // An instance is local to the SAT context (--z3-host-local-instances, the
  // default), as with cvc5's --inst-local: cvc5 adds its clause once, but its
  // decision heuristic treats it as an assertion only in the context where
  // it was last made. The core makes it again when matching finds it again
  // after backtracking, as Z3 does, and it is then sent again, which makes it
  // an assertion there again. Otherwise an instance is sent once.
  bool local = options().z3.z3HostLocalInstances;
  for (const Node& inst : insts)
  {
    sendLemma(inst, local);
  }
  for (const Node& lem : lems)
  {
    sendLemma(lem, false);
  }
}

void HostCore::sendLemma(const Node& coreLem, bool local)
{
  Statistics& stats = getContext().getStats();
  Node lem = toHost(coreLem);
  // cvc5 keeps its lemmas, while the core makes an instance or an axiom
  // again after backtracking, so a lemma is sent once. A lemma weakened by
  // delayUnit holds only under the first decision it was weakened with, so
  // it is sent again when the core makes it again, as is or weakened by the
  // first decision of then.
  Node sent = lem;
  if (d_lemmasSent.find(lem) == d_lemmasSent.end())
  {
    sent = delayUnit(lem);
  }
  if (d_lemmasSent.insert(sent).second)
  {
    stats.d_numHostLemmas++;
  }
  else
  {
    stats.d_numHostDuplicateLemmas++;
    if (!local)
    {
      return;
    }
  }
  lemma(
      sent, local ? theory::LemmaProperty::LOCAL : theory::LemmaProperty::NONE);
  d_needCheck = true;
}

Node HostCore::delayUnit(const Node& lem)
{
  if (!options().z3.z3HostDelayUnits || context()->getLevel() < 2)
  {
    return lem;
  }
  prop::PropEngine* pe = d_te->getPropEngine();
  std::vector<Node> disj;
  if (lem.getKind() == Kind::OR)
  {
    disj.insert(disj.end(), lem.begin(), lem.end());
  }
  else
  {
    disj.push_back(lem);
  }
  // the disjuncts that are not false at the base level
  size_t open = 0;
  for (const Node& d : disj)
  {
    bool pol = d.getKind() != Kind::NOT;
    TNode atom = pol ? d : d[0];
    bool value;
    if (pe->isSatLiteral(atom) && pe->isFixed(atom)
        && pe->hasValue(atom, value))
    {
      if (value == pol)
      {
        // satisfied at the base level, which CaDiCaL ignores
        return lem;
      }
      continue;
    }
    if (++open > 1)
    {
      return lem;
    }
  }
  std::vector<Node> decisions = pe->getPropDecisions();
  if (decisions.empty())
  {
    return lem;
  }
  // null when proofs are produced and lem has none
  Node weakened = d_pg->mkWeakened(lem, decisions[0]);
  if (weakened.isNull())
  {
    return lem;
  }
  auto it = d_lemmaIds.find(lem);
  if (it != d_lemmaIds.end())
  {
    d_lemmaIds.emplace(weakened, it->second);
  }
  getContext().getStats().d_numHostDelayedUnits++;
  d_delayedUnits.push_back(lem);
  return weakened;
}

void HostCore::splitNewlyRelevant()
{
  PropCore& core = getPropCore();
  std::vector<Node> rel;
  core.hostTakeRelevant(rel);
  prop::PropEngine* pe = d_te->getPropEngine();
  for (const Node& n : rel)
  {
    // A variable cvc5 knows is decided by its heuristic when an assertion
    // needs it; the core's own variables (the conditions of term ITEs, for
    // instance) are decided only through a split.
    if (!core.bInternalized(n) || pe->isSatLiteral(toHost(n)))
    {
      continue;
    }
    BoolVar v = core.getBoolVar(n);
    if (core.getAssignment(v) == L_UNDEF && core.isRelevant(v))
    {
      split(v);
    }
  }
}

void HostCore::split(BoolVar v)
{
  PropCore& core = getPropCore();
  prop::PropEngine* pe = d_te->getPropEngine();
  TNode atom = core.boolVar2Expr(v);
  if (atom.isNull() || atom.isConst())
  {
    return;
  }
  // The core has variables for the not-gates nested in terms; cvc5 decides
  // their argument.
  bool pol = atom.getKind() != Kind::NOT;
  Node a = toHost(pol ? atom : atom[0]);
  if (expr::hasFreeVar(a))
  {
    // not an atom of the search: the core has variables for the atoms in
    // the patterns and bodies of quantifiers
    return;
  }
  if (!pe->isSatLiteral(a))
  {
    // an atom of the core's own ground reasoning, which cvc5's theories do
    // instead
    return;
  }
  if (!d_splitAtoms.insert(a).second)
  {
    return;
  }
  d_splitStrategy->add(a);
  getContext().getStats().d_numHostSplits++;
  // cvc5 must search on, for the decision, even after a full check
  d_qim.markUsed();
  d_needCheck = true;
}

Node HostCore::SplitStrategy::getNextDecisionRequest()
{
  prop::PropEngine* pe = d_te->getPropEngine();
  for (const Node& a : d_atoms)
  {
    bool value;
    if (!pe->hasValue(a, value))
    {
      return a;
    }
  }
  return Node::null();
}

void HostCore::splitPendingAtoms()
{
  PropCore& core = getPropCore();
  for (size_t i = 0, n = core.getNumBoolVars(); i < n; ++i)
  {
    BoolVar v = static_cast<BoolVar>(i);
    if (core.getAssignment(v) == L_UNDEF && core.isRelevant(v))
    {
      split(v);
    }
  }
}

bool HostCore::propagateAndReport()
{
  PropCore& core = getPropCore();
  bool ok = core.hostPropagate();
  // the instances and axioms made before a conflict hold regardless
  sendLemmas();
  if (!ok)
  {
    enterConflict();
    return false;
  }
  splitNewlyRelevant();
  return true;
}

Node HostCore::toCore(TNode n)
{
  Node nc = getContext().getNormalizer().normalize(n);
  if (nc != n)
  {
    recordRenamedAtoms(n, nc);
  }
  return nc;
}

void HostCore::recordRenamedAtoms(TNode n, TNode nc)
{
  // The renaming changes only the quantified formulas, so n and nc have the
  // same Boolean structure above their atoms.
  if (n == nc)
  {
    return;
  }
  if (expr::isBooleanConnective(n) && nc.getKind() == n.getKind()
      && nc.getNumChildren() == n.getNumChildren())
  {
    for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; ++i)
    {
      recordRenamedAtoms(n[i], nc[i]);
    }
    return;
  }
  d_hostAtom.emplace(nc, n);
}

Node HostCore::toHost(TNode n)
{
  if (d_hostAtom.empty() || !expr::hasClosure(n))
  {
    return n;
  }
  auto it = d_hostAtom.find(n);
  if (it != d_hostAtom.end())
  {
    return it->second;
  }
  if (!expr::isBooleanConnective(n))
  {
    return n;
  }
  NodeBuilder nb(nodeManager(), n.getKind());
  for (const Node& c : n)
  {
    nb << toHost(c);
  }
  return nb.constructNode();
}

}  // namespace z3
}  // namespace cvc5::internal

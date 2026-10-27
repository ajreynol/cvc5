/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The quantifiers module of the ported Z3 core.
 */

#include "z3/quantifiers/z3_module.h"

#include <ctime>

#include "base/output.h"
#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "options/base_options.h"
#include "options/z3_options.h"
#include "prop/prop_engine.h"
#include "theory/decision_manager.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/skolemize.h"
#include "theory/skolem_lemma.h"
#include "theory/theory_engine.h"
#include "z3/quantifiers/lemma_proof_generator.h"
#include "z3/quantifiers/smt_context.h"

namespace cvc5::internal {
namespace z3 {

Z3Module::Z3Module(Env& env,
                   theory::quantifiers::QuantifiersState& qs,
                   theory::quantifiers::QuantifiersInferenceManager& qim,
                   theory::quantifiers::QuantifiersRegistry& qr,
                   theory::quantifiers::TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_te(nullptr),
      d_setup(false),
      d_inConflict(false),
      d_conflictLevel(0),
      d_needCheck(false),
      d_popLevel(UINT32_MAX),
      d_pg(std::make_unique<LemmaProofGenerator>(env)),
      d_popNotify(std::make_unique<PopNotify>(context(), *this))
{
}

Z3Module::~Z3Module() {}

void Z3Module::finishInit(TheoryEngine* te)
{
  d_te = te;
  d_core = std::make_unique<SmtContext>(d_env, *this);
  d_tracker = std::make_unique<RelevancyTracker>(d_env, te, *this);
  te->addModule(d_tracker.get());
}

void Z3Module::presolve()
{
  d_core->getEGraph().setMasterEqualityEngine(d_qstate.getEqualityEngine());
  if (!d_setup)
  {
    d_core->setupSearch();
    d_setup = true;
  }
}

void Z3Module::ppNotifyAssertions(const std::vector<Node>& assertions)
{
  for (const Node& a : assertions)
  {
    d_core->assertFormula(toCore(a));
  }
}

bool Z3Module::needsCheck(theory::Theory::Effort e)
{
  return e != theory::Theory::EFFORT_LAST_CALL;
}

void Z3Module::check(theory::Theory::Effort e, QEffort quant_e)
{
  // once per check of the quantifiers engine, at its first effort, so that
  // the other modules run only in a round where the core sent no lemma
  if (quant_e != QEFFORT_CONFLICT)
  {
    return;
  }
  // -o inst-strategy prints a line per call that sent lemmas, as for the
  // other modules, which count them through the inference manager; the core
  // sends its lemmas itself, rather than buffering them. It is called at
  // every standard effort check, most of which send none.
  bool printing = isOutputOn(OutputTag::INST_STRATEGY);
  uint32_t numLemmas = d_qim.numSentLemmas();
  clock_t start = printing ? clock() : 0;
  checkCore(e);
  if (printing && d_qim.numSentLemmas() > numLemmas)
  {
    double time = static_cast<double>(clock() - start)
                  / static_cast<double>(CLOCKS_PER_SEC);
    std::ostream& out = output(OutputTag::INST_STRATEGY);
    out << "(inst-strategy " << identify();
    out << " :inst " << (d_qim.numSentLemmas() - numLemmas);
    out << " :time " << time;
    if (d_qstate.isInConflict())
    {
      out << " :conflict";
    }
    out << ")" << std::endl;
  }
}

void Z3Module::preRegisterQuantifier(Node q)
{
  // The core takes the atoms of the SAT solver; it internalizes the terms
  // under them itself.
  if (d_qstate.getValuation().isSatLiteral(q))
  {
    preRegister(q);
  }
}

void Z3Module::notifyMasterMerge(TNode t1, TNode t2)
{
  d_core->getEGraph().notifyMasterMerge(t1, t2);
}

// ------------------------------------------------- the boundary with cvc5
//
// The search of the core under cvc5's propositional engine, and the lemmas it
// sends cvc5.

namespace {

/**
 * How many times in a row a full check retries the final check of the
 * theory side when it asks to continue without telling cvc5 anything new.
 */
constexpr size_t s_maxSilentFinalChecks = 10;

}  // namespace

void Z3Module::lemma(const Node& lem, theory::LemmaProperty p)
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

Node Z3Module::preprocessForTheories(TNode n,
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

Node Z3Module::mkInstance(TNode q,
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

Node Z3Module::mkSkolemization(TNode q, std::vector<Node>& defs)
{
  return preprocessLemma(getSkolemization(toHost(q)),
                         defs,
                         theory::InferenceId::QUANTIFIERS_SKOLEMIZE);
}

Node Z3Module::preprocessLemma(const TrustNode& trn,
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

void Z3Module::preRegister(TNode atom)
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

void Z3Module::assertFact(TNode literal)
{
  if (d_inConflict)
  {
    return;
  }
  syncLevel();
  Trace("z3-host") << "assert " << literal << std::endl;
  SatLiteral l = d_core->literalOf(toCore(literal));
  if (!d_core->getPropCore().hostAssign(l))
  {
    enterConflict();
  }
}

void Z3Module::checkCore(theory::Theory::Effort effort)
{
  // the literals asserted since the last check
  d_tracker->flush(d_qstate);
  d_needCheck = false;
  Statistics& stats = d_core->getStats();
  stats.d_numHostChecks++;
  if (theory::Theory::fullEffort(effort))
  {
    stats.d_numHostFullChecks++;
  }
  Trace("z3-host") << "check " << effort << " at level "
                   << context()->getLevel() << " inConflict " << d_inConflict
                   << std::endl;
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
  syncLevel();
  // the equalities cvc5's theories derived since the last check
  d_core->getEGraph().applyMasterMerges();
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
    d_core->literalOf(atom);
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
    bool done = d_core->finalCheck();
    Trace("z3-host") << "final check " << (done ? "done" : "continue")
                     << " at level " << context()->getLevel() << std::endl;
    if (done)
    {
      if (d_needCheck)
      {
        return;
      }
      // The ground part of the model is cvc5's theories'; the quantified
      // formulas are not checked against it.
      if (d_core->hasQuantifiers())
      {
        d_qim.setModelUnsound(theory::IncompleteId::QUANTIFIERS);
      }
      return;
    }
    // not done: the theory side made progress
    if (!propagateAndReport())
    {
      return;
    }
    if (d_needCheck)
    {
      return;
    }
  }
  d_qim.setModelUnsound(theory::IncompleteId::UNKNOWN);
}

TrustNode Z3Module::getSkolemization(TNode q)
{
  // The lemma is made once per user context, by the quantifiers engine when
  // q is asserted false (or here, for a quantified formula it reduced), while
  // the core asserts it again each time q is assigned false after a
  // backtrack.
  theory::quantifiers::Skolemize* sk = d_qim.getSkolemize();
  sk->process(q);
  TrustNode lem = sk->getSkolemizationLemma(q);
  Assert(!lem.isNull());
  return lem;
}

void Z3Module::notifyPop()
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
  // the merges notified and not applied are void
  d_core->getEGraph().clearPendingMasterMerges();
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

void Z3Module::syncLevel()
{
  uint32_t lvl = context()->getLevel();
  // The scopes above the lowest level the SAT context reached since the last
  // call belong to a branch it left, even if it is now as deep again.
  uint32_t popTo = std::min(lvl, d_popLevel);
  d_popLevel = UINT32_MAX;
  if (d_core->getScopeLevel() > popTo)
  {
    Statistics& stats = d_core->getStats();
    stats.d_numHostPops++;
    stats.d_numHostScopesPopped += d_core->getScopeLevel() - popTo;
    if (popTo == 0)
    {
      stats.d_numHostRestarts++;
    }
    d_core->setScopeLevel(popTo);
  }
  d_core->setScopeLevel(lvl);
}

void Z3Module::enterConflict()
{
  // The conflict follows from the facts cvc5 asserted and the lemmas it was
  // sent, so cvc5's theories find it themselves. Until cvc5 backtracks below
  // the current level, the core does nothing.
  d_core->getStats().d_numShadowConflicts++;
  d_inConflict = true;
  d_conflictLevel = context()->getLevel();
}

void Z3Module::sendLemma(const Node& coreLem, bool local)
{
  Statistics& stats = d_core->getStats();
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
  lemma(sent,
        local ? theory::LemmaProperty::LOCAL : theory::LemmaProperty::NONE);
  d_needCheck = true;
}

Node Z3Module::delayUnit(const Node& lem)
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
  d_core->getStats().d_numHostDelayedUnits++;
  d_delayedUnits.push_back(lem);
  return weakened;
}

bool Z3Module::propagateAndReport()
{
  bool ok = d_core->propagate();
  if (!ok)
  {
    enterConflict();
    return false;
  }
  return true;
}

Node Z3Module::toCore(TNode n)
{
  Node nc = d_core->getNormalizer().normalize(n);
  if (nc != n)
  {
    recordRenamedAtoms(n, nc);
  }
  return nc;
}

void Z3Module::recordRenamedAtoms(TNode n, TNode nc)
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

Node Z3Module::toHost(TNode n)
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

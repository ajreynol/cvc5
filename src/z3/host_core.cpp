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

#include "z3/host_core.h"

#include <algorithm>
#include <cstdint>

#include "base/output.h"
#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "options/z3_options.h"
#include "prop/prop_engine.h"
#include "smt/env.h"
#include "theory/skolem_lemma.h"
#include "theory/theory_engine.h"
#include "z3/prop_core.h"
#include "z3/shadow_feed.h"
#include "z3/shared_backend.h"
#include "z3/smt_context.h"

namespace cvc5::internal {
namespace z3 {

namespace {

/**
 * How many times in a row a full check retries the final check of the
 * theory side when it asks to continue without telling cvc5 anything new.
 */
constexpr size_t s_maxSilentFinalChecks = 10;

}  // namespace

HostCore::HostCore(Env& env, SharedBackend& backend, HostCoreOutput& out)
    : EnvObj(env),
      d_backend(backend),
      d_te(nullptr),
      d_out(out),
      d_setup(false),
      d_inConflict(false),
      d_conflictLevel(0),
      d_needCheck(false),
      d_popLevel(UINT32_MAX)
{
  d_popNotify = std::make_unique<PopNotify>(context(), *this);
  d_feed = std::make_unique<ShadowFeed>(env, backend);
}

HostCore::~HostCore() {}

void HostCore::reset(TheoryEngine* te)
{
  d_te = te;
  d_setup = false;
  d_inConflict = false;
  d_needCheck = false;
  d_popLevel = UINT32_MAX;
  d_preregistered.clear();
  d_lemmasSent.clear();
  d_backend.getContext().setCvc5Preprocessor(
      [this](TNode n, std::vector<Node>& defs) {
        return preprocessForTheories(n, defs);
      });
}

Node HostCore::preprocessForTheories(TNode n, std::vector<Node>& defs)
{
  if (!expr::hasClosure(n))
  {
    std::vector<theory::SkolemLemma> sks;
    TrustNode trn = d_te->getPropEngine()->preprocess(n, sks);
    for (const theory::SkolemLemma& sk : sks)
    {
      defs.push_back(sk.getProven());
    }
    return trn.isNull() ? Node(n) : trn.getNode();
  }
  // cvc5's rewriter would restructure a quantifier, which the core and cvc5
  // know as one atom, so only the parts outside the quantifiers are
  // preprocessed: the Boolean structure above them is followed, a quantifier
  // is left as it is, and so are the closures in an atom.
  if (n.isClosure())
  {
    return n;
  }
  if (!expr::isBooleanConnective(n))
  {
    return preprocessAroundClosures(n, defs);
  }
  NodeBuilder nb(nodeManager(), n.getKind());
  for (const Node& c : n)
  {
    nb << preprocessForTheories(c, defs);
  }
  return nb.constructNode();
}

Node HostCore::preprocessAroundClosures(TNode n, std::vector<Node>& defs)
{
  // Each closure is held by a placeholder constant while the atom is
  // preprocessed. The rest of the atom must be preprocessed all the same:
  // a Boolean term in an argument, for instance, is otherwise not purified,
  // and would reach cvc5's theories as a term (Verus emits such atoms for
  // its lambdas).
  std::vector<Node> closures;
  std::unordered_set<TNode> visited;
  std::vector<TNode> todo{n};
  while (!todo.empty())
  {
    TNode cur = todo.back();
    todo.pop_back();
    if (!visited.insert(cur).second || !expr::hasClosure(cur))
    {
      continue;
    }
    if (cur.isClosure())
    {
      closures.push_back(cur);
      continue;
    }
    todo.insert(todo.end(), cur.begin(), cur.end());
  }
  std::vector<Node> holders;
  for (const Node& c : closures)
  {
    auto it = d_closureHolders.find(c);
    if (it == d_closureHolders.end())
    {
      Node h = NodeManager::mkDummySkolem("z3hold", c.getType());
      it = d_closureHolders.emplace(c, h).first;
    }
    holders.push_back(it->second);
  }
  Node m = n.substitute(
      closures.begin(), closures.end(), holders.begin(), holders.end());
  std::vector<Node> mdefs;
  Node r = preprocessForTheories(m, mdefs);
  for (const Node& d : mdefs)
  {
    defs.push_back(d.substitute(
        holders.begin(), holders.end(), closures.begin(), closures.end()));
  }
  return r.substitute(
      holders.begin(), holders.end(), closures.begin(), closures.end());
}

void HostCore::preRegister(TNode atom)
{
  // The atoms of the input are internalized with the asserted formulas when
  // the search starts; the others are internalized at the next check.
  Trace("z3-host") << "preregister " << atom << std::endl;
  if (d_setup)
  {
    d_preregistered.push_back(atom);
  }
}

void HostCore::assertFact(TNode literal)
{
  if (d_inConflict)
  {
    return;
  }
  PropCore& core = d_backend.getPropCore();
  syncLevel();
  Trace("z3-host") << "assert " << literal << std::endl;
  Literal l = core.hostLiteral(literal);
  if (!core.hostAssign(l))
  {
    enterConflict();
  }
}

void HostCore::skolemize(TNode q, TNode lem)
{
  if (d_inConflict)
  {
    return;
  }
  syncLevel();
  d_backend.getContext().skolemize(q, lem);
}

void HostCore::check(theory::Theory::Effort effort)
{
  d_needCheck = false;
  Statistics& stats = d_backend.getContext().getStats();
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
      d_out.setModelUnsound(theory::IncompleteId::UNKNOWN);
    }
    return;
  }
  PropCore& core = d_backend.getPropCore();
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
        d_out.lemma(du, theory::LemmaProperty::NONE);
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
      if (d_backend.getContext().hasQuantifiers())
      {
        d_out.setModelUnsound(theory::IncompleteId::QUANTIFIERS);
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
  d_out.setModelUnsound(theory::IncompleteId::UNKNOWN);
}

void HostCore::presolve()
{
  if (!d_setup)
  {
    d_backend.getPropCore().hostInit();
    d_setup = true;
  }
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
  PropCore& core = d_backend.getPropCore();
  uint32_t lvl = context()->getLevel();
  // The scopes above the lowest level the SAT context reached since the last
  // call belong to a branch it left, even if it is now as deep again.
  uint32_t popTo = std::min(lvl, d_popLevel);
  d_popLevel = UINT32_MAX;
  if (core.getScopeLevel() > popTo)
  {
    Statistics& stats = d_backend.getContext().getStats();
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
  d_backend.getContext().getStats().d_numShadowConflicts++;
  d_inConflict = true;
  d_conflictLevel = context()->getLevel();
}

void HostCore::sendLemmas()
{
  std::vector<Node> lems;
  std::vector<Node> insts;
  d_backend.getPropCore().hostTakeLemmas(lems, insts);
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

void HostCore::sendLemma(const Node& lem, bool local)
{
  Statistics& stats = d_backend.getContext().getStats();
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
  d_out.lemma(
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
  disj.push_back(decisions[0].negate());
  d_backend.getContext().getStats().d_numHostDelayedUnits++;
  d_delayedUnits.push_back(lem);
  return nodeManager()->mkNode(Kind::OR, disj);
}

void HostCore::splitNewlyRelevant()
{
  PropCore& core = d_backend.getPropCore();
  std::vector<Node> rel;
  core.hostTakeRelevant(rel);
  prop::PropEngine* pe = d_te->getPropEngine();
  for (const Node& n : rel)
  {
    // A variable cvc5 knows is decided by its heuristic when an assertion
    // needs it; the core's own variables (the conditions of term ITEs, for
    // instance) are decided only through a split.
    if (!core.bInternalized(n) || pe->isSatLiteral(n))
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
  PropCore& core = d_backend.getPropCore();
  prop::PropEngine* pe = d_te->getPropEngine();
  TNode atom = core.boolVar2Expr(v);
  if (atom.isNull() || atom.isConst())
  {
    return;
  }
  // The core has variables for the not-gates nested in terms; cvc5 splits
  // on their argument, since lemmas are not rewritten (see literalNode).
  bool pol = atom.getKind() != Kind::NOT;
  TNode a = pol ? atom : atom[0];
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
  Node lem = nodeManager()->mkNode(Kind::OR, a, a.notNode());
  if (!d_lemmasSent.insert(lem).second)
  {
    return;
  }
  d_out.lemma(lem, theory::LemmaProperty::NONE);
  d_backend.getContext().getStats().d_numHostSplits++;
  d_needCheck = true;
}

void HostCore::splitPendingAtoms()
{
  PropCore& core = d_backend.getPropCore();
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
  PropCore& core = d_backend.getPropCore();
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

Node HostCore::literalNode(Literal l)
{
  PropCore& core = d_backend.getPropCore();
  if (l == s_trueLiteral || l == s_falseLiteral)
  {
    return nodeManager()->mkConst(l == s_trueLiteral);
  }
  // The core has variables for the not-gates nested in terms, whose negative
  // literal is cvc5's atom rather than a double negation.
  Node atom = core.boolVar2Expr(l.var());
  return l.sign() ? atom.negate() : atom;
}

}  // namespace z3
}  // namespace cvc5::internal

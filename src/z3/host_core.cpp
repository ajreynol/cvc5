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

HostCore::HostCore(Env& env,
                   SharedBackend& backend,
                   TheoryEngine& te,
                   HostCoreOutput& out)
    : EnvObj(env),
      d_backend(backend),
      d_te(te),
      d_out(out),
      d_setup(false),
      d_conflictSent(false),
      d_needCheck(false),
      d_numReported(0),
      d_reportIdx(0),
      d_popLevel(UINT32_MAX),
      d_shadow(options().z3.z3Slots != options::Z3SlotsMode::ALL)
{
  d_popNotify = std::make_unique<PopNotify>(context(), *this);
}

HostCore::~HostCore() {}

void HostCore::reset()
{
  d_setup = false;
  d_conflictSent = false;
  d_needCheck = false;
  d_numReported = 0;
  d_reportIdx = 0;
  d_popLevel = UINT32_MAX;
  d_preregistered.clear();
  d_lemmasSent.clear();
  if (d_shadow)
  {
    d_backend.getPropCore().hostSetShadow(true);
  }
  if (options().z3.z3TheoryPreprocess)
  {
    d_backend.getContext().setCvc5Preprocessor(
        [this](TNode n, std::vector<Node>& defs) {
          return preprocessForTheories(n, defs);
        });
  }
}

Node HostCore::preprocessForTheories(TNode n, std::vector<Node>& defs)
{
  if (!expr::hasClosure(n))
  {
    std::vector<theory::SkolemLemma> sks;
    TrustNode trn = d_te.getPropEngine()->preprocess(n, sks);
    for (const theory::SkolemLemma& sk : sks)
    {
      defs.push_back(sk.getProven());
    }
    return trn.isNull() ? Node(n) : trn.getNode();
  }
  // cvc5's rewriter would restructure a quantifier, which the core and cvc5
  // know as one atom, so only the parts outside the quantifiers are
  // preprocessed: the Boolean structure above them is followed, and an atom
  // with a quantifier inside is left as it is.
  if (!expr::isBooleanConnective(n))
  {
    return n;
  }
  NodeBuilder nb(nodeManager(), n.getKind());
  for (const Node& c : n)
  {
    nb << preprocessForTheories(c, defs);
  }
  return nb.constructNode();
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
  if (d_conflictSent)
  {
    return;
  }
  PropCore& core = d_backend.getPropCore();
  syncLevel();
  Trace("z3-host") << "assert " << literal << std::endl;
  Literal l = core.hostLiteral(literal);
  std::vector<Literal> conflict;
  if (!core.hostAssign(l, conflict))
  {
    sendConflict(conflict);
  }
}

void HostCore::check(theory::Theory::Effort effort)
{
  d_needCheck = false;
  d_numReported = 0;
  Statistics& stats = d_backend.getContext().getStats();
  stats.d_numHostChecks++;
  if (theory::Theory::fullEffort(effort))
  {
    stats.d_numHostFullChecks++;
  }
  Trace("z3-host") << "check " << effort << " at level "
                   << context()->getLevel() << " conflictSent "
                   << d_conflictSent << std::endl;
  if (d_conflictSent)
  {
    // The conflict sent in this context has not made cvc5 backtrack. A
    // full check must then not let the model through.
    if (theory::Theory::fullEffort(effort))
    {
      d_out.setModelUnsound(theory::IncompleteId::UNKNOWN);
    }
    return;
  }
  PropCore& core = d_backend.getPropCore();
  syncLevel();
  if (context()->getLevel() <= 1 && !d_delayedUnits.empty())
  {
    // As Z3 asserts its delayed units after a restart, the lemmas weakened
    // by delayUnit are sent as they are near the base level, where CaDiCaL
    // backtracks at most one level for them.
    for (const std::pair<Node, bool>& du : d_delayedUnits)
    {
      if (d_lemmasSent.insert(du.first).second)
      {
        d_out.lemma(du.first, theory::LemmaProperty::NONE, du.second);
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
  if (!theory::Theory::fullEffort(effort) || d_needCheck || d_numReported > 0)
  {
    Trace("z3-host") << "check returns: needCheck " << d_needCheck
                     << " propagations " << d_numReported << std::endl;
    return;
  }
  for (size_t i = 0; i < s_maxSilentFinalChecks; ++i)
  {
    Failure f = OK;
    FinalCheckStatus st = core.hostFinalCheck(f);
    Trace("z3-host") << "final check " << st << " at level "
                     << context()->getLevel() << std::endl;
    if (st == FC_GIVEUP)
    {
      d_out.setModelUnsound(theory::IncompleteId::UNKNOWN);
      return;
    }
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
      std::string reason;
      if (d_backend.getContext().hasQuantifiers())
      {
        d_out.setModelUnsound(theory::IncompleteId::QUANTIFIERS);
      }
      else if (!d_backend.getContext().canConfirmModel(reason))
      {
        d_out.setModelUnsound(theory::IncompleteId::UNKNOWN);
      }
      return;
    }
    // FC_CONTINUE: the theory side made progress
    if (!propagateAndReport())
    {
      return;
    }
    splitPendingAtoms();
    if (d_needCheck || d_numReported > 0)
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

Node HostCore::explain(TNode literal)
{
  syncLevel();
  PropCore& core = d_backend.getPropCore();
  Literal l = core.hostLiteral(literal);
  // cvc5 asks only for the explanation of a literal the core propagated,
  // which is still true there; an assumption (a literal cvc5 asserted) has
  // none, and the core would explain it as a fact of the base level.
  Assert(!core.isHostAssigned(l.var()));
  Assert(core.getAssignment(l) == L_TRUE);
  std::vector<Literal> lits;
  core.hostExplain(l, lits);
  d_backend.getContext().getStats().d_numHostExplanations++;
  NodeManager* nm = nodeManager();
  if (lits.empty())
  {
    return nm->mkConst(true);
  }
  if (lits.size() == 1)
  {
    return literalNode(lits[0]);
  }
  std::vector<Node> conj;
  for (Literal a : lits)
  {
    conj.push_back(literalNode(a));
  }
  return nm->mkNode(Kind::AND, conj);
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
  if (!d_setup)
  {
    return;
  }
  d_conflictSent = false;
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
  size_t size = core.assignedLiterals().size();
  if (d_reportIdx > size)
  {
    d_reportIdx = size;
  }
}

void HostCore::sendConflict(const std::vector<Literal>& lits)
{
  NodeManager* nm = nodeManager();
  std::vector<Node> disj;
  for (Literal l : lits)
  {
    disj.push_back(literalNode(~l));
#ifdef CVC5_ASSERTIONS
    // The conflict is made of facts cvc5 asserted, unless the core kept the
    // facts of a branch cvc5 left (see syncLevel).
    prop::PropEngine* pe = d_te.getPropEngine();
    bool val = true;
    Assert(pe->isSatLiteral(disj.back()) && pe->hasValue(disj.back(), val)
           && !val)
        << "conflict literal not false in cvc5: " << disj.back();
#endif
  }
  Node lem = disj.empty()       ? nm->mkConst(false)
             : disj.size() == 1 ? disj[0]
                                : nm->mkNode(Kind::OR, disj);
  lem = delayUnit(lem, false);
  d_out.lemma(lem, theory::LemmaProperty::NONE, true);
  d_backend.getContext().getStats().d_numHostConflicts++;
  d_conflictSent = true;
  d_needCheck = true;
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
    sendLemma(inst, local, true);
  }
  for (const Node& lem : lems)
  {
    sendLemma(lem, false, options().z3.z3HostAxiomDecisions);
  }
}

void HostCore::sendLemma(const Node& lem, bool local, bool notifyDecisions)
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
    sent = delayUnit(lem, notifyDecisions);
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
      sent,
      local ? theory::LemmaProperty::LOCAL : theory::LemmaProperty::NONE,
      notifyDecisions);
  d_needCheck = true;
}

Node HostCore::delayUnit(const Node& lem, bool notifyDecisions)
{
  if (!options().z3.z3HostDelayUnits || context()->getLevel() < 2)
  {
    return lem;
  }
  prop::PropEngine* pe = d_te.getPropEngine();
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
  d_delayedUnits.emplace_back(lem, notifyDecisions);
  return nodeManager()->mkNode(Kind::OR, disj);
}

void HostCore::collectPropagations()
{
  if (d_shadow)
  {
    // cvc5's theories explain the propagations of the ground state; the
    // core's would be explained from facts asserted to other theories
    return;
  }
  PropCore& core = d_backend.getPropCore();
  const LiteralVector& assigned = core.assignedLiterals();
  prop::PropEngine* pe = d_te.getPropEngine();
  if (d_reportIdx > assigned.size())
  {
    d_reportIdx = assigned.size();
  }
  for (; d_reportIdx < assigned.size(); ++d_reportIdx)
  {
    Literal l = assigned[d_reportIdx];
    BoolVar v = l.var();
    // Only the theory side's own propagations: what this side derives from
    // its clauses, cvc5 derives from the same clauses, or learns through a
    // conflict when the clause is this side's only (a gate of a term ITE,
    // for instance).
    if (core.isHostAssigned(v)
        || core.getJustification(v).getKind() != BJustification::JUSTIFICATION)
    {
      continue;
    }
    TNode atom = core.boolVar2Expr(v);
    if (atom.isNull() || atom.isConst() || expr::isBooleanConnective(atom)
        || !pe->isSatLiteral(atom))
    {
      continue;
    }
    d_out.propagate(literalNode(l));
    d_numReported++;
    d_backend.getContext().getStats().d_numHostPropagations++;
  }
}

void HostCore::splitNewlyRelevant()
{
  PropCore& core = d_backend.getPropCore();
  std::vector<Node> rel;
  core.hostTakeRelevant(rel);
  prop::PropEngine* pe = d_te.getPropEngine();
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
  prop::PropEngine* pe = d_te.getPropEngine();
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
  if (d_shadow && !pe->isSatLiteral(a))
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
  d_out.lemma(lem, theory::LemmaProperty::NONE, true);
  d_backend.getContext().getStats().d_numHostSplits++;
  if (core.tryTrueFirst(v) && pe->isSatLiteral(a))
  {
    d_out.preferPhase(a, pol);
  }
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
    std::vector<Literal> conflict;
    core.hostExplainConflict(conflict);
    sendConflict(conflict);
    return false;
  }
  collectPropagations();
  splitNewlyRelevant();
  return true;
}

Node HostCore::literalNode(Literal l)
{
  PropCore& core = d_backend.getPropCore();
  if (l == s_trueLiteral || l == s_falseLiteral)
  {
    return core.literal2Expr(l);
  }
  // The core has variables for the not-gates nested in terms, whose negative
  // literal is cvc5's atom rather than a double negation.
  Node atom = core.boolVar2Expr(l.var());
  return l.sign() ? atom.negate() : atom;
}

}  // namespace z3
}  // namespace cvc5::internal

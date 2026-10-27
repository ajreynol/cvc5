/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The logical context: the ported Z3 SMT d_prop.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), files
 * src/smt/smt_context.cpp and src/smt/smt_internalizer.cpp, and recast in
 * cvc5 style.
 */

#include "z3/quantifiers/smt_context.h"

#include <algorithm>
#include <cstdint>

#include "base/output.h"
#include "expr/node_algorithm.h"
#include "expr/node_manager.h"
#include "options/smt_options.h"
#include "options/z3_options.h"
#include "smt/env.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "util/resource_manager.h"
#include "z3/quantifiers/quantifier_manager.h"
#include "z3/quantifiers/z3_module.h"
#include "z3/relevancy/prop_core.h"

namespace cvc5::internal {
namespace z3 {

SmtContext::SmtContext(Env& env, Z3Module& host)
    : EnvObj(env),
      d_stats(statisticsRegistry()),
      d_host(host),
      d_prop(env, *this, d_stats),
      d_egraph(env, *this, d_trailStack, d_stats),
      d_normalizer(env.getNodeManager()),
      d_qmanager(*this),
      d_trueENode(nullptr),
      d_falseENode(nullptr),
      d_assertedFormulasQhead(0),
      d_hasQuantifiers(false),
      d_internalizingAssertions(false),
      d_searching(false),
      d_resourceOut(false),
      d_generation(0)
{
  init();
}

SmtContext::~SmtContext() { flush(); }

void SmtContext::init()
{
  Node t = nodeManager()->mkConst(true);
  d_prop.initTrue(t);
  d_trueENode = mkENode(t, true, true, false);
  Node f = nodeManager()->mkConst(false);
  d_falseENode = mkENode(f, true, true, false);
}

void SmtContext::flush()
{
  d_prop.flushRelevancy();
  d_prop.flushClauses();
  d_trailStack.reset();
}

void SmtContext::notifyMerge(ENode* r1, ENode* r2)
{
  // Relevancy must be propagated to the rest of the equivalence class, to
  // maintain the invariant on the parent lists of enodes.
  if (d_prop.isRelevant(r1->getExpr()))
  {
    d_prop.markAsRelevant(r2->getExpr());
  }
  else if (d_prop.isRelevant(r2->getExpr()))
  {
    d_prop.markAsRelevant(r1->getExpr());
  }
  d_qmanager.notifyMerge(r1, r2);
}

void SmtContext::propagateBoolENodeAssignment(ENode* r1,
                                              ENode* r2,
                                              ENode* n1,
                                              ENode* n2)
{
  Assert(n1->isBool());
  Assert(n2->isBool());
  Assert(r1->isBool());
  Assert(r2->isBool());
  if (r2 == d_falseENode || r2 == d_trueENode)
  {
    bool sign = r2 == d_falseENode;
    ENode* curr = r1;
    do
    {
      Assert(curr != d_falseENode);
      SatVariable v = enode2BoolVar(curr);
      SatLiteral l(v, sign);
      if (d_prop.getAssignment(l) != SAT_VALUE_TRUE)
      {
        d_prop.assign(l);
      }
      curr = curr->d_next;
    } while (curr != r1);
  }
  else
  {
    SatVariable v1 = enode2BoolVar(n1);
    SatVariable v2 = enode2BoolVar(n2);
    SatValue val1 = d_prop.getAssignment(v1);
    SatValue val2 = d_prop.getAssignment(v2);
    if (val1 != val2)
    {
      if (val2 == SAT_VALUE_UNKNOWN)
      {
        propagateBoolENodeAssignmentCore(n1, n2);
      }
      else
      {
        propagateBoolENodeAssignmentCore(n2, n1);
      }
    }
  }
}

void SmtContext::propagateBoolENodeAssignmentCore(ENode* source, ENode* target)
{
  // source and target are Boolean enodes that were proved equal, and the
  // variable of source is assigned; copy the assignment across the class.
  Assert(source->isBool());
  Assert(target->isBool());
  Assert(source->getRoot() == target->getRoot());
  SatVariable vSource = enode2BoolVar(source);
  SatValue val = d_prop.getAssignment(vSource);
  Assert(val != SAT_VALUE_UNKNOWN);
  bool sign = val == SAT_VALUE_FALSE;
  ENode* first = target;
  do
  {
    SatVariable v2 = enode2BoolVar(target);
    SatValue val2 = d_prop.getAssignment(v2);
    if (val2 != val)
    {
      d_prop.assign(SatLiteral(v2, sign));
    }
    target = target->getNext();
  } while (first != target);
}

bool SmtContext::addDiseq(ENode* n1, ENode* n2)
{
  // There is no theory plugin to tell of the disequality.
  return n1->getRoot() != n2->getRoot();
}

bool SmtContext::isDiseq(ENode* n1, ENode* n2) const
{
  return isDiseqCore(n1, n2, true);
}

bool SmtContext::isDiseqCore(ENode* n1,
                             ENode* n2,
                             bool checkDistinctRootValues) const
{
  Assert(n1->getSort() == n2->getSort());
  if (checkDistinctRootValues)
  {
    TNode e1 = n1->getRoot()->getExpr();
    TNode e2 = n2->getRoot()->getExpr();
    if (e1.isConst() && e2.isConst() && e1 != e2)
    {
      return true;
    }
  }
  // the equality of n1 and n2, if the E-graph has one
  Assert(NodeManager::hasOperator(Kind::EQUAL));
  ENode* args[2] = {n1, n2};
  ENode* r = const_cast<EGraph&>(d_egraph).getENodeEqTo(
      nodeManager()->operatorOf(Kind::EQUAL), true, 2, args);
  if (r != nullptr)
  {
    Assert(r->isEq());
    SatLiteral l = enode2Literal(r->getRoot());
    return l != s_trueLiteral
           && (l == s_falseLiteral
               || (d_prop.isRelevant(l)
                   && d_prop.getAssignment(l) == SAT_VALUE_FALSE));
  }
  return false;
}

bool SmtContext::propagateAtoms()
{
  Assert(!d_prop.inconsistent());
  for (size_t i = 0; i < d_atomPropagationQueue.size() && !getCancelFlag(); ++i)
  {
    Assert(!d_prop.inconsistent());
    SatLiteral l = d_atomPropagationQueue[i];
    SatVariable v = l.getSatVariable();
    SatValue val = d_prop.getAssignment(v);
    Assert(val != SAT_VALUE_UNKNOWN);
    if (d_prop.getBdata(v).isENode())
    {
      propagateBoolVarENode(v);
    }
    if (d_prop.inconsistent())
    {
      return false;
    }
    BoolVarData& d = d_prop.getBdata(v);
    if (d.isEq())
    {
      TNode n = d_prop.boolVar2Expr(v);
      Assert(n.getKind() == Kind::EQUAL);
      TNode lhs = n[0];
      TNode rhs = n[1];
      if (lhs.getType().isBoolean())
      {
        // no-op: Boolean equality is handled by the gate clauses
      }
      else if (val == SAT_VALUE_TRUE)
      {
        d_egraph.addEq(d_egraph.getENode(lhs), d_egraph.getENode(rhs));
      }
      else
      {
        if (!addDiseq(d_egraph.getENode(lhs), d_egraph.getENode(rhs))
            && !d_prop.inconsistent())
        {
          d_prop.setConflict();
        }
      }
    }
    else if (d.isQuantifier())
    {
      // Note that with relevancy lemmas a quantifier may be asserted to
      // false and marked relevant, which happens when a quantifier is part
      // of a conflict clause that becomes unit.
      Assert(isQuantifier(d_prop.boolVar2Expr(v)));
      if (d_prop.getAssignment(v) == SAT_VALUE_TRUE)
      {
        assignQuantifier(d_prop.boolVar2Expr(v));
      }
      else
      {
        // cvc5's quantifiers engine skolemized it when cvc5 asserted it
        // false; the core takes that lemma when it is relevant
        skolemize(d_prop.boolVar2Expr(v));
      }
    }
    if (d_prop.inconsistent())
    {
      return false;
    }
  }
  d_atomPropagationQueue.clear();
  return true;
}

void SmtContext::propagateBoolVarENode(SatVariable v)
{
  // Propagate the truth value of v to the enode n associated with it: n is
  // merged with the true (false) enode when v is assigned true (false).
  Assert(d_prop.getAssignment(v) != SAT_VALUE_UNKNOWN);
  Assert(d_prop.getBdata(v).isENode());
  SatValue val = d_prop.getAssignment(v);
  Assert(v < d_prop.getNumBoolVars());
  ENode* n = boolVar2ENode(v);

  bool sign = val == SAT_VALUE_FALSE;
  if (n->mergeTf())
  {
    d_egraph.addEq(n, sign ? d_falseENode : d_trueENode);
  }
  ENode* r = n->getRoot();
  if (r == d_trueENode || r == d_falseENode)
  {
    return;
  }
  // Move the truth value to the other members of the equivalence class if
  // n is the root, or the variable of the root is unassigned.
  if (n == r
      || !d_prop.isRelevant(r->getExpr())  // needed to fix a propagation bug
      || d_prop.getAssignment(enode2BoolVar(r)) != val)
  {
    ENode* first = n;
    n = n->getNext();
    while (n != first)
    {
      SatVariable v2 = enode2BoolVar(n);
      if (d_prop.getAssignment(v2) != val)
      {
        d_prop.assign(SatLiteral(v2, sign));
      }
      n = n->getNext();
    }
  }
}

void SmtContext::notifyRelevant(TNode n)
{
  if (!isApp(n))
  {
    return;
  }
  if (d_egraph.eInternalized(n))
  {
    d_qmanager.notifyRelevant(d_egraph.getENode(n));
  }
}

bool SmtContext::hasPendingTheoryWork() const
{
  return !d_atomPropagationQueue.empty() || d_qmanager.canPropagate()
         || d_egraph.hasPendingEqs();
}

bool SmtContext::theoryPropagate()
{
  if (!propagateAtoms())
  {
    return false;
  }
  if (!d_egraph.propagateEqs())
  {
    return false;
  }
  if (!getCancelFlag())
  {
    d_qmanager.propagate();
  }
  if (d_prop.inconsistent())
  {
    return false;
  }
  return true;
}

bool SmtContext::canPropagate() const
{
  return d_prop.hasPendingPropagation() || hasPendingTheoryWork();
}

bool SmtContext::propagate()
{
  while (true)
  {
    if (d_prop.inconsistent())
    {
      return false;
    }
    size_t qhead = d_prop.getQhead();
    if (!d_prop.bcp())
    {
      return false;
    }
    Assert(!d_prop.inconsistent());
    d_prop.propagateRelevancy(qhead);
    if (d_prop.inconsistent())
    {
      return false;
    }
    if (!theoryPropagate())
    {
      return false;
    }
    if (resourceLimitsExceeded())
    {
      d_prop.setQhead(qhead);
      return true;
    }
    if (!canPropagate())
    {
      return true;
    }
  }
}

bool SmtContext::getCancelFlag()
{
  if (!resourceManager()->out())
  {
    return false;
  }
  d_resourceOut = true;
  return true;
}

bool SmtContext::resourceLimitsExceeded()
{
  if (d_searching && d_resourceOut)
  {
    return true;
  }
  return getCancelFlag();
}

void SmtContext::pushScope()
{
  d_prop.pushScope();
  d_unitsToReassertLims.push_back(d_unitsToReassert.size());
  d_trailStack.pushScope();
}

void SmtContext::popScope(size_t numScopes)
{
  Assert(numScopes > 0);
  Assert(numScopes <= getScopeLevel());
  uint32_t newLvl = getScopeLevel() - static_cast<uint32_t>(numScopes);
  // The order is that of Z3's pop_scope_core, except that the theory side's
  // state other than the trail is popped in one step, before the Boolean
  // side's clauses and assignment, which are independent of it.
  cacheUnitGenerations(newLvl);
  size_t unitsToReassertLim = d_unitsToReassertLims[newLvl];
  d_qmanager.notifyPop();
  d_prop.popScope(numScopes);
  d_trailStack.popScope(numScopes);
  d_egraph.clearPendingEqs();
  d_atomPropagationQueue.clear();
  d_unitsToReassertLims.resize(newLvl);
  reassertUnits(unitsToReassertLim);
  resetCacheGeneration();
}

void SmtContext::popToBaseLvl()
{
  if (getScopeLevel() > 0)
  {
    popScope(getScopeLevel());
  }
}

void SmtContext::cacheUnitGenerations(uint32_t newScopeLvl)
{
  // When a unit is reasserted its enodes and literals may have to be
  // recreated. The generation number of a recreated enode must be the one it
  // had before, otherwise it would reset to 0 and defeat the matching-loop
  // heuristics that control quantifier instantiation.
  for (size_t i = d_unitsToReassertLims[newScopeLvl],
              sz = d_unitsToReassert.size();
       i < sz;
       ++i)
  {
    cacheGeneration(d_unitsToReassert[i].d_unit, newScopeLvl);
  }
}

void SmtContext::reassertUnits(size_t unitsToReassertLim)
{
  for (size_t i = unitsToReassertLim, sz = d_unitsToReassert.size(); i < sz;
       ++i)
  {
    ReplayUnit& ru = d_unitsToReassert[i];
    internalize(ru.d_unit, true);
    SatVariable v = d_prop.getBoolVar(ru.d_unit);
    Assert(v != prop::undefSatVariable)
        << "unit without a variable: " << ru.d_unit;
    SatLiteral l(v, ru.d_sign);
    d_prop.assign(l);
    if (ru.d_relevant)
    {
      d_prop.markAsRelevant(l);
    }
  }
  if (getScopeLevel() == 0)
  {
    d_unitsToReassert.clear();
  }
}

void SmtContext::assignQuantifier(TNode q) { d_qmanager.notifyAssigned(q); }

void SmtContext::notifyBoolVarDeleted(TNode n)
{
  if (isQuantifier(n))
  {
    d_qmanager.del(n);
  }
}

void SmtContext::cacheGeneration(TNode n, uint32_t newScopeLvl)
{
  std::vector<Node> todo;
  todo.push_back(n);
  while (!todo.empty())
  {
    Node curr = todo.back();
    todo.pop_back();
    if (d_cacheGenerationVisited.count(curr) != 0)
    {
      continue;
    }
    d_cacheGenerationVisited.insert(curr);
    if (isApp(curr))
    {
      if (d_egraph.eInternalized(curr))
      {
        ENode* e = d_egraph.getENode(curr);
        uint32_t ilvl = e->getIscopeLvl();
        if (ilvl <= newScopeLvl)
        {
          // neither the node nor its children will be recreated
          continue;
        }
        d_cachedGeneration[curr] = d_egraph.getGeneration(e);
      }
      for (const Node& arg : curr)
      {
        if (isApp(arg) || isQuantifier(arg))
        {
          todo.push_back(arg);
        }
      }
    }
    else if (isQuantifier(curr) && d_prop.bInternalized(curr))
    {
      d_cachedGeneration[curr] = d_qmanager.getGeneration(curr);
      todo.push_back(curr[1]);
    }
  }
}

void SmtContext::resetCacheGeneration()
{
  d_cacheGenerationVisited.clear();
  d_cachedGeneration.clear();
}

void SmtContext::internalizeInstance(TNode q,
                                     const std::vector<Node>& terms,
                                     uint32_t generation)
{
  if (d_prop.inconsistent())
  {
    return;
  }
  std::vector<Node> key{q};
  key.insert(key.end(), terms.begin(), terms.end());
  auto it = d_instanceForms.emplace(
      q.getNodeManager()->mkNode(Kind::SEXPR, key), Node());
  std::vector<Node> defs;
  if (it.second)
  {
    it.first->second = d_host.mkInstance(q, terms, defs);
  }
  internalizePreprocessed(it.first->second, defs, generation, true);
}

void SmtContext::internalizePreprocessed(TNode norm,
                                         const std::vector<Node>& defs,
                                         uint32_t generation,
                                         bool instance)
{
  // A skolem definition holds globally, and cvc5's preprocessing gives it
  // only once, so it is a root that is asserted again after each backtrack,
  // as a delayed unit is, until it is asserted at the base level.
  for (const Node& d : defs)
  {
    d_host.sendLemma(d, false);
    if (d.isConst())
    {
      continue;
    }
    internalizeAssertion(d, generation);
    // a unit is reasserted as an atom and a sign
    bool neg = d.getKind() == Kind::NOT;
    d_unitsToReassert.push_back(ReplayUnit{neg ? d[0] : d, neg, true});
  }
  if (norm.isConst() && norm.getConst<bool>())
  {
    return;
  }
  // the formula is also a lemma for cvc5's prop engine: an instance, which
  // holds where it was made, or a lemma that holds globally
  // An instance is local to the SAT context (--z3-host-local-instances, the
  // default), as with cvc5's --inst-local: cvc5 adds its clause once, but its
  // decision heuristic treats it as an assertion only in the context where
  // it was last made. The core makes it again when matching finds it again
  // after backtracking, as Z3 does, and it is then sent again, which makes it
  // an assertion there again. Otherwise an instance is sent once.
  d_host.sendLemma(norm, instance && options().z3.z3HostLocalInstances);
  internalizeAssertion(norm, generation);
}

void SmtContext::skolemize(TNode q)
{
  if (q.getKind() != Kind::FORALL)
  {
    return;
  }
  if (d_prop.inconsistent())
  {
    return;
  }
  // The core internalizes the lemma, as it does an instance, so that its
  // witnesses are relevant as the core's own formulas make them: through q,
  // which is relevant here. It also sends it, although cvc5's quantifiers
  // engine did, since cvc5's decisions then treat it as the core's lemma.
  std::vector<Node> defs;
  Node norm = d_host.mkSkolemization(q, defs);
  d_stats.d_numSkolemizations++;
  internalizePreprocessed(norm, defs, generationOf(q), false);
}

void SmtContext::initSearch() { d_qmanager.initSearch(); }

bool SmtContext::finalCheck()
{
  d_stats.d_numFinalChecks++;
  Trace("z3-events") << "FINALCHECK " << d_stats.d_numFinalChecks.get()
                     << std::endl;

  return d_qmanager.finalCheck() && !canPropagate();
}

// ------------------------------------------------------------ internalization
//
// Turning formulas into the core's Boolean variables, clauses and enodes.
//
// Note this is not a Tseitin CNF conversion in the usual sense: the Boolean
// structure is internalized gate by gate, together with the relevancy watches
// that decide which arguments of each gate the current assignment has to
// justify. That coupling is why the core does its own internalization rather
// than reusing cvc5's CnfStream.

namespace {

bool isTrueNode(TNode n)
{
  return n.getKind() == Kind::CONST_BOOLEAN && n.getConst<bool>();
}

bool isFalseNode(TNode n)
{
  return n.getKind() == Kind::CONST_BOOLEAN && !n.getConst<bool>();
}

/** True if n is an atom or the negation of one, as Z3's is_literal is. */
bool isLiteralNode(TNode n)
{
  TNode a = n.getKind() == Kind::NOT ? n[0] : n;
  return !isApp(a) || a.getNumChildren() == 0;
}

}  // namespace

void SmtContext::updateGeneration(ENode* e)
{
  // Patterns with equalities are not supported, so there is no need to track
  // the generation of equality nodes.
  if (e->isEq())
  {
    return;
  }

  if (0 < d_generation && d_generation < d_egraph.getGeneration(e))
  {
    if (e->usesCgTable())
    {
      d_egraph.setGenerationSticky(e, d_generation);
    }
    else
    {
      d_egraph.setGeneration(e, d_generation);
    }
  }
}

void SmtContext::internalizeAssertion(TNode n, uint32_t generation)
{
  uint32_t oldGeneration = d_generation;
  d_generation = generation;
  d_stats.d_maxGeneration.maxAssign(generation);
  Assert(n.getType().isBoolean());
  assertRoot(n);
  d_generation = oldGeneration;
}

void SmtContext::internalize(TNode n, bool gateCtx, uint32_t generation)
{
  uint32_t oldGeneration = d_generation;
  d_generation = generation;
  d_stats.d_maxGeneration.maxAssign(generation);
  internalizeRec(n, gateCtx);
  d_generation = oldGeneration;
}

void SmtContext::internalize(TNode n, bool gateCtx)
{
  internalizeRec(n, gateCtx);
}

void SmtContext::internalizeRec(TNode n, bool gateCtx)
{
  if (isVar(n))
  {
    Unreachable() << "z3: formulas should not contain unbound variables";
  }
  if (n.getType().isBoolean())
  {
    Assert(isQuantifier(n) || isApp(n));
    internalizeFormula(n, gateCtx);
  }
  else
  {
    Assert(isApp(n));
    internalizeTerm(n);
  }
}

void SmtContext::internalizeFormula(TNode n, bool gateCtx)
{
  Assert(n.getType().isBoolean());
  if (isTrueNode(n) || isFalseNode(n))
  {
    return;
  }

  if (n.getKind() == Kind::NOT && gateCtx)
  {
    // A Boolean variable is not needed for a NOT gate inside a gate context.
    internalizeRec(n[0], true);
    return;
  }

  if (d_prop.bInternalized(n))
  {
    // n was already internalized as a Boolean.
    SatVariable v = d_prop.getBoolVar(n);

    updateGeneration(n);

    // An enode is still necessary if n is not in a gate context and is an
    // application. A quantifier is handled here as well: Z3 relies on its own
    // preprocessing to keep quantifiers out of term positions, which cvc5's
    // does not, so the enode has to be built rather than assumed away.
    if (!gateCtx && isQuantifier(n))
    {
      if (!d_egraph.eInternalized(n))
      {
        mkENode(n,
                true, /* suppress the arguments */
                true, /* merge with true/false, since this is not a gate */
                false /* congruence closure is not enabled */);
        setEnodeFlag(v, false);
        if (d_prop.getAssignment(v) != SAT_VALUE_UNKNOWN)
        {
          propagateBoolVarENode(v);
        }
      }
      return;
    }
    if (!gateCtx && isApp(n))
    {
      if (d_egraph.eInternalized(n))
      {
        ENode* e = d_egraph.getENode(n);
        setMergeTf(e, v, false);
      }
      else
      {
        mkENode(n,
                true, /* suppress the arguments: congruence is not used here */
                true, /* merge with true/false, since this is not a gate */
                false /* congruence closure is not enabled */);
        setEnodeFlag(v, false);
        if (d_prop.getAssignment(v) != SAT_VALUE_UNKNOWN)
        {
          propagateBoolVarENode(v);
        }
      }
      Assert(d_prop.getBdata(v).isENode());
    }
    return;
  }

  if (n.getKind() == Kind::EQUAL && !n[0].getType().isBoolean())
  {
    internalizeEq(n, gateCtx);
  }
  else if (n.getKind() == Kind::DISTINCT)
  {
    internalizeDistinct(n, gateCtx);
  }
  else if (isQuantifier(n))
  {
    internalizeQuantifier(n, gateCtx);
  }
  else
  {
    internalizeFormulaCore(n, gateCtx);
  }
}

void SmtContext::internalizeEq(TNode n, bool gateCtx)
{
  Assert(!d_prop.bInternalized(n));
  Assert(n.getKind() == Kind::EQUAL);
  internalizeFormulaCore(n, gateCtx);
  SatVariable v = d_prop.getBoolVar(n);
  d_prop.getBdata(v).setEqFlag();
}

void SmtContext::internalizeDistinct(TNode n, bool gateCtx)
{
  Assert(!d_prop.bInternalized(n));
  Assert(n.getKind() == Kind::DISTINCT);
  SatVariable v = d_prop.mkBoolVar(n);
  SatLiteral l(v);
  // the pairwise expansion of the distinct
  std::vector<Node> diseqs;
  size_t numArgs = n.getNumChildren();
  for (size_t i = 0; i < numArgs; ++i)
  {
    for (size_t j = i + 1; j < numArgs; ++j)
    {
      diseqs.push_back(nodeManager()->mkNode(
          Kind::NOT, nodeManager()->mkNode(Kind::EQUAL, n[i], n[j])));
    }
  }
  Node def =
      diseqs.size() == 1 ? diseqs[0] : nodeManager()->mkNode(Kind::AND, diseqs);
  internalizeRec(def, true);
  SatLiteral lDef = d_prop.getLiteral(def);
  d_prop.mkGateClause(~l, lDef);
  d_prop.mkGateClause(l, ~lDef);
  // Reference counts of negations are not tracked, so a relevancy dependency
  // on the equality is added instead.
  Node relDef = def.getKind() == Kind::NOT ? def[0] : def;
  d_prop.addRelevancyDependency(n, relDef);
  if (!gateCtx)
  {
    mkENode(n, true, true, false);
    setEnodeFlag(v, true);
    // v may have been assigned by the definition clauses before the enode
    // was created.
    if (d_prop.getAssignment(v) != SAT_VALUE_UNKNOWN)
    {
      propagateBoolVarENode(v);
    }
  }
}

void SmtContext::internalizeQuantifier(TNode q, bool gateCtx)
{
  Assert(!d_prop.bInternalized(q));
  if (q.getKind() != Kind::FORALL)
  {
    // Z3's preprocessing puts every formula in a form where only universal
    // quantifiers survive, so its internalizer has no case for exists.
    d_prop.mkBoolVar(q);
    return;
  }
  SatVariable v = d_prop.mkBoolVar(q);
  if (!gateCtx)
  {
    // Z3 asserts gateCtx here: its rewriter guarantees a quantifier only ever
    // occurs as an argument of a gate. cvc5's preprocessor gives no such
    // guarantee -- a Boolean-sorted argument of an uninterpreted function is
    // enough to break it.
    Trace("z3") << "quantifier in a non-gate context: " << q << std::endl;
    mkENode(q,
            true, /* suppress the arguments */
            true, /* merge with true/false, since this is not a gate */
            false /* congruence closure is not enabled */);
    setEnodeFlag(v, false);
  }
  uint32_t generation = generationOf(q);
  BoolVarData& d = d_prop.getBdata(v);
  d.setQuantifierFlag();
  d_qmanager.add(q, generation);
}

void SmtContext::internalizeFormulaCore(TNode n, bool gateCtx)
{
  // Internalize gates, and the (uninterpreted and equality) predicates.
  Assert(!d_prop.bInternalized(n));
  Assert(!d_egraph.eInternalized(n));

  bool isGateN = expr::isBooleanConnective(n);
  // process the arguments
  for (const Node& arg : n)
  {
    internalizeRec(arg, isGateN);
  }

  bool isNewVar = false;
  SatVariable v;
  // n may already be internalized once its children are, for example the
  // equality in (= (ite c 1 0) 1): internalizing the ite term forces both
  // (= (ite c 1 0) 1) and (= (ite c 1 0) 0).
  if (!d_prop.bInternalized(n))
  {
    isNewVar = true;
    v = d_prop.mkBoolVar(n);
  }
  else
  {
    v = d_prop.getBoolVar(n);
  }

  // A formula needs an enode when it is not in a gate context, or when it has
  // arguments and is not a gate (i.e. an uninterpreted predicate or an
  // equality).
  if (!d_egraph.eInternalized(n)
      && (!gateCtx || (!isGateN && n.getNumChildren() > 0)))
  {
    bool suppressArgs = isGateN || n.getKind() == Kind::NOT;
    bool mergeTf = !gateCtx;
    mkENode(n, suppressArgs, mergeTf, true);
    setEnodeFlag(v, isNewVar);
    Assert(d_prop.getBdata(v).isENode());
  }
  else if (!gateCtx && d_egraph.eInternalized(n))
  {
    // n was internalized in a gate context while its children were being
    // internalized (ite-term axioms, for example), but it now occurs outside
    // a gate and must be merged with true/false.
    setMergeTf(d_egraph.getENode(n), v, isNewVar);
  }

  // The constraints of n must be asserted after its Boolean variable and
  // enode exist. Otherwise completeness is lost: an assigned Boolean variable
  // only enters the atom propagation queue when isAtom() holds, and creating
  // the constraints may force v to be assigned.
  if (!isNewVar)
  {
    return;
  }
  Assert(n.getKind() != Kind::NOT || !gateCtx);
  d_prop.mkGateConstraints(n);
}

namespace {

/** Clears the merge-with-true/false flag of an enode. */
class SetMergeTfTrail : public Trail
{
 public:
  SetMergeTfTrail(ENode* n) : d_node(n) {}
  void undo() override { d_node->resetMergeTf(); }

 private:
  ENode* d_node;
};

/** Clears the has-enode flag of a Boolean variable. */
class SetENodeFlagTrail : public Trail
{
 public:
  SetENodeFlagTrail(SmtContext& ctx, SatVariable v) : d_ctx(ctx), d_var(v) {}
  void undo() override { d_ctx.getPropCore().getBdata(d_var).resetENodeFlag(); }

 private:
  SmtContext& d_ctx;
  SatVariable d_var;
};

}  // namespace

void SmtContext::setMergeTf(ENode* n, SatVariable v, bool isNewVar)
{
  // With the merge-tf flag set, n is merged with the true (false) enode
  // whenever v is assigned true (false).
  Assert(boolVar2ENode(v) == n);
  if (n->d_mergeTf)
  {
    return;
  }
  if (!isNewVar)
  {
    d_trailStack.push(SetMergeTfTrail(n));
  }
  n->d_mergeTf = true;
  switch (d_prop.getAssignment(v))
  {
    case SAT_VALUE_UNKNOWN: break;
    case SAT_VALUE_TRUE:
      if (n->getRoot() != d_trueENode->getRoot())
      {
        d_egraph.pushEq(n, d_trueENode);
      }
      break;
    case SAT_VALUE_FALSE:
      if (n->getRoot() != d_falseENode->getRoot())
      {
        d_egraph.pushEq(n, d_falseENode);
      }
      break;
  }
}

void SmtContext::setEnodeFlag(SatVariable v, bool isNewVar)
{
  Assert(d_egraph.eInternalized(d_prop.boolVar2Expr(v)));
  BoolVarData& data = d_prop.getBdata(v);
  if (!data.isENode())
  {
    if (!isNewVar)
    {
      d_trailStack.push(SetENodeFlagTrail(*this, v));
    }
    data.setENodeFlag();
  }
}

void SmtContext::internalizeTerm(TNode n)
{
  if (d_egraph.eInternalized(n))
  {
    updateGeneration(d_egraph.getENode(n));
    return;
  }
  // A term if-then-else does not occur here: the formulas the core
  // internalizes are in the form cvc5's theories take, without them.
  internalizeUninterpreted(n);
  Assert(d_egraph.eInternalized(n));
}

void SmtContext::internalizeUninterpreted(TNode n)
{
  Assert(!d_egraph.eInternalized(n));
  // process the arguments
  for (const Node& arg : n)
  {
    internalizeRec(arg, false);
    Assert(d_egraph.eInternalized(arg));
  }
  if (d_egraph.eInternalized(n))
  {
    return;
  }

  // The arithmetic terms keep the congruence policy of Z3's arithmetic
  // plugin, which never enables congruence closure for (+ ...) and (* ...)
  // (theory_arith::enable_cgc_for).
  Kind k = n.getKind();
  bool cgc = k != Kind::ADD && k != Kind::MULT && k != Kind::NONLINEAR_MULT;
  mkENode(n,
          false, /* do not suppress the arguments */
          false, /* a term, so it is not merged with true/false */
          cgc);
}

uint32_t SmtContext::generationOf(TNode n)
{
  auto itg = d_cachedGeneration.find(n);
  if (itg != d_cachedGeneration.end())
  {
    return itg->second;
  }
  // the first internalization records the generation for later ones
  auto ith = d_hostGeneration.emplace(n, d_generation).first;
  return ith->second;
}

ENode* SmtContext::mkENode(TNode n,
                           bool suppressArgs,
                           bool mergeTf,
                           bool cgcEnabled)
{
  ENode* e = d_egraph.mkENode(
      n, generationOf(n), suppressArgs, mergeTf, cgcEnabled, getScopeLevel());
  if (e->getNumArgs() > 0 && e->isTrueEq())
  {
    // the equality holds already
    d_prop.assign(SatLiteral(enode2BoolVar(e)));
    d_egraph.pushEq(e, d_trueENode);
  }
  return e;
}

void SmtContext::assertFormula(TNode e)
{
  if (getCancelFlag())
  {
    return;
  }
  if (!d_searching)
  {
    popToBaseLvl();
  }
  pushAssertion(e);
}

void SmtContext::pushAssertion(TNode e)
{
  // Z3 splits a conjunction, and a negated disjunction, into separate
  // assertions while they are being collected (see
  // asserted_formulas::push_assertion). This matters beyond saving a Boolean
  // variable: an assertion is marked relevant when it is asserted, while the
  // conjuncts of a top-level conjunction never are -- the and-gate only
  // propagates relevancy to its arguments once the conjunction itself is
  // assigned, which never happens for a root. cvc5's preprocessor leaves
  // such conjunctions in place, so the split is done here.
  if (isTrueNode(e))
  {
    return;
  }
  if (isFalseNode(e))
  {
    d_prop.setAssertedInconsistent();
    d_assertedFormulas.push_back(e);
    return;
  }
  if (e.getKind() == Kind::AND)
  {
    for (const Node& arg : e)
    {
      pushAssertion(arg);
    }
    return;
  }
  if (e.getKind() == Kind::NOT && e[0].getKind() == Kind::OR)
  {
    for (const Node& arg : e[0])
    {
      pushAssertion(arg.negate());
    }
    return;
  }
  // What Z3 does next is asserted_formulas::flatten_clauses, whose point is
  // that its core gets flat clauses rather than a tree of gates: every nested
  // gate costs a Boolean variable, two clauses and a link in the chain
  // relevancy has to walk before it reaches the atoms. A top-level
  // if-then-else is two clauses, and a top-level disjunction over a
  // conjunction distributes.
  if (e.getKind() == Kind::ITE)
  {
    pushAssertion(nodeManager()->mkNode(Kind::OR, e[0].negate(), e[1]));
    pushAssertion(nodeManager()->mkNode(Kind::OR, Node(e[0]), e[2]));
    return;
  }
  if (e.getKind() == Kind::OR && e.getNumChildren() == 2)
  {
    for (size_t i = 0; i < 2; ++i)
    {
      TNode conj = e[i];
      TNode rest = e[1 - i];
      // Z3 also distributes over a shared conjunction when the other side is
      // not a literal, using a reference count to tell that the conjunction
      // occurs nowhere else. There is no equally cheap test here, so only the
      // case that cannot grow the formula is taken: duplicating a literal
      // across the conjuncts costs one literal per conjunct.
      if (conj.getKind() == Kind::AND && isLiteralNode(rest))
      {
        for (const Node& arg : conj)
        {
          pushAssertion(nodeManager()->mkNode(Kind::OR, Node(rest), arg));
        }
        return;
      }
    }
  }
  if (!d_hasQuantifiers && expr::hasClosure(Node(e)))
  {
    d_hasQuantifiers = true;
  }
  Trace("z3-assert") << "ASSERT " << e << std::endl;
  d_assertedFormulas.push_back(e);
}

void SmtContext::internalizeAssertions()
{
  if (getCancelFlag() || d_internalizingAssertions)
  {
    return;
  }
  d_internalizingAssertions = true;
  if (d_prop.isAssertedInconsistent())
  {
    d_prop.setConflict();
    d_internalizingAssertions = false;
    return;
  }
  while (d_assertedFormulasQhead < d_assertedFormulas.size())
  {
    if (getCancelFlag())
    {
      d_internalizingAssertions = false;
      return;
    }
    TNode f = d_assertedFormulas[d_assertedFormulasQhead];
    ++d_assertedFormulasQhead;
    internalizeAssertion(f, 0);
  }
  d_internalizingAssertions = false;
}

void SmtContext::assertRoot(TNode n)
{
  if (expr::isBooleanConnective(n) && n.getKind() != Kind::NOT)
  {
    switch (n.getKind())
    {
      case Kind::AND:
      {
        for (const Node& arg : n)
        {
          internalizeRec(arg, true);
          SatLiteral lit = d_prop.getLiteral(arg);
          d_prop.mkRootClause(1, &lit);
        }
        break;
      }
      case Kind::OR:
      {
        std::vector<SatLiteral> lits;
        for (const Node& arg : n)
        {
          internalizeRec(arg, true);
          lits.push_back(d_prop.getLiteral(arg));
        }
        d_prop.mkRootClause(lits.size(), lits.data());
        d_prop.addOrRelWatches(n);
        break;
      }
      case Kind::IMPLIES:
      {
        internalizeRec(n[0], true);
        internalizeRec(n[1], true);
        d_prop.mkRootClause(~d_prop.getLiteral(n[0]), d_prop.getLiteral(n[1]));
        d_prop.addImpliesRelWatches(n);
        break;
      }
      case Kind::EQUAL:
      case Kind::XOR:
      {
        TNode lhs = n[0];
        TNode rhs = n[1];
        internalizeRec(lhs, true);
        internalizeRec(rhs, true);
        SatLiteral l1 = d_prop.getLiteral(lhs);
        SatLiteral l2 = d_prop.getLiteral(rhs);
        if (n.getKind() == Kind::XOR)
        {
          l2 = ~l2;
        }
        d_prop.mkRootClause(l1, ~l2);
        d_prop.mkRootClause(~l1, l2);
        break;
      }
      case Kind::ITE:
      {
        TNode c = n[0];
        TNode t = n[1];
        TNode e = n[2];
        internalizeRec(c, true);
        internalizeRec(t, true);
        internalizeRec(e, true);
        SatLiteral cl = d_prop.getLiteral(c);
        SatLiteral tl = d_prop.getLiteral(t);
        SatLiteral el = d_prop.getLiteral(e);
        d_prop.mkRootClause(~cl, tl);
        d_prop.mkRootClause(cl, el);
        d_prop.addIteRelWatches(n);
        break;
      }
      default: Unreachable();
    }
    d_prop.markAsRelevant(n);
  }
  else if (n.getKind() == Kind::DISTINCT)
  {
    // Z3 encodes a very large distinct with auxiliary values over a fresh
    // sort. cvc5's rewriter expands distinct during preprocessing, so the
    // core is not expected to meet one at all; the plain encoding is used.
    assertDefault(n);
    d_prop.markAsRelevant(n);
  }
  else
  {
    assertDefault(n);
  }
}

void SmtContext::assertDefault(TNode n)
{
  internalize(n, true);
  SatLiteral l = d_prop.getLiteral(n);
  if (l == s_falseLiteral)
  {
    d_prop.setConflict();
  }
  else if (l == s_trueLiteral)
  {
    return;
  }
  else
  {
    d_prop.assign(l);
    d_prop.markAsRelevant(l);
  }
}

void SmtContext::setupSearch()
{
  d_stats.d_numAssertedFormulas =
      static_cast<int64_t>(d_assertedFormulas.size());
  popToBaseLvl();
  internalizeAssertions();
  initSearch();
  d_resourceOut = false;
  d_searching = true;
}

void SmtContext::setScopeLevel(uint32_t lvl)
{
  while (getScopeLevel() < lvl)
  {
    pushScope();
  }
  if (getScopeLevel() > lvl)
  {
    popScope(getScopeLevel() - lvl);
  }
}

SatLiteral SmtContext::literalOf(TNode n)
{
  bool neg = n.getKind() == Kind::NOT;
  TNode atom = neg ? n[0] : n;
  if (!d_prop.bInternalized(atom))
  {
    internalize(atom, true);
  }
  SatLiteral l = d_prop.getLiteral(atom);
  return neg ? ~l : l;
}

}  // namespace z3
}  // namespace cvc5::internal

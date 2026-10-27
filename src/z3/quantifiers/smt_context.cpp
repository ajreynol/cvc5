/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The logical context: the ported Z3 SMT core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), files
 * src/smt/smt_context.cpp and src/smt/smt_internalizer.cpp, and recast in
 * cvc5 style.
 */

#include "z3/quantifiers/smt_context.h"

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <fstream>

#include "base/output.h"
#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "options/smt_options.h"
#include "options/z3_options.h"
#include "printer/printer.h"
#include "prop/prop_engine.h"
#include "smt/env.h"
#include "smt/print_benchmark.h"
#include "smt/set_defaults.h"
#include "smt/solver_engine.h"
#include "theory/decision_manager.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/skolemize.h"
#include "theory/skolem_lemma.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "util/resource_manager.h"
#include "z3/quantifiers/lemma_proof_generator.h"
#include "z3/quantifiers/quantifier_manager.h"
#include "z3/relevancy/prop_core.h"
#include "z3/relevancy/relevancy_tracker.h"

namespace cvc5::internal {
namespace z3 {

SmtContext::SmtContext(Env& env,
                       theory::quantifiers::QuantifiersInferenceManager& qim,
                       TheoryEngine* te)
    : EnvObj(env),
      d_stats(statisticsRegistry()),
      d_te(te),
      d_qim(qim),
      d_setup(false),
      d_inConflict(false),
      d_conflictLevel(0),
      d_needCheck(false),
      d_popLevel(UINT32_MAX),
      d_pg(std::make_unique<LemmaProofGenerator>(env)),
      d_splitStrategy(std::make_unique<SplitStrategy>(env, d_te)),
      d_popNotify(std::make_unique<PopNotify>(context(), *this)),
      d_masterEe(nullptr),
      d_masterTerm(context()),
      d_masterIdx(context(), 0),
      d_tracker(std::make_unique<RelevancyTracker>(env, te, *this)),
      d_prop(env, *this, d_stats),
      d_normalizer(env.getNodeManager()),
      d_qmanager(*this),
      d_trueENode(nullptr),
      d_falseENode(nullptr),
      d_generation(0),
      d_mkENodeTrail(*this)
{
  te->addModule(d_tracker.get());
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

uint32_t SmtContext::getDeclId(TNode decl)
{
  Assert(!decl.isNull());
  auto it = d_declIds.find(decl);
  if (it != d_declIds.end())
  {
    return it->second;
  }
  uint32_t id = static_cast<uint32_t>(d_declIds.size());
  d_declIds[decl] = id;
  return id;
}

uint32_t SmtContext::getDeclIdOption(TNode decl) const
{
  if (decl.isNull())
  {
    return UINT32_MAX;
  }
  auto it = d_declIds.find(decl);
  return it == d_declIds.end() ? UINT32_MAX : it->second;
}

namespace {

/** Undoes an addEq. */
class AddEqTrail : public Trail
{
 public:
  AddEqTrail(SmtContext& ctx, ENode* r1, size_t r2NumParents)
      : d_ctx(ctx), d_r1(r1), d_r2NumParents(r2NumParents)
  {
  }
  void undo() override;

 private:
  SmtContext& d_ctx;
  ENode* d_r1;
  size_t d_r2NumParents;
};

}  // namespace

void SmtContext::addEq(ENode* n1, ENode* n2)
{
  Assert(n1->getSort() == n2->getSort());

  d_stats.d_numAddEq++;
  ENode* r1 = n1->getRoot();
  ENode* r2 = n2->getRoot();

  if (r1 == r2)
  {
    // a redundant constraint
    return;
  }

  if (r1->isInterpreted() && r2->isInterpreted())
  {
    // two distinct values were found equal
    setConflict();
    return;
  }

  // Swap r1 and r2 if the class of r1 is bigger than the class of r2, or if
  // r1 is interpreted but r2 is not. The second condition maintains the
  // invariant that if a class contains an interpreted enode then its root is
  // interpreted too.
  if ((r1->getClassSize() > r2->getClassSize() && !r2->isInterpreted())
      || r1->isInterpreted())
  {
    Assert(!r2->isInterpreted());
    std::swap(n1, n2);
    std::swap(r1, r2);
  }

  // Relevancy must be propagated to the rest of the equivalence class, to
  // maintain the invariant on the parent lists of enodes.
  if (isRelevant(r1))
  {
    markAsRelevant(r2);
  }
  else if (isRelevant(r2))
  {
    markAsRelevant(r1);
  }

  size_t r2NumParents = r2->getNumParents();

  d_qmanager.notifyMerge(r1, r2);

  removeParentsFromCgTable(r1);

  ENode* curr = r1;
  do
  {
    curr->d_root = r2;
    curr = curr->d_next;
  } while (curr != r1);

  Assert(r1->getRoot() == r2);
  reinsertParentsIntoCgTable(r1, r2);

  // The AddEqTrail is pushed after reinsertParentsIntoCgTable, because the
  // latter may push merge-generation trails and addEq must be undone before
  // those are.
  pushTrail(AddEqTrail(*this, r1, r2NumParents));

  if (n2->isBool())
  {
    propagateBoolENodeAssignment(r1, r2, n1, n2);
  }

  // merge the equivalence classes
  std::swap(r1->d_next, r2->d_next);

  // update the class size
  r2->d_classSize += r1->d_classSize;
}

namespace {

void AddEqTrail::undo() { d_ctx.undoAddEq(d_r1, d_r2NumParents); }

}  // namespace

void SmtContext::removeParentsFromCgTable(ENode* r1)
{
  // When two equivalence classes merge, the parents of the smaller one that
  // are congruence roots must leave the congruence table, since their hash
  // codes are about to change.
  Assert(d_r1ParentGenerations.empty());

  for (ENode* parent : r1->getParents())
  {
    if (!parent->isMarked() && parent->isCgr() && !parent->isTrueEq())
    {
      Assert(!parent->isCgcEnabled() || d_cgTable.containsPtr(parent));
      parent->setMark();
      if (parent->isCgcEnabled())
      {
        if (!parent->isEq())
        {
          // generations of equalities are not tracked
          d_r1ParentGenerations.emplace_back(parent, getGeneration(parent));
        }
        d_cgTable.erase(parent);
        Assert(!d_cgTable.containsPtr(parent));
      }
    }
  }
}

void SmtContext::setGenerationSticky(ENode* n, uint32_t generation)
{
  Assert(n->usesCgTable());
  Assert(!n->isEq());
  // The caller is responsible for this; sticky updates are too expensive to
  // spend on no-ops.
  Assert(generation < getGeneration(n));

  setGeneration(n, generation);
  d_stickyGenerationUpdates[n] = generation;
}

void SmtContext::reinsertParentsIntoCgTable(ENode* r1, ENode* r2)
{
  // Reinsert the parents of r1 that removeParentsFromCgTable took out. Some
  // of them become congruent to other enodes, which propagates a new
  // equality. The ones that remain congruence roots move to r2's parent list.
  ENodeVector& r2Parents = r2->d_parents;
  ENodeVector& r1Parents = r1->d_parents;
  size_t numR1Parents = r1Parents.size();
  size_t generationCacheIdx = 0;
  for (size_t i = 0; i < numR1Parents; ++i)
  {
    ENode* parent = r1Parents[i];
    if (!parent->isMarked())
    {
      continue;
    }
    parent->unsetMark();
    if (parent->isEq())
    {
      Assert(parent->getNumArgs() == 2);
      ENode* lhs = parent->getArg(0);
      ENode* rhs = parent->getArg(1);
      if (lhs->getRoot() == rhs->getRoot())
      {
        Assert(parent->isTrueEq());
        size_t exprId = parent->getOwnerId();
        BoolVar v = getBoolVarOfId(exprId);
        SatValue val = getAssignment(v);
        if (val != SAT_VALUE_TRUE)
        {
          assign(Literal(v));
        }
        // There is no need to reinsert the equality into the congruence
        // table: the congruence propagations it could lead to are already
        // handled by the assign above.
        continue;
      }
    }
    if (parent->isCgcEnabled())
    {
      // look up the generation cache
      uint32_t parentGeneration = 0;  // equalities just use generation 0
      if (!parent->isEq())
      {
        if (generationCacheIdx < d_r1ParentGenerations.size())
        {
          std::pair<ENode*, uint32_t>& pg =
              d_r1ParentGenerations[generationCacheIdx++];
          Assert(pg.first == parent);
          parentGeneration = pg.second;
        }
        else
        {
          parentGeneration = getGeneration(parent);
        }
      }

      ENode* parentPrime = d_cgTable.insert(parent);
      if (parentPrime == parent)
      {
        Assert(parent->isCgr());
        Assert(d_cgTable.containsPtr(parent));
        parent->d_generation = parentGeneration;
        r2Parents.push_back(parent);
        continue;
      }

      parent->d_cg = parentPrime;
      mergeCgcGenerations(parent, parentGeneration, parentPrime);

      if (parentPrime->d_root != parent->d_root)
      {
        pushNewCongruence(parent, parentPrime);
      }
    }
    else
    {
      // congruence closure is disabled for parent, so just copy it over
      r2Parents.push_back(parent);
    }
  }
  d_r1ParentGenerations.clear();
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
      BoolVar v = enode2BoolVar(curr);
      Literal l(v, sign);
      if (getAssignment(l) != SAT_VALUE_TRUE)
      {
        assign(l);
      }
      curr = curr->d_next;
    } while (curr != r1);
  }
  else
  {
    BoolVar v1 = enode2BoolVar(n1);
    BoolVar v2 = enode2BoolVar(n2);
    SatValue val1 = getAssignment(v1);
    SatValue val2 = getAssignment(v2);
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
  BoolVar vSource = enode2BoolVar(source);
  SatValue val = getAssignment(vSource);
  Assert(val != SAT_VALUE_UNKNOWN);
  bool sign = val == SAT_VALUE_FALSE;
  ENode* first = target;
  do
  {
    BoolVar v2 = enode2BoolVar(target);
    SatValue val2 = getAssignment(v2);
    if (val2 != val)
    {
      assign(Literal(v2, sign));
    }
    target = target->getNext();
  } while (first != target);
}

void SmtContext::undoAddEq(ENode* r1, size_t r2NumParents)
{
  ENode* r2 = r1->getRoot();

  // restore r2's class size
  r2->d_classSize -= r1->d_classSize;

  // unmerge the equivalence classes
  std::swap(r1->d_next, r2->d_next);

  Assert(d_r1ParentGenerations.empty());

  // remove the parents of r1 that remained congruence roots
  ENodeVector::iterator it = r2->beginParents();
  ENodeVector::iterator end = r2->endParents();
  it += r2NumParents;
  for (; it != end; ++it)
  {
    ENode* parent = *it;
    if (parent->isCgcEnabled())
    {
      Assert(parent->isCgr())
          << "parent " << parent->getExpr() << " of " << r1->getExpr()
          << " merged into " << r2->getExpr() << " is not a congruence root";
      Assert(d_cgTable.containsPtr(parent));
      if (!parent->isEq())
      {
        d_r1ParentGenerations.emplace_back(parent, getGeneration(parent));
      }
      d_cgTable.erase(parent);
    }
  }

  ENode* curr = r1;
  do
  {
    curr->d_root = r1;
    curr = curr->d_next;
  } while (curr != r1);

  // restore the parents of r2
  r2->d_parents.resize(r2NumParents);

  size_t generationCacheIdx = 0;

  // try to reinsert the parents of r1 that are not congruence roots
  for (ENode* parent : r1->getParents())
  {
    if (!parent->isCgcEnabled())
    {
      continue;
    }
    ENode* cg = parent->d_cg;
    if (parent->isTrueEq()
        || !(parent == cg                 // root of its class before and after
             || !congruent(parent, cg)))  // root before but not after
    {
      continue;
    }

    uint32_t gen;
    if (parent->isEq())
    {
      gen = 0;
    }
    else if (parent == cg)
    {
      ENode* p = nullptr;
      uint32_t parentGeneration = 0;
      if (generationCacheIdx < d_r1ParentGenerations.size())
      {
        p = d_r1ParentGenerations[generationCacheIdx].first;
        parentGeneration = d_r1ParentGenerations[generationCacheIdx].second;
      }
      if (p == parent)
      {
        generationCacheIdx++;
        gen = parentGeneration;
      }
      else
      {
        Assert(d_cgTable.containsPtr(parent));
        continue;
      }
    }
    else
    {
      // Insert at a dummy generation; an undoMergeCgcGenerations immediately
      // follows and sets the real one. Deliberately not UINT32_MAX, so that
      // an overflow here would not be invisible.
      gen = 100000;
    }

    parent->d_cg = d_cgTable.insert(parent);
    if (parent->d_cg == parent)
    {
      // parent is a congruence root again: restore its generation
      parent->d_generation = gen;
    }
  }

  d_r1ParentGenerations.clear();
}

void SmtContext::undoMergeCgcGenerations(ENode* e1,
                                         uint32_t e1Generation,
                                         ENode* e2,
                                         uint32_t e2Generation)
{
  setGeneration(e1, e1Generation);
  setGeneration(e2, e2Generation);
  applyStickyUpdates(e1, e1Generation, e2, e2Generation);
}

void SmtContext::applyStickyUpdates(ENode* e1,
                                    uint32_t e1Generation,
                                    ENode* e2,
                                    uint32_t e2Generation)
{
  Assert(e1->usesCgTable());
  Assert(e2->usesCgTable());
  for (const std::pair<ENode* const, uint32_t>& tg : d_stickyGenerationUpdates)
  {
    if (tg.second < e1Generation && congruent(tg.first, e1))
    {
      setGeneration(e1, tg.second);
    }
    else if (tg.second < e2Generation && congruent(tg.first, e2))
    {
      setGeneration(e2, tg.second);
    }
  }
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
  ENode* r = const_cast<SmtContext*>(this)->getENodeEqTo(
      nodeManager()->operatorOf(Kind::EQUAL), true, 2, args);
  if (r != nullptr)
  {
    Assert(r->isEq());
    Literal l = enode2Literal(r->getRoot());
    return l != s_trueLiteral
           && (l == s_falseLiteral
               || (isRelevant(l) && getAssignment(l) == SAT_VALUE_FALSE));
  }
  return false;
}

ENode* SmtContext::getENodeEqTo(TNode decl,
                                bool commutative,
                                size_t numArgs,
                                ENode* const* args)
{
  ENode* tmp = d_tmpENode.set(decl, commutative, numArgs, args);
  return d_cgTable.find(tmp);
}

void SmtContext::setGeneration(ENode* e, uint32_t generation)
{
  // Patterns with equalities are not supported, so equality generations are
  // not tracked.
  if (e->isEq())
  {
    return;
  }
  // The class generation lives in the congruence root's generation field.
  ENode* cgr = getCgRoot(e);
  cgr->d_generation = generation;
}

bool SmtContext::propagateEqs()
{
  size_t i = 0;
  for (; i < d_eqPropagationQueue.size() && !getCancelFlag(); ++i)
  {
    NewEq& entry = d_eqPropagationQueue[i];
    addEq(entry.d_lhs, entry.d_rhs);
    if (inconsistent())
    {
      d_eqPropagationQueue.clear();
      return false;
    }
  }
  d_eqPropagationQueue.clear();
  return true;
}

bool SmtContext::propagateAtoms()
{
  Assert(!inconsistent());
  for (size_t i = 0; i < d_atomPropagationQueue.size() && !getCancelFlag(); ++i)
  {
    Assert(!inconsistent());
    Literal l = d_atomPropagationQueue[i];
    BoolVar v = l.var();
    SatValue val = getAssignment(v);
    Assert(val != SAT_VALUE_UNKNOWN);
    if (getBdata(v).isENode())
    {
      propagateBoolVarENode(v);
    }
    if (inconsistent())
    {
      return false;
    }
    BoolVarData& d = getBdata(v);
    if (d.isEq())
    {
      TNode n = boolVar2Expr(v);
      Assert(n.getKind() == Kind::EQUAL);
      TNode lhs = n[0];
      TNode rhs = n[1];
      if (lhs.getType().isBoolean())
      {
        // no-op: Boolean equality is handled by the gate clauses
      }
      else if (val == SAT_VALUE_TRUE)
      {
        addEq(getENode(lhs), getENode(rhs));
      }
      else
      {
        if (!addDiseq(getENode(lhs), getENode(rhs)) && !inconsistent())
        {
          setConflict();
        }
      }
    }
    else if (d.isQuantifier())
    {
      // Note that with relevancy lemmas a quantifier may be asserted to
      // false and marked relevant, which happens when a quantifier is part
      // of a conflict clause that becomes unit.
      Assert(isQuantifier(boolVar2Expr(v)));
      if (getAssignment(v) == SAT_VALUE_TRUE)
      {
        assignQuantifier(boolVar2Expr(v));
      }
      else
      {
        // cvc5's quantifiers engine skolemized it when cvc5 asserted it
        // false; the core takes that lemma when it is relevant
        skolemize(boolVar2Expr(v));
      }
    }
    if (inconsistent())
    {
      return false;
    }
  }
  d_atomPropagationQueue.clear();
  return true;
}

void SmtContext::propagateBoolVarENode(BoolVar v)
{
  // Propagate the truth value of v to the enode n associated with it: n is
  // merged with the true (false) enode when v is assigned true (false).
  Assert(getAssignment(v) != SAT_VALUE_UNKNOWN);
  Assert(getBdata(v).isENode());
  SatValue val = getAssignment(v);
  Assert(v < d_prop.getNumBoolVars());
  ENode* n = boolVar2ENode(v);

  bool sign = val == SAT_VALUE_FALSE;
  if (n->mergeTf())
  {
    addEq(n, sign ? d_falseENode : d_trueENode);
  }
  ENode* r = n->getRoot();
  if (r == d_trueENode || r == d_falseENode)
  {
    return;
  }
  // Move the truth value to the other members of the equivalence class if
  // n is the root, or the variable of the root is unassigned.
  if (n == r || !isRelevant(r)  // needed to fix a propagation bug
      || getAssignment(enode2BoolVar(r)) != val)
  {
    ENode* first = n;
    n = n->getNext();
    while (n != first)
    {
      BoolVar v2 = enode2BoolVar(n);
      if (getAssignment(v2) != val)
      {
        assign(Literal(v2, sign));
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
  if (eInternalized(n))
  {
    d_qmanager.notifyRelevant(getENode(n));
  }
}

bool SmtContext::hasPendingTheoryWork() const
{
  return !d_atomPropagationQueue.empty() || d_qmanager.canPropagate()
         || !d_eqPropagationQueue.empty();
}

bool SmtContext::theoryPropagate()
{
  if (!propagateAtoms())
  {
    return false;
  }
  if (!propagateEqs())
  {
    return false;
  }
  if (!getCancelFlag())
  {
    d_qmanager.propagate();
  }
  if (inconsistent())
  {
    return false;
  }
  return true;
}

void SmtContext::assignQuantifier(TNode q) { d_qmanager.notifyAssigned(q); }

void SmtContext::notifyBoolVarDeleted(TNode n)
{
  if (isQuantifier(n))
  {
    d_qmanager.del(n);
  }
}

void SmtContext::pushTheoryScope()
{
  getTrailStack().pushScope();
}

void SmtContext::popTheoryScopeBegin() { d_qmanager.notifyPop(); }

void SmtContext::popTheoryScopeEnd(size_t numScopes)
{
  d_trailStack.popScope(numScopes);
  d_eqPropagationQueue.clear();
  d_atomPropagationQueue.clear();
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
      if (eInternalized(curr))
      {
        ENode* e = getENode(curr);
        uint32_t ilvl = e->getIscopeLvl();
        if (ilvl <= newScopeLvl)
        {
          // neither the node nor its children will be recreated
          continue;
        }
        d_cachedGeneration[curr] = getGeneration(e);
      }
      for (const Node& arg : curr)
      {
        if (isApp(arg) || isQuantifier(arg))
        {
          todo.push_back(arg);
        }
      }
    }
    else if (isQuantifier(curr) && bInternalized(curr))
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
  if (inconsistent())
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
    it.first->second = mkInstance(q, terms, defs);
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
    sendLemma(d, false);
    if (d.isConst())
    {
      continue;
    }
    internalizeAssertion(d, generation);
    // a unit is reasserted as an atom and a sign
    bool neg = d.getKind() == Kind::NOT;
    d_prop.addUnitToReassert(neg ? d[0] : d, neg, true);
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
  sendLemma(norm, instance && options().z3.z3HostLocalInstances);
  internalizeAssertion(norm, generation);
}

void SmtContext::skolemize(TNode q)
{
  if (q.getKind() != Kind::FORALL)
  {
    return;
  }
  if (inconsistent())
  {
    return;
  }
  // The core internalizes the lemma, as it does an instance, so that its
  // witnesses are relevant as the core's own formulas make them: through q,
  // which is relevant here. It also sends it, although cvc5's quantifiers
  // engine did, since cvc5's decisions then treat it as the core's lemma.
  std::vector<Node> defs;
  Node norm = mkSkolemization(q, defs);
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

}  // namespace

void SmtContext::updateGeneration(ENode* e)
{
  // Patterns with equalities are not supported, so there is no need to track
  // the generation of equality nodes.
  if (e->isEq())
  {
    return;
  }

  if (0 < d_generation && d_generation < getGeneration(e))
  {
    if (e->usesCgTable())
    {
      setGenerationSticky(e, d_generation);
    }
    else
    {
      setGeneration(e, d_generation);
    }
  }
}

namespace {

/** Undoes a congruence class generation merge. */
class MergeCgcGenerationsTrail : public Trail
{
 public:
  MergeCgcGenerationsTrail(SmtContext& ctx,
                           ENode* e1,
                           uint32_t e1Generation,
                           ENode* e2,
                           uint32_t e2Generation)
      : d_ctx(ctx),
        d_e1(e1),
        d_e1Generation(e1Generation),
        d_e2(e2),
        d_e2Generation(e2Generation)
  {
  }

  void undo() override
  {
    d_ctx.undoMergeCgcGenerations(d_e1, d_e1Generation, d_e2, d_e2Generation);
  }

 private:
  SmtContext& d_ctx;
  ENode* d_e1;
  uint32_t d_e1Generation;
  ENode* d_e2;
  uint32_t d_e2Generation;
};

}  // namespace

void SmtContext::mergeCgcGenerations(ENode* e1,
                                     uint32_t e1Generation,
                                     ENode* e2)
{
  Assert(e2->isCgr());
  Assert(!d_cgTable.containsPtr(e1));
  Assert(d_cgTable.containsPtr(e2));

  // Push the trail even for a no-op, otherwise e1's generation could not be
  // restored when the merge is undone.
  pushTrail(
      MergeCgcGenerationsTrail(*this, e1, e1Generation, e2, e2->d_generation));

  if (e1Generation >= e2->d_generation)
  {
    return;  // a no-op
  }

  e2->d_generation = e1Generation;
}

void SmtContext::internalizeAssertion(TNode n, uint32_t generation)
{
  uint32_t oldGeneration = d_generation;
  d_generation = generation;
  d_stats.d_maxGeneration.maxAssign(generation);
  Assert(n.getType().isBoolean());
  d_prop.assertRoot(n);
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

  if (bInternalized(n))
  {
    // n was already internalized as a Boolean.
    BoolVar v = getBoolVar(n);

    updateGeneration(n);

    // An enode is still necessary if n is not in a gate context and is an
    // application. A quantifier is handled here as well: Z3 relies on its own
    // preprocessing to keep quantifiers out of term positions, which cvc5's
    // does not, so the enode has to be built rather than assumed away.
    if (!gateCtx && isQuantifier(n))
    {
      if (!eInternalized(n))
      {
        mkENode(n,
                true, /* suppress the arguments */
                true, /* merge with true/false, since this is not a gate */
                false /* congruence closure is not enabled */);
        setEnodeFlag(v, false);
        if (getAssignment(v) != SAT_VALUE_UNKNOWN)
        {
          propagateBoolVarENode(v);
        }
      }
      return;
    }
    if (!gateCtx && isApp(n))
    {
      if (eInternalized(n))
      {
        ENode* e = getENode(n);
        setMergeTf(e, v, false);
      }
      else
      {
        mkENode(n,
                true, /* suppress the arguments: congruence is not used here */
                true, /* merge with true/false, since this is not a gate */
                false /* congruence closure is not enabled */);
        setEnodeFlag(v, false);
        if (getAssignment(v) != SAT_VALUE_UNKNOWN)
        {
          propagateBoolVarENode(v);
        }
      }
      Assert(hasENode(v));
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
  Assert(!bInternalized(n));
  Assert(n.getKind() == Kind::EQUAL);
  internalizeFormulaCore(n, gateCtx);
  BoolVar v = getBoolVar(n);
  getBdata(v).setEqFlag();
}

void SmtContext::internalizeDistinct(TNode n, bool gateCtx)
{
  Assert(!bInternalized(n));
  Assert(n.getKind() == Kind::DISTINCT);
  BoolVar v = mkBoolVar(n);
  Literal l(v);
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
  Literal lDef = getLiteral(def);
  mkGateClause(~l, lDef);
  mkGateClause(l, ~lDef);
  // Reference counts of negations are not tracked, so a relevancy dependency
  // on the equality is added instead.
  Node relDef = def.getKind() == Kind::NOT ? def[0] : def;
  addRelevancyDependency(n, relDef);
  if (!gateCtx)
  {
    mkENode(n, true, true, false);
    setEnodeFlag(v, true);
    // v may have been assigned by the definition clauses before the enode
    // was created.
    if (getAssignment(v) != SAT_VALUE_UNKNOWN)
    {
      propagateBoolVarENode(v);
    }
  }
}

void SmtContext::internalizeQuantifier(TNode q, bool gateCtx)
{
  Assert(!bInternalized(q));
  if (q.getKind() != Kind::FORALL)
  {
    // Z3's preprocessing puts every formula in a form where only universal
    // quantifiers survive, so its internalizer has no case for exists.
    mkBoolVar(q);
    return;
  }
  BoolVar v = mkBoolVar(q);
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
  BoolVarData& d = getBdata(v);
  d.setQuantifierFlag();
  d_qmanager.add(q, generation);
}

void SmtContext::internalizeFormulaCore(TNode n, bool gateCtx)
{
  // Internalize gates, and the (uninterpreted and equality) predicates.
  Assert(!bInternalized(n));
  Assert(!eInternalized(n));

  bool isGateN = expr::isBooleanConnective(n);
  // process the arguments
  for (const Node& arg : n)
  {
    internalizeRec(arg, isGateN);
  }

  bool isNewVar = false;
  BoolVar v;
  // n may already be internalized once its children are, for example the
  // equality in (= (ite c 1 0) 1): internalizing the ite term forces both
  // (= (ite c 1 0) 1) and (= (ite c 1 0) 0).
  if (!bInternalized(n))
  {
    isNewVar = true;
    v = mkBoolVar(n);
  }
  else
  {
    v = getBoolVar(n);
  }

  // A formula needs an enode when it is not in a gate context, or when it has
  // arguments and is not a gate (i.e. an uninterpreted predicate or an
  // equality).
  if (!eInternalized(n) && (!gateCtx || (!isGateN && n.getNumChildren() > 0)))
  {
    bool suppressArgs = isGateN || n.getKind() == Kind::NOT;
    bool mergeTf = !gateCtx;
    mkENode(n, suppressArgs, mergeTf, true);
    setEnodeFlag(v, isNewVar);
    Assert(hasENode(v));
  }
  else if (!gateCtx && eInternalized(n))
  {
    // n was internalized in a gate context while its children were being
    // internalized (ite-term axioms, for example), but it now occurs outside
    // a gate and must be merged with true/false.
    setMergeTf(getENode(n), v, isNewVar);
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
  SetENodeFlagTrail(SmtContext& ctx, BoolVar v) : d_ctx(ctx), d_var(v) {}
  void undo() override { d_ctx.getBdata(d_var).resetENodeFlag(); }

 private:
  SmtContext& d_ctx;
  BoolVar d_var;
};

}  // namespace

void SmtContext::setMergeTf(ENode* n, BoolVar v, bool isNewVar)
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
    pushTrail(SetMergeTfTrail(n));
  }
  n->d_mergeTf = true;
  switch (getAssignment(v))
  {
    case SAT_VALUE_UNKNOWN: break;
    case SAT_VALUE_TRUE:
      if (n->getRoot() != d_trueENode->getRoot())
      {
        pushEq(n, d_trueENode);
      }
      break;
    case SAT_VALUE_FALSE:
      if (n->getRoot() != d_falseENode->getRoot())
      {
        pushEq(n, d_falseENode);
      }
      break;
  }
}

void SmtContext::setEnodeFlag(BoolVar v, bool isNewVar)
{
  Assert(eInternalized(boolVar2Expr(v)));
  BoolVarData& data = getBdata(v);
  if (!data.isENode())
  {
    if (!isNewVar)
    {
      pushTrail(SetENodeFlagTrail(*this, v));
    }
    data.setENodeFlag();
  }
}

void SmtContext::internalizeTerm(TNode n)
{
  if (eInternalized(n))
  {
    updateGeneration(getENode(n));
    return;
  }
  // A term if-then-else does not occur here: the formulas the core
  // internalizes are in the form cvc5's theories take, without them.
  internalizeUninterpreted(n);
  Assert(eInternalized(n));
}

void SmtContext::internalizeUninterpreted(TNode n)
{
  Assert(!eInternalized(n));
  // process the arguments
  for (const Node& arg : n)
  {
    internalizeRec(arg, false);
    Assert(eInternalized(arg));
  }
  if (eInternalized(n))
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
  Assert(!eInternalized(n));
  size_t id = n.getId();
  uint32_t generation = generationOf(n);
  ENode* e = ENode::mk(d_trailStack,
                       d_app2ENode,
                       n,
                       generation,
                       suppressArgs,
                       mergeTf,
                       getScopeLevel(),
                       cgcEnabled);
  if (n.isConst())
  {
    e->markAsInterpreted();
  }
  if (id >= d_app2ENode.size())
  {
    d_app2ENode.resize(id + 1, static_cast<ENode*>(nullptr));
  }
  d_app2ENode[id] = e;
  d_eInternalizedStack.push_back(n);
  d_trailStack.pushPtr(&d_mkENodeTrail);
  d_enodes.push_back(e);
  if (e->getNumArgs() > 0)
  {
    if (e->isTrueEq())
    {
      BoolVar v = enode2BoolVar(e);
      assign(Literal(v));
      e->d_cg = e;
      pushEq(e, d_trueENode);
    }
    else if (cgcEnabled)
    {
      ENode* r = d_cgTable.insert(e);
      if (e != r)
      {
        e->d_cg = r;
        // Patterns with equalities are not supported, so equality
        // generations are not tracked.
        if (!e->isEq())
        {
          mergeCgcGenerations(e, generation, r);
        }
        pushNewCongruence(e, r);
      }
      else
      {
        e->d_cg = e;
      }
    }
    else
    {
      e->d_cg = e;
    }
    if (!e->isEq())
    {
      uint32_t declId = getDeclId(e->getDecl());
      if (declId >= d_decl2ENodes.size())
      {
        d_decl2ENodes.resize(declId + 1);
      }
      d_decl2ENodes[declId].push_back(e);
    }
  }

  Assert(eInternalized(n));
  d_stats.d_numMkENode++;
  return e;
}

void SmtContext::undoMkENode()
{
  Assert(!d_eInternalizedStack.empty());
  d_stats.d_numDelENode++;
  Node n = d_eInternalizedStack.back();
  size_t nId = n.getId();
  ENode* e = d_app2ENode[nId];
  d_app2ENode[nId] = nullptr;
  if (e->isCgr() && e->usesCgTable())
  {
    Assert(d_cgTable.containsPtr(e));
    d_cgTable.erase(e);
  }
  if (e->getNumArgs() > 0 && !e->isEq())
  {
    uint32_t declId = getDeclId(e->getDecl());
    Assert(declId < d_decl2ENodes.size());
    Assert(d_decl2ENodes[declId].back() == e);
    d_decl2ENodes[declId].pop_back();
  }
  e->destroy();
  Assert(d_eInternalizedStack.size() == d_enodes.size());
  d_enodes.pop_back();
  d_eInternalizedStack.pop_back();
  d_stickyGenerationUpdates.erase(e);
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

void SmtContext::lemma(const Node& lem, theory::LemmaProperty p)
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

Node SmtContext::preprocessForTheories(TNode n,
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

Node SmtContext::mkInstance(TNode q,
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

Node SmtContext::mkSkolemization(TNode q, std::vector<Node>& defs)
{
  return preprocessLemma(getSkolemization(toHost(q)),
                         defs,
                         theory::InferenceId::QUANTIFIERS_SKOLEMIZE);
}

Node SmtContext::preprocessLemma(const TrustNode& trn,
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

void SmtContext::assertInput(const std::vector<Node>& assertions)
{
  PropCore& core = d_prop;
  for (const Node& a : assertions)
  {
    core.assertFormula(toCore(a));
  }
}

void SmtContext::preRegister(TNode atom)
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

void SmtContext::assertFact(TNode literal)
{
  if (d_inConflict)
  {
    return;
  }
  PropCore& core = d_prop;
  syncLevel();
  Trace("z3-host") << "assert " << literal << std::endl;
  Literal l = core.hostLiteral(toCore(literal));
  if (!core.hostAssign(l))
  {
    enterConflict();
  }
}

void SmtContext::check(theory::Theory::Effort effort,
                       const theory::TheoryState& state)
{
  // the literals asserted since the last check
  d_tracker->flush(state);
  d_needCheck = false;
  Statistics& stats = d_stats;
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
  PropCore& core = d_prop;
  syncLevel();
  // the equalities cvc5's theories derived since the last check
  applyMasterMerges();
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
    bool done = core.hostFinalCheck();
    Trace("z3-host") << "final check " << (done ? "done" : "continue")
                     << " at level " << context()->getLevel() << std::endl;
    if (done)
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
      if (hasQuantifiers())
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
    splitPendingAtoms();
    if (d_needCheck)
    {
      return;
    }
  }
  d_qim.setModelUnsound(theory::IncompleteId::UNKNOWN);
}

void SmtContext::presolve(theory::eq::EqualityEngine* master)
{
  d_masterEe = master;
  if (!d_setup)
  {
    d_prop.hostInit();
    d_setup = true;
  }
  // The strategies of the decision manager are cleared after each check-sat.
  d_te->getDecisionManager()->registerStrategy(
      theory::DecisionManager::STRAT_QUANT_Z3_SPLIT, d_splitStrategy.get());
}

TrustNode SmtContext::getSkolemization(TNode q)
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

void SmtContext::notifyMasterMerge(TNode t1, TNode t2)
{
  // The Boolean classes are those of the atoms, whose values reach the core
  // as facts.
  if (!t1.getType().isBoolean())
  {
    d_pendingMerges.emplace_back(t1, t2);
  }
}

Node SmtContext::masterTermOf(TNode rep) const
{
  auto it = d_masterTerm.find(rep);
  return it == d_masterTerm.end() ? Node::null() : it->second;
}

void SmtContext::mergeMasterTerms(TNode a, TNode b)
{
  if (a == b || !eInternalized(a) || !eInternalized(b))
  {
    return;
  }
  pushEq(getENode(a), getENode(b));
  d_stats.d_numShadowMerges++;
}

void SmtContext::applyMasterMerges()
{
  if (d_masterEe == nullptr)
  {
    return;
  }
  if (inconsistent())
  {
    d_pendingMerges.clear();
    return;
  }
  // The merges notified, in order: each is keyed by the representatives of
  // the time, as d_masterTerm is.
  for (const std::pair<Node, Node>& p : d_pendingMerges)
  {
    const Node& r1 = p.first;
    const Node& r2 = p.second;
    Node c1 = masterTermOf(r1);
    Node c2 = masterTermOf(r2);
    if (c1.isNull() && c2.isNull())
    {
      continue;
    }
    if (c1.isNull())
    {
      // r1 represents the merged class, which now holds c2
      d_masterTerm.insert(r1, c2);
      continue;
    }
    if (c2.isNull())
    {
      continue;
    }
    mergeMasterTerms(c1, c2);
  }
  d_pendingMerges.clear();
  // The terms the core internalized since the last call, which may have
  // been merged in the master equality engine before.
  size_t n = getNumEInternalized();
  for (size_t i = std::min(d_masterIdx.get(), n); i < n; ++i)
  {
    TNode t = getEInternalized(i);
    if (t.getType().isBoolean() || !d_masterEe->hasTerm(t))
    {
      continue;
    }
    Node r = d_masterEe->getRepresentative(t);
    Node c = masterTermOf(r);
    if (c.isNull())
    {
      d_masterTerm.insert(r, t);
    }
    else
    {
      mergeMasterTerms(t, c);
    }
  }
  d_masterIdx = n;
}

void SmtContext::notifyPop()
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
  d_pendingMerges.clear();
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

void SmtContext::syncLevel()
{
  PropCore& core = d_prop;
  uint32_t lvl = context()->getLevel();
  // The scopes above the lowest level the SAT context reached since the last
  // call belong to a branch it left, even if it is now as deep again.
  uint32_t popTo = std::min(lvl, d_popLevel);
  d_popLevel = UINT32_MAX;
  if (core.getScopeLevel() > popTo)
  {
    Statistics& stats = d_stats;
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

void SmtContext::enterConflict()
{
  // The conflict follows from the facts cvc5 asserted and the lemmas it was
  // sent, so cvc5's theories find it themselves. Until cvc5 backtracks below
  // the current level, the core does nothing.
  d_stats.d_numShadowConflicts++;
  d_inConflict = true;
  d_conflictLevel = context()->getLevel();
}

void SmtContext::sendLemma(const Node& coreLem, bool local)
{
  Statistics& stats = d_stats;
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

Node SmtContext::delayUnit(const Node& lem)
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
  d_stats.d_numHostDelayedUnits++;
  d_delayedUnits.push_back(lem);
  return weakened;
}

void SmtContext::splitNewlyRelevant()
{
  PropCore& core = d_prop;
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
    if (core.getAssignment(v) == SAT_VALUE_UNKNOWN && core.isRelevant(v))
    {
      split(v);
    }
  }
}

void SmtContext::split(BoolVar v)
{
  PropCore& core = d_prop;
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
  d_stats.d_numHostSplits++;
  // cvc5 must search on, for the decision, even after a full check
  d_qim.markUsed();
  d_needCheck = true;
}

Node SmtContext::SplitStrategy::getNextDecisionRequest()
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

void SmtContext::splitPendingAtoms()
{
  PropCore& core = d_prop;
  for (size_t i = 0, n = core.getNumBoolVars(); i < n; ++i)
  {
    BoolVar v = static_cast<BoolVar>(i);
    if (core.getAssignment(v) == SAT_VALUE_UNKNOWN && core.isRelevant(v))
    {
      split(v);
    }
  }
}

bool SmtContext::propagateAndReport()
{
  PropCore& core = d_prop;
  bool ok = core.hostPropagate();
  if (!ok)
  {
    enterConflict();
    return false;
  }
  splitNewlyRelevant();
  return true;
}

Node SmtContext::toCore(TNode n)
{
  Node nc = d_normalizer.normalize(n);
  if (nc != n)
  {
    recordRenamedAtoms(n, nc);
  }
  return nc;
}

void SmtContext::recordRenamedAtoms(TNode n, TNode nc)
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

Node SmtContext::toHost(TNode n)
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

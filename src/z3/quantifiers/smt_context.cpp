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
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_context.cpp, and recast in cvc5 style.
 */

#include "z3/quantifiers/smt_context.h"

#include <algorithm>
#include <cmath>
#include <fstream>

#include "base/output.h"
#include "expr/node_algorithm.h"
#include "expr/node_manager.h"
#include "options/smt_options.h"
#include "options/z3_options.h"
#include "printer/printer.h"
#include "smt/env.h"
#include "smt/print_benchmark.h"
#include "smt/set_defaults.h"
#include "smt/solver_engine.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/theory.h"
#include "util/resource_manager.h"
#include "util/statistics_registry.h"
#include "z3/quantifiers/quantifier_manager.h"
#include "z3/util/types.h"

namespace cvc5::internal {
namespace z3 {

namespace {

}  // namespace

SmtContext::SmtContext(Env& env)
    : EnvObj(env),
      d_prop(env, *this, d_stats),
      d_normalizer(env.getNodeManager()),
      d_qmanager(nullptr),
      d_trueENode(nullptr),
      d_falseENode(nullptr),
      d_isDiseqTmp(nullptr),
      d_trailStack(d_trailRegion),
      d_generation(0),
      d_mkENodeTrail(*this)
{
  d_qmanager.reset(new QuantifierManager(*this));
  registerStatistics();
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
  d_qmanager.reset(nullptr);
  if (d_isDiseqTmp != nullptr)
  {
    d_isDiseqTmp->delEh(false);
    ENode::delDummy(d_isDiseqTmp);
    d_isDiseqTmp = nullptr;
  }
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

  d_qmanager->addEqEh(r1, r2);

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
        LBool val = getAssignment(v);
        if (val != L_TRUE)
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

      ENodeBoolPair r = d_cgTable.insert(parent);
      ENode* parentPrime = r.first;
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
      if (getAssignment(l) != L_TRUE)
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
    LBool val1 = getAssignment(v1);
    LBool val2 = getAssignment(v2);
    if (val1 != val2)
    {
      if (val2 == L_UNDEF)
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
  LBool val = getAssignment(vSource);
  Assert(val != L_UNDEF);
  bool sign = val == L_FALSE;
  ENode* first = target;
  do
  {
    BoolVar v2 = enode2BoolVar(target);
    LBool val2 = getAssignment(v2);
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

    ENodeBoolPair r = d_cgTable.insert(parent);
    parent->d_cg = r.first;
    if (r.first == parent)
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
  SmtContext* self = const_cast<SmtContext*>(this);
  if (d_isDiseqTmp == nullptr
      || d_isDiseqTmp->getExpr()[0].getType() != n1->getSort())
  {
    if (d_isDiseqTmp != nullptr)
    {
      ENode::delDummy(self->d_isDiseqTmp);
    }
    self->d_isDiseqTmpExpr =
        nodeManager()->mkNode(Kind::EQUAL, n1->getExpr(), n2->getExpr());
    // The dummy enode's arguments are overwritten below, so the enodes of the
    // arguments do not need to be internalized.
    self->d_isDiseqTmp = ENode::mkDummy(d_app2ENode, self->d_isDiseqTmpExpr);
  }
  d_isDiseqTmp->argsPtr()[0] = n1;
  d_isDiseqTmp->argsPtr()[1] = n2;
  Assert(d_isDiseqTmp->getNumArgs() == 2);
  ENode* r = d_cgTable.find(d_isDiseqTmp);
  if (r != nullptr)
  {
    Assert(r->isEq());
    Literal l = enode2Literal(r->getRoot());
    return l != s_trueLiteral
           && (l == s_falseLiteral
               || (isRelevant(l) && getAssignment(l) == L_FALSE));
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
    LBool val = getAssignment(v);
    Assert(val != L_UNDEF);
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
      else if (val == L_TRUE)
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
      if (getAssignment(v) == L_TRUE)
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
  Assert(getAssignment(v) != L_UNDEF);
  Assert(getBdata(v).isENode());
  LBool val = getAssignment(v);
  Assert(v < d_prop.getNumBoolVars());
  ENode* n = boolVar2ENode(v);

  bool sign = val == L_FALSE;
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

void SmtContext::relevantEh(TNode n)
{
  if (!isApp(n))
  {
    return;
  }
  if (eInternalized(n))
  {
    d_qmanager->relevantEh(getENode(n));
  }
}

bool SmtContext::hasPendingTheoryWork() const
{
  return !d_atomPropagationQueue.empty() || d_qmanager->canPropagate()
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
    d_qmanager->propagate();
  }
  if (inconsistent())
  {
    return false;
  }
  return true;
}

void SmtContext::assignQuantifier(TNode q) { d_qmanager->assignEh(q); }

void SmtContext::notifyBoolVarDeleted(TNode n)
{
  if (isQuantifier(n))
  {
    d_qmanager->del(n);
  }
}

void SmtContext::pushTheoryScope()
{
  d_region.pushScope();
  getTrailStack().pushScope();

  d_qmanager->push();
}

void SmtContext::popTheoryScopeBegin(size_t numScopes)
{
  d_qmanager->pop(numScopes);
}

void SmtContext::popTheoryScopeEnd(size_t numScopes)
{
  d_trailStack.popScope(numScopes);
  d_eqPropagationQueue.clear();
  d_region.popScope(numScopes);
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
      d_cachedGeneration[curr] = d_qmanager->getGeneration(curr);
      todo.push_back(getQuantBody(curr));
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
  Assert(d_instanceMaker);
  std::vector<Node> key{q};
  key.insert(key.end(), terms.begin(), terms.end());
  auto it = d_instanceForms.emplace(
      q.getNodeManager()->mkNode(Kind::SEXPR, key), Node());
  std::vector<Node> defs;
  if (it.second)
  {
    it.first->second = d_instanceMaker(q, terms, defs);
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
  Assert(d_lemmaSender);
  for (const Node& d : defs)
  {
    d_lemmaSender(d, false);
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
  d_lemmaSender(norm, instance);
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
  Assert(d_skolemizer);
  std::vector<Node> defs;
  Node norm = d_skolemizer(q, defs);
  d_stats.d_numSkolemizations++;
  internalizePreprocessed(norm, defs, generationOf(q), false);
}

void SmtContext::initSearchEh() { d_qmanager->initSearchEh(); }

FinalCheckStatus SmtContext::finalCheck()
{
  d_stats.d_numFinalChecks++;
  Trace("z3-events") << "FINALCHECK " << d_stats.d_numFinalChecks << std::endl;

  FinalCheckStatus result = d_qmanager->finalCheckEh(false);
  if (result != FC_DONE)
  {
    return result;
  }
  result = d_qmanager->finalCheckEh(true);
  if (result != FC_CONTINUE && canPropagate())
  {
    return FC_CONTINUE;
  }
  return result;
}

void SmtContext::registerStatistics()
{
  StatisticsRegistry& reg = statisticsRegistry();
  // Note the handle is stored first and only then pointed at the counter:
  // the temporary returned by registerReference detaches the counter when it
  // is destroyed at the end of the statement.
  auto add = [&](const char* name, const uint64_t& v) {
    d_regStats.push_back(reg.registerReference<uint64_t>(name, false));
    d_regStats.back().set(v);
  };
  add("z3::propagations", d_stats.d_numPropagations);
  add("z3::binPropagations", d_stats.d_numBinPropagations);
  add("z3::addEq", d_stats.d_numAddEq);
  add("z3::finalChecks", d_stats.d_numFinalChecks);
  add("z3::assertedFormulas", d_stats.d_numAssertedFormulas);
  add("z3::mkBoolVar", d_stats.d_numMkBoolVar);
  add("z3::delBoolVar", d_stats.d_numDelBoolVar);
  add("z3::mkENode", d_stats.d_numMkENode);
  add("z3::delENode", d_stats.d_numDelENode);
  add("z3::mkClause", d_stats.d_numMkClause);
  add("z3::delClause", d_stats.d_numDelClause);
  add("z3::mkBinClause", d_stats.d_numMkBinClause);
  add("z3::mkLits", d_stats.d_numMkLits);
  add("z3::maxGeneration", d_stats.d_maxGeneration);
  add("z3::assignments", d_stats.d_numAssignments);
  add("z3::instances", d_stats.d_numInstances);
  add("z3::skolemizations", d_stats.d_numSkolemizations);
  add("z3::lazyInstances", d_stats.d_numLazyInstances);
  add("z3::instancesCheckerSat", d_stats.d_numInstancesCheckerSat);
  add("z3::instancesSimplifyTrue", d_stats.d_numInstancesSimplifyTrue);
  add("z3::hostChecks", d_stats.d_numHostChecks);
  add("z3::hostFullChecks", d_stats.d_numHostFullChecks);
  add("z3::hostPops", d_stats.d_numHostPops);
  add("z3::hostScopesPopped", d_stats.d_numHostScopesPopped);
  add("z3::hostRestarts", d_stats.d_numHostRestarts);
  add("z3::hostLemmas", d_stats.d_numHostLemmas);
  add("z3::hostDuplicateLemmas", d_stats.d_numHostDuplicateLemmas);
  add("z3::hostSplits", d_stats.d_numHostSplits);
  add("z3::shadowMerges", d_stats.d_numShadowMerges);
  add("z3::shadowConflicts", d_stats.d_numShadowConflicts);
  add("z3::hostDelayedUnits", d_stats.d_numHostDelayedUnits);
  add("z3::missedInstances", d_stats.d_numMissedInstances);
  add("z3::mamRelevantEh", d_stats.d_numMamRelevantEh);
  add("z3::mamRelevantApp", d_stats.d_numMamRelevantApp);
  add("z3::mamTrees", d_stats.d_numMamTrees);
  add("z3::setRelevant", d_stats.d_numSetRelevant);
  add("z3::mamEqCandidates", d_stats.d_numMamEqCandidates);
  add("z3::mamAddEq", d_stats.d_numMamAddEq);
  add("z3::mamCandidates", d_stats.d_numMamCandidates);
  add("z3::mamExecs", d_stats.d_numMamExecs);
  add("z3::mamMatches", d_stats.d_numMamMatches);
}

}  // namespace z3
}  // namespace cvc5::internal

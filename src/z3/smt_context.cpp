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

#include "z3/smt_context.h"

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
#include "z3/quantifier_manager.h"
#include "z3/theory_cvc5.h"
#include "z3/util/luby.h"
#include "z3/util/util.h"

namespace cvc5::internal {
namespace z3 {

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

SmtContext::SmtContext(Env& env, Params& p)
    : EnvObj(env),
      d_params(p),
      d_relevancyLvl(p.d_relevancyLvl),
      d_prop(env, *this, p, d_stats),
      d_normalizer(env.getNodeManager()),
      d_connNormalizer(env.getNodeManager(),
                       env.getOptions().z3.z3EliminateAnd),
      d_assertionRewriter(env),
      d_nnf(env.getNodeManager()),
      d_ngPushAppIte(env.getNodeManager(),
                     p.d_ngLiftIte == Params::LI_CONSERVATIVE),
      d_patternInference(env.getNodeManager(), d_params),
      d_qmanager(nullptr),
      d_relevancyPropagator(new RelevancyPropagator(*this)),
      d_random(p.d_randomSeed),
      d_fingerprints(d_region),
      d_assertedFormulasQhead(0),
      d_hasQuantifiers(false),
      d_internalizingAssertions(false),
      d_finalCheckIdx(0),
      d_trueENode(nullptr),
      d_falseENode(nullptr),
      d_theories(s_numTheories, nullptr),
      d_isDiseqTmp(nullptr),
      d_dynAckManager(*this, p),
      d_explainer(*this, d_dynAckManager),
      d_unknown("unknown"),
      d_generation(0),
      d_setupDone(false),
      d_mkENodeTrail(*this)
{
  d_qmanager.reset(new QuantifierManager(*this, p));
  d_prop.finishInit();

  registerStatistics();

  init();

  if (!relevancy())
  {
    d_params.d_relevancyLemma = false;
  }
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
  d_relevancyPropagator.reset(nullptr);
  for (Theory* th : d_theorySet)
  {
    th->flushEh();
  }
  d_prop.flushClauses();
  delJustifications(d_justifications, 0);
  d_trailStack.reset();
  d_qmanager.reset(nullptr);
  if (d_isDiseqTmp != nullptr)
  {
    d_isDiseqTmp->delEh(false);
    ENode::delDummy(d_isDiseqTmp);
    d_isDiseqTmp = nullptr;
  }
  for (Theory* th : d_theorySet)
  {
    delete th;
  }
  d_theorySet.clear();
  std::fill(d_theories.begin(), d_theories.end(), nullptr);
}

uint32_t SmtContext::relevancyLvl() const
{
  return std::min(d_relevancyLvl, d_params.d_relevancyLvl);
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

Node SmtContext::mkEqAtom(TNode lhs, TNode rhs)
{
  Theory* th = getTheory(theory::Theory::theoryOf(lhs.getType()));
  if (th != nullptr)
  {
    return th->mkEqAtom(lhs, rhs);
  }
  if (lhs.getId() > rhs.getId())
  {
    std::swap(lhs, rhs);
  }
  return nodeManager()->mkNode(Kind::EQUAL, lhs, rhs);
}

void SmtContext::pushNewThEq(TheoryId th, TheoryVar lhs, TheoryVar rhs)
{
  Assert(lhs != rhs);
  Assert(lhs != s_nullTheoryVar);
  Assert(rhs != s_nullTheoryVar);
  Assert(th != s_nullTheoryId);
  d_thEqPropagationQueue.push_back(NewThEq(th, lhs, rhs));
}

void SmtContext::pushNewThDiseq(TheoryId th, TheoryVar lhs, TheoryVar rhs)
{
  Assert(lhs != rhs);
  Assert(lhs != s_nullTheoryVar);
  Assert(rhs != s_nullTheoryVar);
  Assert(th != s_nullTheoryId);
  Theory* t = getTheory(th);
  if (t->getENode(lhs)->isInterpreted() && t->getENode(rhs)->isInterpreted())
  {
    return;
  }
  d_thDiseqPropagationQueue.push_back(NewThEq(th, lhs, rhs));
}

namespace {

/** Undoes an addEq. */
class AddEqTrail : public Trail
{
 public:
  AddEqTrail(SmtContext& ctx, ENode* r1, ENode* n1, size_t r2NumParents)
      : d_ctx(ctx), d_r1(r1), d_n1(n1), d_r2NumParents(r2NumParents)
  {
  }
  void undo() override;

 private:
  SmtContext& d_ctx;
  ENode* d_r1;
  ENode* d_n1;
  size_t d_r2NumParents;
};

}  // namespace

void SmtContext::addEq(ENode* n1, ENode* n2, EqJustification js)
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
    setConflict(mkJustification(EqConflictJustification(n1, n2, js)));
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

  mergeTheoryVars(n2, n1, js);

  // The proof forest, before:
  //   n1 -> ... -> r1
  //   n2 -> ... -> r2
  invertTrans(n1);
  n1->d_trans.d_target = n2;
  n1->d_trans.d_justification = js;
  // and after:
  //   r1 -> ..  -> n1 -> n2 -> ... -> r2

  removeParentsFromCgTable(r1);

  ENode* curr = r1;
  do
  {
    curr->d_root = r2;
    curr = curr->d_next;
  } while (curr != r1);

  Assert(r1->getRoot() == r2);
  reinsertParentsIntoCgTable(r1, r2, n1, n2, js);

  // The AddEqTrail is pushed after reinsertParentsIntoCgTable, because the
  // latter may push merge-generation trails and addEq must be undone before
  // those are.
  pushTrail(AddEqTrail(*this, r1, n1, r2NumParents));

  if (n2->isBool())
  {
    propagateBoolENodeAssignment(r1, r2, n1, n2);
  }

  // merge the equivalence classes
  std::swap(r1->d_next, r2->d_next);

  // update the class size
  r2->d_classSize += r1->d_classSize;
  r2->d_isShared = 2;
}

namespace {

void AddEqTrail::undo() { d_ctx.undoAddEq(d_r1, d_n1, d_r2NumParents); }

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

void SmtContext::reinsertParentsIntoCgTable(
    ENode* r1, ENode* r2, ENode* n1, ENode* n2, EqJustification js)
{
  // Reinsert the parents of r1 that removeParentsFromCgTable took out. Some
  // of them become congruent to other enodes, which propagates a new
  // equality. The ones that remain congruence roots move to r2's parent list.
  //
  // n1, n2 and js implement dynamic Ackermannization: js justifies n1 = n2,
  // and that equality is the one that implied r1 = r2.
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
          if (val == L_FALSE && js.getKind() == EqJustification::CONGRUENCE)
          {
            d_dynAckManager.cgConflictEh(n1->getExpr(), n2->getExpr());
          }
          assign(Literal(v),
                 mkJustification(EqPropagationJustification(lhs, rhs)));
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
      bool usedCommutativity = r.second;
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
        pushNewCongruence(parent, parentPrime, usedCommutativity);
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

void SmtContext::invertTrans(ENode* n)
{
  // A branch of the transitivity forest is the sequence starting at n and
  // ending at n->getRoot(); this inverts it.
  ENode* curr = n->d_trans.d_target;
  ENode* prev = n;
  EqJustification js = n->d_trans.d_justification;
  prev->d_trans.d_target = nullptr;
  prev->d_trans.d_justification = s_nullEqJustification;
  while (curr != nullptr)
  {
    ENode* newCurr = curr->d_trans.d_target;
    EqJustification newJs = curr->d_trans.d_justification;
    curr->d_trans.d_target = prev;
    curr->d_trans.d_justification = js;
    prev = curr;
    js = newJs;
    curr = newCurr;
  }
}

TheoryVar SmtContext::getClosestVar(ENode* n, TheoryId thId)
{
  // Return a theory variable for thId that is as close to n as possible along
  // the proof branch n -> ... -> root. Sending the theories the natural chain
  // of equalities, rather than always pairing against the root, keeps the
  // justifications they build free of unnecessary detours.
  if (thId == s_nullTheoryId)
  {
    return s_nullTheoryVar;
  }
  while (n != nullptr)
  {
    TheoryVar v = n->getThVar(thId);
    if (v != s_nullTheoryVar)
    {
      return v;
    }
    n = n->d_trans.d_target;
  }
  return s_nullTheoryVar;
}

void SmtContext::mergeTheoryVars(ENode* n2, ENode* n1, EqJustification js)
{
  // Merge the theory variables of n2->getRoot() and n1->getRoot() into
  // n2->getRoot(), propagating the new theory variable equalities.
  ENode* r2 = n2->getRoot();
  ENode* r1 = n1->getRoot();
  if (!r1->hasThVars() && !r2->hasThVars())
  {
    return;
  }

  TheoryId fromTh = s_nullTheoryId;

  if (js.getKind() == EqJustification::JUSTIFICATION)
  {
    fromTh = js.getJustification()->getFromTheory();
  }

  if (r2->d_thVarList.getNext() == nullptr
      && r1->d_thVarList.getNext() == nullptr)
  {
    // the common case: r2 and r1 have at most one theory variable each
    TheoryId t2 = static_cast<TheoryId>(r2->d_thVarList.getId());
    TheoryId t1 = static_cast<TheoryId>(r1->d_thVarList.getId());
    TheoryVar v2 = d_params.d_newCore2ThEq ? getClosestVar(n2, t2)
                                           : r2->d_thVarList.getVar();
    TheoryVar v1 = d_params.d_newCore2ThEq ? getClosestVar(n1, t1)
                                           : r1->d_thVarList.getVar();
    if (v2 != s_nullTheoryVar && v1 != s_nullTheoryVar)
    {
      if (t1 == t2)
      {
        // only send the equality to the theory if the theory did not
        // propagate it itself
        if (t1 != fromTh)
        {
          pushNewThEq(t1, v2, v1);
        }
      }
      else
      {
        // the uncommon case: r2 ends up with two theory variables
        r2->addThVar(v1, t1, getRegion());
        pushNewThDiseqs(r2, v1, getTheory(t1));
        pushNewThDiseqs(r1, v2, getTheory(t2));
      }
    }
    else if (v1 == s_nullTheoryVar && v2 != s_nullTheoryVar)
    {
      pushNewThDiseqs(r1, v2, getTheory(t2));
    }
    else if (v1 != s_nullTheoryVar && v2 == s_nullTheoryVar)
    {
      r2->d_thVarList.setVar(v1);
      r2->d_thVarList.setId(t1);
      pushNewThDiseqs(r2, v1, getTheory(t1));
    }
    return;
  }

  // r1 and/or r2 have more than one theory variable
  const TheoryVarList* l2 = r2->getThVarList();
  while (l2 != nullptr)
  {
    TheoryId t2 = static_cast<TheoryId>(l2->getId());
    TheoryVar v2 =
        d_params.d_newCore2ThEq ? getClosestVar(n2, t2) : l2->getVar();
    Assert(v2 != s_nullTheoryVar);
    Assert(t2 != s_nullTheoryId);
    TheoryVar v1 =
        d_params.d_newCore2ThEq ? getClosestVar(n1, t2) : r1->getThVar(t2);

    if (v1 != s_nullTheoryVar)
    {
      if (t2 != fromTh)
      {
        pushNewThEq(t2, v2, v1);
      }
    }
    else
    {
      pushNewThDiseqs(r1, v2, getTheory(t2));
    }
    l2 = l2->getNext();
  }

  const TheoryVarList* l1 = r1->getThVarList();
  while (l1 != nullptr)
  {
    TheoryId t1 = static_cast<TheoryId>(l1->getId());
    TheoryVar v1 =
        d_params.d_newCore2ThEq ? getClosestVar(n1, t1) : l1->getVar();
    Assert(v1 != s_nullTheoryVar);
    Assert(t1 != s_nullTheoryId);
    TheoryVar v2 = r2->getThVar(t1);
    if (v2 == s_nullTheoryVar)
    {
      r2->addThVar(v1, t1, getRegion());
      pushNewThDiseqs(r2, v1, getTheory(t1));
    }
    l1 = l1->getNext();
  }
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
        assign(l, mkJustification(EqRootPropagationJustification(curr)));
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
      if (val2 != L_UNDEF && congruent(source, target)
          && source->getNumArgs() > 0)
      {
        d_dynAckManager.cgConflictEh(source->getExpr(), target->getExpr());
      }
      assign(Literal(v2, sign),
             mkJustification(MpIffJustification(source, target)));
    }
    target = target->getNext();
  } while (first != target);
}

void SmtContext::undoAddEq(ENode* r1, ENode* n1, size_t r2NumParents)
{
  ENode* r2 = r1->getRoot();

  // restore r2's class size
  r2->d_classSize -= r1->d_classSize;
  r2->d_isShared = 2;

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
      Assert(parent->isCgr());
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

  // restore the theory variables
  if (r2->d_thVarList.getNext() == nullptr)
  {
    // the common case: r2 has at most one variable
    TheoryVar v2 = r2->d_thVarList.getVar();
    if (v2 != s_nullTheoryVar)
    {
      TheoryId t2 = static_cast<TheoryId>(r2->d_thVarList.getId());
      if (getTheory(t2)->getENode(v2)->getRoot() != r2)
      {
        Assert(getTheory(t2)->getENode(v2)->getRoot() == r1);
        // remove the variable from r2
        r2->d_thVarList.setVar(s_nullTheoryVar);
        r2->d_thVarList.setId(s_nullTheoryId);
      }
    }
  }
  else
  {
    restoreTheoryVars(r2, r1);
  }

  // The proof forest, before: r1 -> ..  -> n1 -> n2 -> ... -> r2
  n1->d_trans.d_target = nullptr;
  n1->d_trans.d_justification = s_nullEqJustification;
  invertTrans(r1);
  // and after:
  //   n1 -> ... -> r1
  //   n2 -> ... -> r2
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

void SmtContext::restoreTheoryVars(ENode* r2, ENode* r1)
{
  // Delete any theory variable v2 of r2 that is no longer equivalent to r2.
  // Any such variable must instead be equivalent to r1, which is what the
  // assertion below checks.
  (void)r1;
  Assert(r2->getRoot() == r2);
  TheoryVarList* newL2 = nullptr;
  TheoryVarList* l2 = r2->getThVarListPtr();
  while (l2 != nullptr)
  {
    TheoryVar v2 = l2->getVar();
    TheoryId t2 = static_cast<TheoryId>(l2->getId());

    if (getTheory(t2)->getENode(v2)->getRoot() != r2)
    {
      Assert(getTheory(t2)->getENode(v2)->getRoot() == r1);
      l2 = l2->getNext();
    }
    else
    {
      if (newL2 != nullptr)
      {
        newL2->setNext(l2);
        newL2 = l2;
      }
      else
      {
        r2->d_thVarList = *l2;
        newL2 = &(r2->d_thVarList);
      }
      l2 = l2->getNext();
    }
  }

  if (newL2 != nullptr)
  {
    newL2->setNext(nullptr);
  }
  else
  {
    r2->d_thVarList.setVar(s_nullTheoryVar);
    r2->d_thVarList.setNext(nullptr);
  }
}

bool SmtContext::addDiseq(ENode* n1, ENode* n2)
{
  ENode* r1 = n1->getRoot();
  ENode* r2 = n2->getRoot();

  if (r1 == r2)
  {
    TheoryId t1 = static_cast<TheoryId>(r1->d_thVarList.getId());
    if (t1 == s_nullTheoryId)
    {
      return false;
    }
    return getTheory(t1)->useDiseqs();
  }

  // propagate the disequality to the theories
  if (r1->d_thVarList.getNext() == nullptr
      && r2->d_thVarList.getNext() == nullptr)
  {
    // the common case: r2 and r1 have at most one theory variable each
    TheoryId t1 = static_cast<TheoryId>(r1->d_thVarList.getId());
    TheoryVar v1 = d_params.d_newCore2ThEq ? getClosestVar(n1, t1)
                                           : r1->d_thVarList.getVar();
    TheoryVar v2 = d_params.d_newCore2ThEq ? getClosestVar(n2, t1)
                                           : r2->d_thVarList.getVar();
    if (t1 != s_nullTheoryId && v1 != s_nullTheoryVar && v2 != s_nullTheoryVar
        && t1 == static_cast<TheoryId>(r2->d_thVarList.getId()))
    {
      if (getTheory(t1)->useDiseqs())
      {
        pushNewThDiseq(t1, v1, v2);
      }
    }
  }
  else
  {
    const TheoryVarList* l1 = r1->getThVarList();
    while (l1 != nullptr)
    {
      TheoryId t1 = static_cast<TheoryId>(l1->getId());
      TheoryVar v1 =
          d_params.d_newCore2ThEq ? getClosestVar(n1, t1) : l1->getVar();
      Theory* th = getTheory(t1);
      if (th->useDiseqs())
      {
        TheoryVar v2 =
            d_params.d_newCore2ThEq ? getClosestVar(n2, t1) : r2->getThVar(t1);
        if (v2 != s_nullTheoryVar)
        {
          pushNewThDiseq(t1, v1, v2);
        }
      }
      l1 = l1->getNext();
    }
  }
  return true;
}

bool SmtContext::isDiseq(ENode* n1, ENode* n2) const
{
  return isDiseqCore(n1, n2, true);
}

bool SmtContext::isDiseqNoValueCheck(ENode* n1, ENode* n2) const
{
  return isDiseqCore(n1, n2, false);
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

bool SmtContext::isDiseqSlow(ENode* n1, ENode* n2) const
{
  if (n1->getNumParents() > n2->getNumParents())
  {
    std::swap(n1, n2);
  }
  for (ENode* parent : n1->getConstParents())
  {
    if (parent->isEq() && isRelevant(parent->getExpr())
        && getAssignment(enode2BoolVar(parent)) == L_FALSE
        && ((parent->getArg(0)->getRoot() == n1->getRoot()
             && parent->getArg(1)->getRoot() == n2->getRoot())
            || (parent->getArg(1)->getRoot() == n1->getRoot()
                && parent->getArg(0)->getRoot() == n2->getRoot())))
    {
      return true;
    }
  }
  return false;
}

bool SmtContext::isExtDiseq(ENode* n1, ENode* n2, uint32_t depth)
{
  ENode* r1 = n1->getRoot();
  ENode* r2 = n2->getRoot();
  if (r1 == r2)
  {
    return false;
  }
  if (r1->isInterpreted() && r2->isInterpreted())
  {
    return true;
  }
  if (isDiseq(n1, n2))
  {
    return true;
  }
  if (r1->getNumParents() > r2->getNumParents())
  {
    std::swap(n1, n2);
    std::swap(r1, r2);
  }
  if (depth == 0)
  {
    return false;
  }
  for (ENode* p1 : r1->getConstParents())
  {
    if (!isRelevant(p1) || p1->isEq() || !p1->isCgr())
    {
      continue;
    }
    TNode f = p1->getDecl();
    uint32_t numArgs = p1->getNumArgs();
    for (ENode* p2 : r2->getConstParents())
    {
      if (!isRelevant(p2) || p2->isEq() || !p2->isCgr())
      {
        continue;
      }
      if (p1->getRoot() != p2->getRoot() && p2->getDecl() == f
          && p2->getNumArgs() == numArgs)
      {
        uint32_t j = 0;
        for (; j < numArgs; ++j)
        {
          ENode* arg1 = p1->getArg(j)->getRoot();
          ENode* arg2 = p2->getArg(j)->getRoot();
          if (arg1 == arg2)
          {
            continue;
          }
          if ((arg1 == r1 || arg1 == r2) && (arg2 == r1 || arg2 == r2))
          {
            continue;
          }
          break;
        }
        if (j == numArgs && isExtDiseq(p1, p2, depth - 1))
        {
          return true;
        }
      }
    }
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
    addEq(entry.d_lhs, entry.d_rhs, entry.d_justification);
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
        addEq(getENode(lhs), getENode(rhs), EqJustification(l));
      }
      else
      {
        if (!addDiseq(getENode(lhs), getENode(rhs)) && !inconsistent())
        {
          Literal nEq = Literal(l.var(), true);
          setConflict(BJustification(mkJustification(EqPropagationJustification(
                          getENode(lhs), getENode(rhs)))),
                      nEq);
        }
      }
    }
    else if (d.isTheoryAtom())
    {
      Theory* th = getTheory(d.getTheory());
      Assert(th != nullptr);
      th->assignEh(v, val == L_TRUE);
    }
    else if (d.isQuantifier())
    {
      // Note that with relevancy lemmas a quantifier may be asserted to
      // false and marked relevant, which happens when a quantifier is part
      // of a conflict clause that becomes unit.
      Assert(isQuantifier(boolVar2Expr(v)));
      if (getAssignment(v) == L_TRUE)
      {
        // All universal quantifiers occur positively in the input, so
        // quantifiers assigned to false can be ignored.
        assignQuantifier(boolVar2Expr(v));
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

namespace {

/** Undoes setVarTheory. */
class SetVarTheoryTrail : public Trail
{
 public:
  SetVarTheoryTrail(SmtContext& ctx, BoolVar v) : d_ctx(ctx), d_var(v) {}
  void undo() override { d_ctx.getBdata(d_var).resetNotifyTheory(); }

 private:
  SmtContext& d_ctx;
  BoolVar d_var;
};

}  // namespace

void SmtContext::setVarTheory(BoolVar v, TheoryId tid)
{
  Assert(getVarTheory(v) == s_nullTheoryId);
  Assert(getInternLevel(v) <= getScopeLevel());
  if (getScopeLevel() > getInternLevel(v))
  {
    pushTrail(SetVarTheoryTrail(*this, v));
  }
  getBdata(v).setNotifyTheory(tid);
}

void SmtContext::propagateBoolVarENode(BoolVar v)
{
  // Propagate the truth value of v to the enode n associated with it: n is
  // merged with the true (false) enode when v is assigned true (false).
  Assert(getAssignment(v) != L_UNDEF);
  Assert(getBdata(v).isENode());
  LBool val = getAssignment(v);
  Assert(v < getNumBoolVars());
  ENode* n = boolVar2ENode(v);

  bool sign = val == L_FALSE;
  if (n->mergeTf())
  {
    addEq(n,
          sign ? d_falseENode : d_trueENode,
          EqJustification(Literal(v, sign)));
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
        assign(Literal(v2, sign),
               mkJustification(MpIffJustification(first, n)));
      }
      n = n->getNext();
    }
  }
}

void SmtContext::pushNewThDiseqs(ENode* r, TheoryVar v, Theory* th)
{
  // Traverse the disequalities of r's equivalence class and propagate them.
  if (!th->useDiseqs())
  {
    return;
  }
  TheoryId thId = th->getId();
  for (ENode* parent : r->getParents())
  {
    if (!parent->isEq())
    {
      continue;
    }
    BoolVar bv = getBoolVarOfId(parent->getOwnerId());
    if (getAssignment(bv) != L_FALSE)
    {
      continue;
    }
    ENode* lhs = parent->getArg(0);
    ENode* rhs = parent->getArg(1);
    Assert(lhs->getRoot() == r->getRoot() || rhs->getRoot() == r->getRoot());
    if (rhs->getRoot() == r->getRoot())
    {
      std::swap(lhs, rhs);
    }
    ENode* rhsRoot = rhs->getRoot();
    TheoryVar rhsVar = d_params.d_newCore2ThEq ? getClosestVar(rhs, thId)
                                               : rhsRoot->getThVar(thId);
    if (d_params.d_newCore2ThEq)
    {
      TheoryVar lv = getClosestVar(lhs, thId);
      if (lv != s_nullTheoryVar)
      {
        v = lv;
      }
    }
    // If v == rhsVar then the core detects the inconsistency itself.
    if (rhsVar != s_nullTheoryVar && v != rhsVar)
    {
      pushNewThDiseq(thId, v, rhsVar);
    }
  }
}

LBool SmtContext::getAssignment(ENode* n) const
{
  TNode owner = n->getExpr();
  if (!owner.getType().isBoolean())
  {
    return L_UNDEF;
  }
  if (n == d_falseENode)
  {
    return L_FALSE;
  }
  BoolVar v = getBoolVarOfId(owner.getId());
  return getAssignment(v);
}

void SmtContext::relevantEh(TNode n)
{
  if (bInternalized(n))
  {
    BoolVar v = getBoolVar(n);
    BoolVarData& d = getBdata(v);
    Assert(relevancy());
    // Quantifiers are only asserted when marked relevant; other atoms only
    // when the relevancy level is at least 2.
    if (d.isAtom() && (d.isQuantifier() || relevancyLvl() >= 2))
    {
      LBool val = getAssignment(v);
      if (val != L_UNDEF)
      {
        d_atomPropagationQueue.push_back(Literal(v, val == L_FALSE));
      }
    }
  }
  d_prop.getCaseSplitQueue().relevantEh(n);

  if (!isApp(n))
  {
    return;
  }
  if (eInternalized(n))
  {
    Assert(relevancy());
    d_qmanager->relevantEh(getENode(n));
  }

  Theory* propagatedTh = nullptr;
  TheoryId fid = familyIdOf(n);
  if (fid != theory::THEORY_BOOL && fid != theory::THEORY_BUILTIN)
  {
    Theory* th = getTheory(fid);
    if (th != nullptr)
    {
      th->relevantEh(n);
      // remember that relevantEh was already invoked for this theory
      propagatedTh = th;
    }
  }

  if (eInternalized(n))
  {
    ENode* e = getENode(n);
    const TheoryVarList* l = e->getThVarList();
    while (l != nullptr)
    {
      TheoryId thId = static_cast<TheoryId>(l->getId());
      Theory* th = getTheory(thId);
      // do not invoke relevantEh twice for the same n
      if (th != nullptr && th != propagatedTh)
      {
        th->relevantEh(n);
      }
      l = l->getNext();
    }
  }
}

void SmtContext::propagateRelevancy(size_t qhead)
{
  if (!relevancy())
  {
    return;
  }
  size_t sz = assignedLiterals().size();
  while (qhead < sz)
  {
    Literal l = assignedLiterals()[qhead];
    Assert(getAssignment(l) == L_TRUE);
    qhead++;
    BoolVar var = l.var();
    TNode n = boolVar2Expr(var);
    d_relevancyPropagator->assignEh(n, !l.sign());
  }
  d_relevancyPropagator->propagate();
}

bool SmtContext::propagateTheories()
{
  for (Theory* t : d_theorySet)
  {
    t->propagate();
    if (inconsistent())
    {
      return false;
    }
  }
  return true;
}

void SmtContext::propagateThEqs()
{
  for (size_t i = 0; i < d_thEqPropagationQueue.size() && !inconsistent(); ++i)
  {
    NewThEq curr = d_thEqPropagationQueue[i];
    Theory* th = getTheory(curr.d_thId);
    Assert(th != nullptr);
    th->newEqEh(curr.d_lhs, curr.d_rhs);
  }
  d_thEqPropagationQueue.clear();
}

void SmtContext::propagateThDiseqs()
{
  for (size_t i = 0; i < d_thDiseqPropagationQueue.size() && !inconsistent();
       ++i)
  {
    NewThEq curr = d_thDiseqPropagationQueue[i];
    Theory* th = getTheory(curr.d_thId);
    Assert(th != nullptr);
    th->newDiseqEh(curr.d_lhs, curr.d_rhs);
  }
  d_thDiseqPropagationQueue.clear();
}

bool SmtContext::hasPendingTheoryWork() const
{
  return d_relevancyPropagator->canPropagate()
         || !d_atomPropagationQueue.empty() || d_qmanager->canPropagate()
         || canTheoriesPropagate() || !d_eqPropagationQueue.empty()
         || !d_thEqPropagationQueue.empty()
         || !d_thDiseqPropagationQueue.empty();
}

bool SmtContext::theoryPropagate(size_t qhead)
{
  propagateRelevancy(qhead);
  if (inconsistent())
  {
    return false;
  }
  if (!propagateAtoms())
  {
    return false;
  }
  if (!propagateEqs())
  {
    return false;
  }
  propagateThEqs();
  propagateThDiseqs();
  if (inconsistent())
  {
    return false;
  }
  if (!propagateTheories())
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

bool SmtContext::canTheoriesPropagate() const
{
  for (Theory* t : d_theorySet)
  {
    if (t->canPropagate())
    {
      return true;
    }
  }
  return false;
}

void SmtContext::assignQuantifier(TNode q) { d_qmanager->assignEh(q); }

void SmtContext::notifyBoolVarDeleted(TNode n)
{
  if (isQuantifier(n))
  {
    d_qmanager->del(n);
  }
}

bool SmtContext::containsInstance(TNode q,
                                  size_t numBindings,
                                  ENode* const* bindings)
{
  return d_fingerprints.contains(
      q.getId(), static_cast<uint32_t>(q.getId()), numBindings, bindings);
}

bool SmtContext::addInstance(TNode q,
                             TNode pat,
                             size_t numBindings,
                             ENode* const* bindings,
                             uint32_t maxGeneration,
                             uint32_t minTopGeneration,
                             uint32_t maxTopGeneration,
                             std::vector<std::pair<ENode*, ENode*>>& usedENodes)
{
  return d_qmanager->addInstance(q,
                                 pat,
                                 numBindings,
                                 bindings,
                                 maxGeneration,
                                 minTopGeneration,
                                 maxTopGeneration,
                                 usedENodes);
}

uint32_t SmtContext::getGeneration(TNode q) const
{
  return d_qmanager->getGeneration(q);
}

bool SmtContext::internalizedQuantifiers() const
{
  return !d_qmanager->empty();
}

void SmtContext::pushTheoryScope()
{
  d_region.pushScope();
  getTrailStack().pushScope();
  d_justificationsLims.push_back(d_justifications.size());

  d_relevancyPropagator->push();
  d_qmanager->push();
  d_fingerprints.pushScope();

  for (Theory* t : d_theorySet)
  {
    t->pushScopeEh();
  }
}

void SmtContext::popTheoryScopeBegin(size_t numScopes)
{
  d_qmanager->pop(numScopes);
  d_relevancyPropagator->pop(numScopes);
  d_fingerprints.popScope(numScopes);
}

void SmtContext::popTheoryScopeEnd(size_t numScopes, uint32_t newLvl)
{
  Assert(d_justificationsLims.size() > newLvl);
  d_trailStack.popScope(numScopes);

  for (Theory* th : d_theorySet)
  {
    th->popScopeEh(numScopes);
  }
  delJustifications(d_justifications, d_justificationsLims[newLvl]);

  d_eqPropagationQueue.clear();
  d_thEqPropagationQueue.clear();
  d_region.popScope(numScopes);
  d_thDiseqPropagationQueue.clear();
  d_atomPropagationQueue.clear();
  d_justificationsLims.resize(newLvl);
}

void SmtContext::delJustifications(JustificationVector& justifications,
                                   size_t oldLim)
{
  Assert(oldLim <= justifications.size());
  size_t i = justifications.size();
  while (i != oldLim)
  {
    --i;
    Justification* js = justifications[i];
    js->delEh();
    if (!js->inRegion())
    {
      delete js;
    }
    else
    {
      // A region-allocated justification still needs its destructor run,
      // since some of them own vectors.
      js->~Justification();
    }
  }
  justifications.resize(oldLim);
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

void SmtContext::registerPlugin(Theory* th)
{
  if (getTheory(th->getFamilyId()) != nullptr)
  {
    // the context already has a theory for this family id
    delete th;
    return;
  }
  Assert(std::find(d_theorySet.begin(), d_theorySet.end(), th)
         == d_theorySet.end());
  d_theories[th->getFamilyId()] = th;
  th->init();
  d_theorySet.push_back(th);
  for (uint32_t i = 0; i < getScopeLevel(); ++i)
  {
    th->pushScopeEh();
  }
}

void SmtContext::assertFormula(TNode e)
{
  if (getCancelFlag())
  {
    return;
  }
  if (!isSearching())
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
    pushAssertion(
        d_env.getNodeManager()->mkNode(Kind::OR, e[0].negate(), e[1]));
    pushAssertion(d_env.getNodeManager()->mkNode(Kind::OR, Node(e[0]), e[2]));
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
          pushAssertion(
              d_env.getNodeManager()->mkNode(Kind::OR, Node(rest), arg));
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

void SmtContext::push()
{
  popToBaseLvl();
  setupContext(false);
  bool wasConsistent = !inconsistent();
  internalizeAssertions();
  d_prop.propagate();
  if (wasConsistent && inconsistent() && !d_prop.isAssertedInconsistent())
  {
    // the logical context became inconsistent during the user push
    bool resolved = d_prop.resolveConflict();
    Assert(!resolved);
    (void)resolved;
  }
  d_prop.pushScope();
  d_prop.pushBaseScope();
}

void SmtContext::pop(size_t numScopes)
{
  Assert(numScopes > 0);
  if (numScopes > getScopeLevel())
  {
    return;
  }
  popToBaseLvl();
  d_prop.popScope(numScopes);
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
    if (d_prop.getConflict() == s_nullBJustification)
    {
      assertedInconsistent();
    }
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

void SmtContext::internalizeInstance(TNode body, uint32_t generation)
{
  if (inconsistent())
  {
    return;
  }
  // The quantified variables are numbered by de Bruijn *level* (see
  // z3/ast.h), which Z3's relative de Bruijn indices make unnecessary there:
  // when Z3 instantiates a quantifier whose body holds another one, the inner
  // variables shift down on their own. Here they do not, so a nested
  // quantifier would arrive at the core with its variables still numbered
  // from the enclosing scope, while being a top-level quantifier with fewer
  // declarations -- and everything that indexes per-quantifier state by
  // variable level (the pattern compiler, the inverted path index, the
  // checker) would read the wrong slot. Renormalizing the instance restores
  // the invariant, and is idempotent on the parts that are already canonical.
  Node norm = d_normalizer.normalize(body);
  internalizeAssertion(norm, generation);
}

void SmtContext::assertedInconsistent()
{
  setConflict(BJustification::mkAxiom());
}

bool SmtContext::checkPreamble()
{
  d_stats.d_numChecks++;
  // The size of what the core is given, to be compared with the num-exprs
  // Z3 reports for the same query at verbosity 10.
  d_stats.d_numAssertedFormulas = d_assertedFormulas.size();
  std::unordered_set<TNode> seen;
  std::vector<TNode> todo(d_assertedFormulas.begin(), d_assertedFormulas.end());
  while (!todo.empty())
  {
    TNode n = todo.back();
    todo.pop_back();
    if (!seen.insert(n).second)
    {
      continue;
    }
    todo.insert(todo.end(), n.begin(), n.end());
  }
  d_stats.d_numAssertedExprs = seen.size();
  if (!d_env.getOptions().z3.z3DumpAssertions.empty())
  {
    dumpAssertions(d_env.getOptions().z3.z3DumpAssertions.c_str());
  }
  popToBaseLvl();
  d_prop.resetConflictResolution();
  return true;
}

void SmtContext::checkCandidateModel()
{
  // A development hook: hand the assigned relevant literals to a full cvc5
  // subsolver. If it reports unsat, the ported core accepted a state it
  // should have refuted, which means a theory of this port is too weak
  // rather than a quantifier instance being missing.
  std::vector<Node> lits;
  for (size_t i = 0; i < assignedLiterals().size(); ++i)
  {
    Literal l = assignedLiterals()[i];
    Node a = boolVar2Expr(l.var());
    if (a.isNull() || getBdata(l.var()).isQuantifier())
    {
      continue;
    }
    if (relevancy() && !isRelevantCore(l))
    {
      continue;
    }
    if (expr::hasClosure(a))
    {
      // A literal that still contains a quantifier would let the subsolver
      // instantiate it, which is exactly what this check has to exclude.
      continue;
    }
    lits.push_back(l.sign() ? a.notNode() : a);
  }
  std::unique_ptr<SolverEngine> sub;
  Options subOptions;
  subOptions.copyValues(d_env.getOptions());
  subOptions.write_z3().z3 = false;
  subOptions.write_smt().unsatAssumptions = true;
  smt::SetDefaults::disableChecking(subOptions);
  theory::SubsolverSetupInfo ssi(d_env, subOptions);
  theory::initializeSubsolver(d_env.getNodeManager(), sub, ssi);
  Result r = sub->checkSat(lits);
  std::stringstream ss;
  ss << "z3: candidate model over " << lits.size()
     << " relevant literals: cvc5 says " << r << "\n";
  if (r.getStatus() == Result::UNSAT)
  {
    for (const Node& c : sub->getUnsatAssumptions())
    {
      ss << "z3:   core: " << c << "\n";
    }
  }
  Warning() << ss.str();
}

void SmtContext::dumpCandidateModel(const char* path)
{
  // A development hook: write the state E-matching saturated in as a
  // self-contained benchmark -- the assigned relevant ground literals
  // together with every quantified assertion of the query. Running cvc5 on
  // it with --dump-instantiations answers the question this port keeps
  // asking: if the file is unsat, saturation was premature, and the
  // instantiations cvc5 prints are the ones E-matching failed to find.
  std::vector<Node> asserts;
  for (size_t i = 0; i < assignedLiterals().size(); ++i)
  {
    Literal l = assignedLiterals()[i];
    Node a = boolVar2Expr(l.var());
    if (a.isNull() || getBdata(l.var()).isQuantifier())
    {
      continue;
    }
    if (relevancy() && !isRelevantCore(l))
    {
      continue;
    }
    if (expr::hasClosure(a))
    {
      continue;
    }
    asserts.push_back(l.sign() ? a.notNode() : a);
  }
  for (const Node& a : d_assertedFormulas)
  {
    if (expr::hasClosure(a))
    {
      asserts.push_back(a);
    }
  }
  std::ofstream out(path);
  smt::PrintBenchmark pb(d_env.getNodeManager(), Printer::getPrinter(out));
  pb.printBenchmark(out, d_env.getLogicInfo().getLogicString(), {}, asserts);
}

void SmtContext::dumpAssertions(const char* path)
{
  // The formula this port's pipeline produces, so that Z3 can be run on the
  // identical input: comparing instantiation counts against Z3 on the
  // original file otherwise confuses a difference in search with a difference
  // in preprocessing.
  std::vector<Node> asserts(d_assertedFormulas.begin(),
                            d_assertedFormulas.end());
  std::ofstream out(path);
  smt::PrintBenchmark pb(d_env.getNodeManager(), Printer::getPrinter(out));
  pb.printBenchmark(out, d_env.getLogicInfo().getLogicString(), {}, asserts);
}

LBool SmtContext::checkFinalize(LBool r)
{
  if (d_params.d_qiProfile && d_qmanager != nullptr)
  {
    // Z3 prints these as each quantifier is deleted, so the only way to see
    // the whole table there is to let it finish; printing it once here is the
    // same information, in the same format, without that dependence.
    std::stringstream ss;
    d_qmanager->printStats(ss);
    Warning() << ss.str();
  }

  if (r == L_TRUE && getCancelFlag())
  {
    r = L_UNDEF;
  }
  std::string reason;
  if (r == L_TRUE && !d_theoryStatus.canConfirmModel(reason))
  {
    d_prop.setLastSearchFailure(THEORY);
    d_unknown = reason;
    r = L_UNDEF;
  }
  return r;
}

Cvc5Bridge& SmtContext::getCvc5Bridge()
{
  if (d_cvc5Bridge == nullptr)
  {
    d_cvc5Bridge.reset(new Cvc5Bridge(*this));
  }
  return *d_cvc5Bridge;
}

ConfigMode SmtContext::getConfigMode(bool useStaticFeatures) const
{
  if (!d_params.d_autoConfig)
  {
    return CFG_BASIC;
  }
  if (useStaticFeatures)
  {
    return CFG_AUTO;
  }
  return CFG_LOGIC;
}

void SmtContext::setupComponents()
{
  d_random.setSeed(d_params.d_randomSeed);
  d_dynAckManager.setup();

  if (!relevancy())
  {
    d_params.d_relevancyLemma = false;
  }

  for (Theory* th : d_theorySet)
  {
    th->setup();
  }
}

LBool SmtContext::setupAndCheck() { return check(); }

LBool SmtContext::check()
{
  if (!checkPreamble())
  {
    return L_UNDEF;
  }
  Assert(atBaseLevel());
  // The configuration happens on the first check only; passing autoConfig
  // here is what makes that first call collect the static features of the
  // input, as Z3 does when it is given a file rather than driven
  // incrementally.
  setupContext(d_params.d_autoConfig);
  popToBaseLvl();
  internalizeAssertions();
  // Z3 sets the search level in init_assumptions, which also creates the
  // scope the assumptions live in. This port does not support assumptions
  // (see the README), so the search level is simply the current scope.
  d_prop.setSearchLevel(getScopeLevel());
  Assert(getSearchLevel() == getBaseLevel());
  LBool r = d_prop.search();
  return checkFinalize(r);
}

void SmtContext::initSearchEh()
{
  for (Theory* th : d_theorySet)
  {
    th->initSearchEh();
  }
  d_qmanager->initSearchEh();
  d_dynAckManager.initSearchEh();
  d_finalCheckIdx = 0;
}

void SmtContext::notifyConflictResolved() { d_dynAckManager.propagateEh(); }

void SmtContext::clearPropagationQueues()
{
  d_atomPropagationQueue.clear();
  d_eqPropagationQueue.clear();
  d_thEqPropagationQueue.clear();
  d_thDiseqPropagationQueue.clear();
}

void SmtContext::restartEh()
{
  for (Theory* th : d_theorySet)
  {
    if (!inconsistent())
    {
      th->restartEh();
    }
  }

  if (!inconsistent())
  {
    d_qmanager->restartEh();
  }
}

QuantifierManager::CheckModelResult SmtContext::checkModel()
{
  if (!d_qmanager->hasQuantifiers())
  {
    return QuantifierManager::SAT;
  }
  const options::HolderZ3& z3opts = d_env.getOptions().z3;
  if (!z3opts.z3DumpSaturated.empty())
  {
    dumpCandidateModel(z3opts.z3DumpSaturated.c_str());
  }
  if (z3opts.z3CheckSaturated)
  {
    checkCandidateModel();
  }
  return d_qmanager->checkModel();
}

FinalCheckStatus SmtContext::finalCheck(Failure& failure)
{
  failure = OK;
  d_stats.d_numFinalChecks++;
  Trace("z3-events") << "FINALCHECK " << d_stats.d_numFinalChecks << std::endl;

  FinalCheckStatus ok = d_qmanager->finalCheckEh(false);
  if (ok != FC_DONE)
  {
    return ok;
  }

  size_t oldIdx = d_finalCheckIdx;
  size_t numTh = d_theorySet.size();
  size_t range = numTh + 1;
  size_t level = 1;
  size_t maxLevel = 1;
  FinalCheckStatus result = FC_DONE;
  Failure f = OK;

  while (true)
  {
    FinalCheckStatus st;
    if (d_finalCheckIdx < numTh)
    {
      Theory* th = d_theorySet[d_finalCheckIdx];
      st = th->finalCheckEh(level);
      maxLevel = std::max(maxLevel, th->numFinalCheckLevels());
      if (getCancelFlag())
      {
        f = CANCELED;
        st = FC_GIVEUP;
      }
      else if (st == FC_GIVEUP)
      {
        f = THEORY;
      }
    }
    else
    {
      st = d_qmanager->finalCheckEh(true);
    }

    d_finalCheckIdx = (d_finalCheckIdx + 1) % range;

    switch (st)
    {
      case FC_DONE: break;
      case FC_GIVEUP: result = FC_GIVEUP; break;
      case FC_CONTINUE: return FC_CONTINUE;
    }
    if (d_finalCheckIdx == oldIdx)
    {
      if (level >= maxLevel || result == FC_DONE || result == FC_CONTINUE
          || canPropagate())
      {
        break;
      }
      ++level;
      // Re-evaluate at the higher level: clear the give-up state accumulated
      // at the lower levels, so that a level that succeeds is not masked by a
      // previous FC_GIVEUP.
      result = FC_DONE;
      f = OK;
    }
  }

  if (canPropagate())
  {
    return FC_CONTINUE;
  }

  if (result == FC_GIVEUP && f != OK)
  {
    failure = f;
  }
  return result;
}

void SmtContext::recordRelevancy(size_t n, const Literal* lits)
{
  // A literal may have been marked relevant inside the scope that conflict
  // resolution pops, in which case it is no longer relevant afterwards. That
  // would make E-matching miss relevant triggers and lose completeness, so
  // the relevancy is recorded here and restored after the pop.
  d_relevantConflictLiterals.clear();
  for (size_t i = 0; i < n; ++i)
  {
    d_relevantConflictLiterals.push_back(isRelevant(lits[i]));
  }
}

void SmtContext::restoreRelevancy(size_t n, const Literal* lits)
{
  for (size_t i = 0; i < n; ++i)
  {
    if (d_relevantConflictLiterals[i] && !isRelevant(lits[i]))
    {
      markAsRelevant(lits[i]);
    }
  }
}

bool SmtContext::assumeEq(ENode* lhs, ENode* rhs)
{
  if (lhs->getRoot() == rhs->getRoot())
  {
    // it is not necessary to assume the equality
    return false;
  }
  Node eq = mkEqAtom(lhs->getExpr(), rhs->getExpr());
  if (isFalseNode(eq))
  {
    return false;
  }
  bool r = false;
  if (!bInternalized(eq))
  {
    // internalizeFormulaCore rather than internalize, so that the
    // try-true-first flag is set before Theory::internalizeEqEh runs: the
    // theories use that information to also mark their auxiliary atoms.
    if (eq.getKind() == Kind::EQUAL)
    {
      internalizeFormulaCore(eq, true);
      BoolVar v = getBoolVar(eq);
      BoolVarData& d = getBdata(v);
      d.setEqFlag();
      setTrueFirstFlag(v);
      Theory* th = getTheory(theory::Theory::theoryOf(eq[0].getType()));
      if (th != nullptr)
      {
        th->internalizeEqEh(eq, v);
      }
    }
    else
    {
      internalize(eq, true);
    }
    r = true;
    d_stats.d_numInterfaceEqs++;
  }
  BoolVar v = getBoolVar(eq);
  BoolVarData& d = getBdata(v);
  if (!d.tryTrueFirst())
  {
    setTrueFirstFlag(v);
    r = true;
  }
  if (getAssignment(v) == L_UNDEF)
  {
    r = true;
  }
  if (relevancy() && !isRelevant(eq))
  {
    markAsRelevant(eq);
    r = true;
  }
  return r;
}

bool SmtContext::isShared(ENode* n) const
{
  n = n->getRoot();
  switch (n->isShared())
  {
    case L_TRUE: return true;
    case L_FALSE: return false;
    default: break;
  }

  size_t numThVars = n->getNumThVars();
  if (n->getExpr().getKind() == Kind::ITE)
  {
    n->setIsShared(L_TRUE);
    return true;
  }
  switch (numThVars)
  {
    case 0: return false;
    case 1:
    {
      if (d_qmanager->isShared(n))
      {
        return true;
      }

      // The node is shared if its equivalence class has a parent application
      // belonging to another theory.
      const TheoryVarList* l = n->getThVarList();
      TheoryId thId = static_cast<TheoryId>(l->getId());

      for (ENode* parent : n->getConstParents())
      {
        TheoryId fid = parent->getFamilyId();
        if (fid != thId && fid != theory::THEORY_BOOL
            && fid != theory::THEORY_BUILTIN)
        {
          if (isBetaRedex(parent, n))
          {
            continue;
          }
          n->setIsShared(L_TRUE);
          return true;
        }
      }

      // Some theories implement families of theories (arrays and tuples, for
      // example), in which case the theory itself decides.
      bool r = getTheory(thId)->isShared(l->getVar());
      n->setIsShared(toLBool(r));
      return r;
    }
    default: return true;
  }
}

bool SmtContext::isBetaRedex(ENode* p, ENode* n) const
{
  Theory* th = getTheory(p->getFamilyId());
  return th != nullptr && th->isBetaRedex(p, n);
}

bool SmtContext::getValue(ENode* n, Node& value)
{
  Theory* th = getTheory(theory::Theory::theoryOf(n->getSort()));
  if (th == nullptr)
  {
    return false;
  }
  return th->getValue(n, value);
}

std::ostream& SmtContext::printLiteral(std::ostream& out, Literal l) const
{
  if (l == s_trueLiteral)
  {
    return out << "true";
  }
  if (l == s_falseLiteral)
  {
    return out << "false";
  }
  if (l == s_nullLiteral)
  {
    return out << "null";
  }
  if (l.sign())
  {
    out << "(not ";
  }
  out << boolVar2Expr(l.var());
  if (l.sign())
  {
    out << ")";
  }
  return out;
}

std::ostream& SmtContext::printLiterals(std::ostream& out,
                                        size_t numLits,
                                        const Literal* lits) const
{
  out << "{";
  for (size_t i = 0; i < numLits; ++i)
  {
    if (i > 0)
    {
      out << " or ";
    }
    printLiteral(out, lits[i]);
  }
  return out << "}";
}

std::ostream& SmtContext::print(std::ostream& out, BJustification j) const
{
  out << j.getKind();
  switch (j.getKind())
  {
    case BJustification::CLAUSE:
      if (j.getClause() != nullptr)
      {
        j.getClause()->print(out << " ", d_prop.getBoolVar2ExprMap());
      }
      break;
    case BJustification::BIN_CLAUSE:
      printLiteral(out << " ", j.getLiteral());
      break;
    case BJustification::JUSTIFICATION:
      out << " " << j.getJustification()->getName();
      break;
    default: break;
  }
  return out;
}

void SmtContext::print(std::ostream& out) const
{
  out << "z3::context\n";
  out << "scope level: " << getScopeLevel()
      << ", base level: " << getBaseLevel()
      << ", search level: " << getSearchLevel() << "\n";
  out << "num bool vars: " << getNumBoolVars()
      << ", num enodes: " << d_enodes.size()
      << ", num aux clauses: " << d_prop.getNumAuxClauses()
      << ", num lemmas: " << getLemmas().size() << "\n";
}

void SmtContext::printStatistics(std::ostream& out) const
{
  d_stats.print(out);
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
  add("z3::conflicts", d_stats.d_numConflicts);
  add("z3::satConflicts", d_stats.d_numSatConflicts);
  add("z3::decisions", d_stats.d_numDecisions);
  add("z3::addEq", d_stats.d_numAddEq);
  add("z3::restarts", d_stats.d_numRestarts);
  add("z3::finalChecks", d_stats.d_numFinalChecks);
  add("z3::assertedFormulas", d_stats.d_numAssertedFormulas);
  add("z3::assertedExprs", d_stats.d_numAssertedExprs);
  add("z3::mkBoolVar", d_stats.d_numMkBoolVar);
  add("z3::delBoolVar", d_stats.d_numDelBoolVar);
  add("z3::mkENode", d_stats.d_numMkENode);
  add("z3::delENode", d_stats.d_numDelENode);
  add("z3::mkClause", d_stats.d_numMkClause);
  add("z3::delClause", d_stats.d_numDelClause);
  add("z3::mkBinClause", d_stats.d_numMkBinClause);
  add("z3::mkLits", d_stats.d_numMkLits);
  add("z3::dynAck", d_stats.d_numDynAck);
  add("z3::arithNlFallbacks", d_stats.d_numArithNlFallbacks);
  add("z3::arithNlFallbackConflicts", d_stats.d_numArithNlFallbackConflicts);
  add("z3::interfaceEqs", d_stats.d_numInterfaceEqs);
  add("z3::propagatedEqs", d_stats.d_numPropagatedEqs);
  add("z3::separatedEqs", d_stats.d_numSeparatedEqs);
  add("z3::sharedGroups", d_stats.d_numSharedGroups);
  add("z3::coincidingShared", d_stats.d_numCoincidingShared);
  add("z3::maxGeneration", d_stats.d_maxGeneration);
  add("z3::minimizedLits", d_stats.d_numMinimizedLits);
  add("z3::learnedLits", d_stats.d_numLearnedLits);
  add("z3::checks", d_stats.d_numChecks);
  add("z3::simplifications", d_stats.d_numSimplifications);
  add("z3::assignments", d_stats.d_numAssignments);
  add("z3::instances", d_stats.d_numInstances);
  add("z3::lazyInstances", d_stats.d_numLazyInstances);
  add("z3::instancesCheckerSat", d_stats.d_numInstancesCheckerSat);
  add("z3::instancesSimplifyTrue", d_stats.d_numInstancesSimplifyTrue);
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
  add("z3::dtOccursCheck", d_stats.d_numDtOccursCheck);
  add("z3::dtSplits", d_stats.d_numDtSplits);
  add("z3::dtConstructorAx", d_stats.d_numDtConstructorAx);
  add("z3::dtAccessorAx", d_stats.d_numDtAccessorAx);
  add("z3::dtUpdateFieldAx", d_stats.d_numDtUpdateFieldAx);
  add("z3::bridgeAssumptions", d_stats.d_bridgeAssumptions);
  add("z3::bridgeAsserted", d_stats.d_bridgeAsserted);
  add("z3::bridgeTimeMs", d_stats.d_bridgeTimeMs);
  add("z3::bridgeChecks", d_stats.d_numBridgeChecks);
  add("z3::bridgeConflicts", d_stats.d_numBridgeConflicts);
}

std::ostream& SmtContext::printLastFailure(std::ostream& out) const
{
  return out << getLastSearchFailure();
}
}  // namespace z3
}  // namespace cvc5::internal

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The E-graph of the ported Z3 core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * the E-graph part of file src/smt/smt_context.cpp, and recast in cvc5
 * style.
 */

#include "z3/quantifiers/egraph.h"

#include <algorithm>

#include "theory/uf/equality_engine.h"
#include "z3/quantifiers/smt_context.h"

namespace cvc5::internal {
namespace z3 {

EGraph::EGraph(Env& env, SmtContext& ctx, TrailStack& trail, Statistics& stats)
    : EnvObj(env),
      d_ctx(ctx),
      d_trailStack(trail),
      d_stats(stats),
      d_mkENodeTrail(*this),
      d_masterEe(nullptr),
      d_masterTerm(context()),
      d_masterIdx(context(), 0)
{
}

ENode* EGraph::mkENode(TNode n,
                       uint32_t generation,
                       bool suppressArgs,
                       bool mergeTf,
                       bool cgcEnabled,
                       uint32_t scopeLvl)
{
  Assert(!eInternalized(n));
  size_t id = n.getId();
  ENode* e = ENode::mk(d_trailStack,
                       d_app2ENode,
                       n,
                       generation,
                       suppressArgs,
                       mergeTf,
                       scopeLvl,
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
      // see SmtContext::mkENode
      e->d_cg = e;
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

uint32_t EGraph::getDeclId(TNode decl)
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

uint32_t EGraph::getDeclIdOption(TNode decl) const
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
  AddEqTrail(EGraph& eg, ENode* r1, size_t r2NumParents)
      : d_eg(eg), d_r1(r1), d_r2NumParents(r2NumParents)
  {
  }
  void undo() override;

 private:
  EGraph& d_eg;
  ENode* d_r1;
  size_t d_r2NumParents;
};

}  // namespace

void EGraph::addEq(ENode* n1, ENode* n2)
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
    d_ctx.getPropCore().setConflict();
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

  size_t r2NumParents = r2->getNumParents();

  // relevancy spreads to the class, and the quantifier manager is notified
  d_ctx.notifyMerge(r1, r2);

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
  d_trailStack.push(AddEqTrail(*this, r1, r2NumParents));

  if (n2->isBool())
  {
    d_ctx.propagateBoolENodeAssignment(r1, r2, n1, n2);
  }

  // merge the equivalence classes
  std::swap(r1->d_next, r2->d_next);

  // update the class size
  r2->d_classSize += r1->d_classSize;
}

namespace {

void AddEqTrail::undo() { d_eg.undoAddEq(d_r1, d_r2NumParents); }

}  // namespace

void EGraph::removeParentsFromCgTable(ENode* r1)
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

void EGraph::setGenerationSticky(ENode* n, uint32_t generation)
{
  Assert(n->usesCgTable());
  Assert(!n->isEq());
  // The caller is responsible for this; sticky updates are too expensive to
  // spend on no-ops.
  Assert(generation < getGeneration(n));

  setGeneration(n, generation);
  d_stickyGenerationUpdates[n] = generation;
}

void EGraph::reinsertParentsIntoCgTable(ENode* r1, ENode* r2)
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
        BoolVar v = d_ctx.getPropCore().getBoolVarOfId(exprId);
        SatValue val = d_ctx.getPropCore().getAssignment(v);
        if (val != SAT_VALUE_TRUE)
        {
          d_ctx.getPropCore().assign(Literal(v));
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

void EGraph::undoAddEq(ENode* r1, size_t r2NumParents)
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

void EGraph::undoMergeCgcGenerations(ENode* e1,
                                         uint32_t e1Generation,
                                         ENode* e2,
                                         uint32_t e2Generation)
{
  setGeneration(e1, e1Generation);
  setGeneration(e2, e2Generation);
  applyStickyUpdates(e1, e1Generation, e2, e2Generation);
}

void EGraph::applyStickyUpdates(ENode* e1,
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

ENode* EGraph::getENodeEqTo(TNode decl,
                                bool commutative,
                                size_t numArgs,
                                ENode* const* args)
{
  ENode* tmp = d_tmpENode.set(decl, commutative, numArgs, args);
  return d_cgTable.find(tmp);
}

void EGraph::setGeneration(ENode* e, uint32_t generation)
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

bool EGraph::propagateEqs()
{
  size_t i = 0;
  for (; i < d_eqPropagationQueue.size() && !d_ctx.getCancelFlag(); ++i)
  {
    NewEq& entry = d_eqPropagationQueue[i];
    addEq(entry.d_lhs, entry.d_rhs);
    if (d_ctx.getPropCore().inconsistent())
    {
      d_eqPropagationQueue.clear();
      return false;
    }
  }
  d_eqPropagationQueue.clear();
  return true;
}

namespace {

/** Undoes a congruence class generation merge. */
class MergeCgcGenerationsTrail : public Trail
{
 public:
  MergeCgcGenerationsTrail(EGraph& eg,
                           ENode* e1,
                           uint32_t e1Generation,
                           ENode* e2,
                           uint32_t e2Generation)
      : d_eg(eg),
        d_e1(e1),
        d_e1Generation(e1Generation),
        d_e2(e2),
        d_e2Generation(e2Generation)
  {
  }

  void undo() override
  {
    d_eg.undoMergeCgcGenerations(d_e1, d_e1Generation, d_e2, d_e2Generation);
  }

 private:
  EGraph& d_eg;
  ENode* d_e1;
  uint32_t d_e1Generation;
  ENode* d_e2;
  uint32_t d_e2Generation;
};

}  // namespace

void EGraph::mergeCgcGenerations(ENode* e1,
                                     uint32_t e1Generation,
                                     ENode* e2)
{
  Assert(e2->isCgr());
  Assert(!d_cgTable.containsPtr(e1));
  Assert(d_cgTable.containsPtr(e2));

  // Push the trail even for a no-op, otherwise e1's generation could not be
  // restored when the merge is undone.
  d_trailStack.push(
      MergeCgcGenerationsTrail(*this, e1, e1Generation, e2, e2->d_generation));

  if (e1Generation >= e2->d_generation)
  {
    return;  // a no-op
  }

  e2->d_generation = e1Generation;
}

void EGraph::undoMkENode()
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

Node EGraph::masterTermOf(TNode rep) const
{
  auto it = d_masterTerm.find(rep);
  return it == d_masterTerm.end() ? Node::null() : it->second;
}

void EGraph::mergeMasterTerms(TNode a, TNode b)
{
  if (a == b || !eInternalized(a) || !eInternalized(b))
  {
    return;
  }
  pushEq(getENode(a), getENode(b));
  d_stats.d_numShadowMerges++;
}

void EGraph::applyMasterMerges()
{
  if (d_masterEe == nullptr)
  {
    return;
  }
  if (d_ctx.getPropCore().inconsistent())
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

void EGraph::notifyMasterMerge(TNode t1, TNode t2)
{
  // The Boolean classes are those of the atoms, whose values reach the core
  // as facts.
  if (!t1.getType().isBoolean())
  {
    d_pendingMerges.emplace_back(t1, t2);
  }
}

}  // namespace z3
}  // namespace cvc5::internal

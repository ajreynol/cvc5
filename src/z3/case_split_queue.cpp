/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The case split queue.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_case_split_queue.cpp, and recast in cvc5 style.
 *
 * Not ported: Z3's CS_RELEVANCY_GOAL queue, which tracks the "current goal"
 * through Z3 label literals. cvc5's input language has no counterpart to
 * labels, so the strategy has nothing to key on; selecting it is reported as
 * an error rather than silently behaving like plain relevancy.
 */

#include "z3/case_split_queue.h"

#include <unordered_map>
#include <unordered_set>

#include "base/output.h"
#include "z3/enode.h"
#include "z3/smt_context.h"
#include "z3/util/heap.h"
#include "z3/util/random_gen.h"

namespace cvc5::internal {
namespace z3 {

namespace {

using TheoryVarPriorityMap = std::unordered_map<BoolVar, double>;

/** Orders Boolean variables by decreasing activity. */
struct BoolVarActLt
{
  const std::vector<double>& d_activity;
  BoolVarActLt(const std::vector<double>& a) : d_activity(a) {}
  bool operator()(int v1, int v2) const
  {
    return d_activity[v1] > d_activity[v2];
  }
};

using BoolVarActQueue = Heap<BoolVarActLt>;

/** Orders Boolean variables by decreasing theory priority plus activity. */
struct TheoryAwareActLt
{
  const std::vector<double>& d_activity;
  const TheoryVarPriorityMap& d_theoryVarPriority;
  TheoryAwareActLt(const std::vector<double>& act,
                   const TheoryVarPriorityMap& a)
      : d_activity(act), d_theoryVarPriority(a)
  {
  }
  bool operator()(int v1, int v2) const
  {
    double pv1 = 0.0;
    double pv2 = 0.0;
    auto it1 = d_theoryVarPriority.find(static_cast<BoolVar>(v1));
    if (it1 != d_theoryVarPriority.end())
    {
      pv1 = it1->second;
    }
    auto it2 = d_theoryVarPriority.find(static_cast<BoolVar>(v2));
    if (it2 != d_theoryVarPriority.end())
    {
      pv2 = it2->second;
    }
    // add clause activity
    pv1 += d_activity[v1];
    pv2 += d_activity[v2];
    return pv1 > pv2;
  }
};

using TheoryAwareActQueue = Heap<TheoryAwareActLt>;

/** The case split queue based on activity and random splits. */
class ActCaseSplitQueue : public CaseSplitQueue
{
 public:
  ActCaseSplitQueue(SmtContext& ctx, Params& p)
      : d_context(ctx),
        d_params(p),
        d_queue(1024, BoolVarActLt(ctx.getActivityVector()))
  {
  }

  void activityIncreasedEh(BoolVar v) override
  {
    if (d_queue.contains(v))
    {
      d_queue.decreased(v);
    }
  }

  void activityDecreasedEh(BoolVar v) override
  {
    if (d_queue.contains(v))
    {
      d_queue.increased(v);
    }
  }

  void mkVarEh(BoolVar v) override
  {
    d_queue.reserve(v + 1);
    Assert(!d_queue.contains(v));
    d_queue.insert(v);
  }

  void delVarEh(BoolVar v) override
  {
    if (d_queue.contains(v))
    {
      d_queue.erase(v);
    }
  }

  void unassignVarEh(BoolVar v) override
  {
    if (!d_queue.contains(v))
    {
      d_queue.insert(v);
    }
  }

  void relevantEh(TNode n) override {}

  void initSearchEh() override {}

  void endSearchEh() override {}

  void reset() override { d_queue.reset(); }

  void pushScope() override {}

  void popScope(size_t numScopes) override {}

  void nextCaseSplit(BoolVar& next, LBool& phase) override
  {
    phase = L_UNDEF;

    if (d_context.getRandomValue()
        < static_cast<int>(d_params.d_randomVarFreq * RandomGen::maxValue()))
    {
      next = d_context.getRandomValue() % d_context.getNumBInternalized();
      if (d_context.getAssignment(next) == L_UNDEF)
      {
        return;
      }
    }

    while (!d_queue.empty())
    {
      next = d_queue.eraseMin();
      if (d_context.getAssignment(next) == L_UNDEF)
      {
        return;
      }
    }

    next = s_nullBoolVar;
  }

  void print(std::ostream& out) override
  {
    bool first = true;
    for (int v : d_queue)
    {
      if (d_context.getAssignment(static_cast<BoolVar>(v)) == L_UNDEF)
      {
        if (first)
        {
          out << "remaining case-splits:\n";
          first = false;
        }
        out << "#" << d_context.boolVar2Expr(static_cast<BoolVar>(v)).getId()
            << " ";
      }
    }
    if (!first)
    {
      out << "\n";
    }
  }

 protected:
  SmtContext& d_context;
  Params& d_params;
  BoolVarActQueue d_queue;
};

/**
 * Like ActCaseSplitQueue, but splits created during the search are delayed
 * until the main queue is exhausted. This is Z3's default.
 */
class DactCaseSplitQueue : public ActCaseSplitQueue
{
 public:
  DactCaseSplitQueue(SmtContext& ctx, Params& p)
      : ActCaseSplitQueue(ctx, p),
        d_delayedQueue(1024, BoolVarActLt(ctx.getActivityVector()))
  {
  }

  void activityIncreasedEh(BoolVar v) override
  {
    ActCaseSplitQueue::activityIncreasedEh(v);
    if (d_queue.contains(v))
    {
      d_queue.decreased(v);
    }
    if (d_delayedQueue.contains(v))
    {
      d_delayedQueue.decreased(v);
    }
  }

  void activityDecreasedEh(BoolVar v) override
  {
    ActCaseSplitQueue::activityDecreasedEh(v);
    if (d_queue.contains(v))
    {
      d_queue.increased(v);
    }
    if (d_delayedQueue.contains(v))
    {
      d_delayedQueue.increased(v);
    }
  }

  void mkVarEh(BoolVar v) override
  {
    d_queue.reserve(v + 1);
    d_delayedQueue.reserve(v + 1);
    Assert(!d_delayedQueue.contains(v));
    Assert(!d_queue.contains(v));
    if (d_context.isSearching())
    {
      d_delayedQueue.insert(v);
    }
    else
    {
      d_queue.insert(v);
    }
  }

  void delVarEh(BoolVar v) override
  {
    ActCaseSplitQueue::delVarEh(v);
    if (d_delayedQueue.contains(v))
    {
      d_delayedQueue.erase(v);
    }
  }

  void reset() override
  {
    ActCaseSplitQueue::reset();
    d_delayedQueue.reset();
  }

  void nextCaseSplit(BoolVar& next, LBool& phase) override
  {
    ActCaseSplitQueue::nextCaseSplit(next, phase);
    if (next != s_nullBoolVar)
    {
      return;
    }

    d_queue.swap(d_delayedQueue);
    Assert(d_delayedQueue.empty());

    while (!d_queue.empty())
    {
      next = d_queue.eraseMin();
      if (d_context.getAssignment(next) == L_UNDEF)
      {
        return;
      }
    }

    next = s_nullBoolVar;
  }

 private:
  BoolVarActQueue d_delayedQueue;
};

/** Like ActCaseSplitQueue, but the activity survives variable deletion. */
class CactCaseSplitQueue : public ActCaseSplitQueue
{
 public:
  CactCaseSplitQueue(SmtContext& ctx, Params& p) : ActCaseSplitQueue(ctx, p) {}

  void mkVarEh(BoolVar v) override
  {
    TNode n = d_context.boolVar2Expr(v);
    if (!n.isNull())
    {
      auto it = d_cache.find(n);
      if (it != d_cache.end())
      {
        d_context.setActivity(v, it->second);
      }
    }
    ActCaseSplitQueue::mkVarEh(v);
  }

  void delVarEh(BoolVar v) override
  {
    if (d_context.isSearching())
    {
      double act = d_context.getActivity(v);
      if (act > 0.0)
      {
        TNode n = d_context.boolVar2Expr(v);
        if (!n.isNull())
        {
          d_cache[n] = act;
        }
      }
    }
    ActCaseSplitQueue::delVarEh(v);
  }

  void initSearchEh() override { d_cache.clear(); }

  void reset() override { initSearchEh(); }

 private:
  std::unordered_map<Node, double> d_cache;
};

/**
 * Find a child of parent that is assigned to val, or else select an
 * unassigned child to branch on. The choice among unassigned children follows
 * d_relCaseSplitOrder: 0 takes the first, 1 picks one at random.
 */
bool hasChildAssignedTo(SmtContext& ctx,
                        TNode parent,
                        LBool val,
                        TNode& undefChild,
                        uint32_t order)
{
  std::vector<Node> undefChildren;
  bool foundUndef = false;
  size_t numArgs = parent.getNumChildren();
  for (size_t i = 0; i < numArgs; ++i)
  {
    TNode arg = parent[i];
    LBool argVal = ctx.getAssignment(arg);
    if (argVal == val)
    {
      return true;
    }
    if (foundUndef && order == 0)
    {
      continue;
    }
    if (argVal == L_UNDEF)
    {
      if (order == 1)
      {
        undefChildren.push_back(arg);
      }
      else
      {
        undefChild = arg;
      }
      foundUndef = true;
    }
  }
  if (order == 1)
  {
    if (undefChildren.size() == 1)
    {
      undefChild = undefChildren[0];
    }
    else if (undefChildren.size() > 1)
    {
      undefChild =
          undefChildren[ctx.getRandomValue() % undefChildren.size()];
    }
  }
  return false;
}

/**
 * The case split queue based on relevancy propagation.
 *
 * Candidates are enqueued as they become relevant, and the queue walks them in
 * that order: branching follows the shape of the formula that the current
 * assignment still has to justify, rather than activity.
 */
class RelCaseSplitQueue : public CaseSplitQueue
{
  struct Scope
  {
    size_t d_queueTrail;
    size_t d_headOld;
    size_t d_queue2Trail;
    size_t d_head2Old;
  };

 public:
  RelCaseSplitQueue(SmtContext& ctx, Params& p)
      : d_context(ctx),
        d_params(p),
        d_head(0),
        d_bsNumBoolVars(UINT32_MAX),
        d_head2(0)
  {
  }

  void activityIncreasedEh(BoolVar v) override {}

  void activityDecreasedEh(BoolVar v) override {}

  void mkVarEh(BoolVar v) override {}

  void delVarEh(BoolVar v) override {}

  void unassignVarEh(BoolVar v) override {}

  void relevantEh(TNode n) override
  {
    if (!n.getType().isBoolean())
    {
      return;
    }
    bool isOr = n.getKind() == Kind::OR;
    bool intern = d_context.bInternalized(n);
    if (!intern && !isOr)
    {
      return;
    }
    BoolVar var = s_nullBoolVar;
    if (intern)
    {
      var = d_context.getBoolVar(n);
      Assert(var != s_nullBoolVar);
      bool isAnd = n.getKind() == Kind::AND;
      LBool val = d_context.getAssignment(var);
      if (!(val == L_UNDEF ||              // n was not assigned yet
            (isOr && val == L_TRUE) ||     // need to justify a child
            (isAnd && val == L_FALSE)))    // need to justify a child
      {
        return;
      }
    }
    if (!intern && d_context.isSearching())
    {
      Assert(isOr);
      d_queue2.push_back(n);
      return;
    }
    if (var < d_bsNumBoolVars)
    {
      d_queue.push_back(n);
    }
    else
    {
      d_queue2.push_back(n);
    }
  }

  void initSearchEh() override
  {
    d_bsNumBoolVars = static_cast<BoolVar>(d_context.getNumBoolVars());
  }

  void endSearchEh() override { d_bsNumBoolVars = UINT32_MAX; }

  void reset() override
  {
    d_queue.clear();
    d_head = 0;
    d_queue2.clear();
    d_head2 = 0;
    d_scopes.clear();
  }

  void pushScope() override
  {
    d_scopes.push_back(
        Scope{d_queue.size(), d_head, d_queue2.size(), d_head2});
  }

  void popScope(size_t numScopes) override
  {
    Assert(numScopes <= d_scopes.size());
    size_t newLvl = d_scopes.size() - numScopes;
    Scope& s = d_scopes[newLvl];
    d_queue.resize(s.d_queueTrail);
    d_head = s.d_headOld;
    d_queue2.resize(s.d_queue2Trail);
    d_head2 = s.d_head2Old;
    d_scopes.resize(newLvl);
    Assert(d_head <= d_queue.size());
  }

  void nextCaseSplit(BoolVar& next, LBool& phase) override
  {
    nextCaseSplitCore(d_queue, d_head, next, phase);
    if (next == s_nullBoolVar)
    {
      nextCaseSplitCore(d_queue2, d_head2, next, phase);
    }
    // Force the negative phase if next is an equality already known to be
    // disequal in the logical context.
    if (d_params.d_lookaheadDiseq && next != s_nullBoolVar && phase != L_FALSE
        && d_context.hasENode(next))
    {
      ENode* n = d_context.boolVar2ENode(next);
      if (n->isEq())
      {
        ENode* lhs = n->getArg(0);
        ENode* rhs = n->getArg(1);
        if (d_context.isExtDiseq(lhs, rhs, 2))
        {
          phase = L_FALSE;
        }
      }
    }
  }

  void print(std::ostream& out) override
  {
    if (d_queue.empty() && d_queue2.empty())
    {
      return;
    }
    out << "case-splits:\n";
    printCore(out, d_queue, d_head, 1);
    printCore(out, d_queue2, d_head2, 2);
  }

 private:
  void nextCaseSplitCore(std::vector<Node>& queue,
                         size_t& head,
                         BoolVar& next,
                         LBool& phase)
  {
    phase = L_UNDEF;
    size_t sz = queue.size();
    for (; head < sz; ++head)
    {
      TNode curr = queue[head];
      bool isOr = curr.getKind() == Kind::OR;
      bool isAnd = curr.getKind() == Kind::AND;
      bool intern = d_context.bInternalized(curr);
      Assert(intern || isOr);
      LBool val = L_UNDEF;
      if (intern)
      {
        next = d_context.getBoolVar(curr);
        val = d_context.getAssignment(next);
      }
      else
      {
        Assert(isOr);  // a top level clause
        val = L_TRUE;
      }
      if ((isOr && val == L_TRUE) || (isAnd && val == L_FALSE))
      {
        TNode undefChild;
        if (!hasChildAssignedTo(
                d_context, curr, val, undefChild, d_params.d_relCaseSplitOrder))
        {
          Literal l = d_context.getLiteral(undefChild);
          next = l.var();
          phase = l.sign() ? L_FALSE : L_TRUE;
          return;
        }
      }
      else if (val == L_UNDEF)
      {
        Assert(intern && d_context.getBoolVar(curr) == next);
        phase = L_UNDEF;
        return;
      }
    }
    next = s_nullBoolVar;
  }

  void printCore(std::ostream& out,
                 std::vector<Node>& queue,
                 size_t head,
                 size_t idx)
  {
    if (queue.empty())
    {
      return;
    }
    for (size_t i = 0, sz = queue.size(); i < sz; ++i)
    {
      if (i == head)
      {
        out << "[HEAD" << idx << "]=> ";
      }
      out << "#" << queue[i].getId() << " ";
    }
    out << "\n";
  }

  SmtContext& d_context;
  Params& d_params;
  std::vector<Node> d_queue;
  size_t d_head;
  /** The number of Boolean variables before the search started. */
  BoolVar d_bsNumBoolVars;
  std::vector<Node> d_queue2;
  size_t d_head2;
  std::vector<Scope> d_scopes;
};

/**
 * The case split queue based on relevancy propagation, falling back to
 * activity for the variables created during the search.
 */
class RelActCaseSplitQueue : public CaseSplitQueue
{
  struct Scope
  {
    size_t d_queueTrail;
    size_t d_headOld;
  };

 public:
  RelActCaseSplitQueue(SmtContext& ctx, Params& p)
      : d_context(ctx),
        d_params(p),
        d_head(0),
        d_bsNumBoolVars(UINT32_MAX),
        d_delayedQueue(1024, BoolVarActLt(ctx.getActivityVector()))
  {
  }

  void activityIncreasedEh(BoolVar v) override {}

  void activityDecreasedEh(BoolVar v) override {}

  void mkVarEh(BoolVar v) override
  {
    if (d_context.isSearching())
    {
      Assert(v >= d_bsNumBoolVars);
      d_delayedQueue.reserve(v + 1);
      d_delayedQueue.insert(v);
    }
  }

  void delVarEh(BoolVar v) override
  {
    if (v >= d_bsNumBoolVars && d_delayedQueue.contains(v))
    {
      d_delayedQueue.erase(v);
    }
  }

  void unassignVarEh(BoolVar v) override
  {
    if (v < d_bsNumBoolVars)
    {
      return;
    }
    if (!d_delayedQueue.contains(v))
    {
      d_delayedQueue.insert(v);
    }
  }

  void relevantEh(TNode n) override
  {
    if (!n.getType().isBoolean())
    {
      return;
    }
    bool isOr = n.getKind() == Kind::OR;
    bool intern = d_context.bInternalized(n);
    if (!intern && !isOr)
    {
      return;
    }
    BoolVar var = s_nullBoolVar;
    if (intern)
    {
      var = d_context.getBoolVar(n);
      Assert(var != s_nullBoolVar);
      bool isAnd = n.getKind() == Kind::AND;
      LBool val = d_context.getAssignment(var);
      if (!(val == L_UNDEF || (isOr && val == L_TRUE)
            || (isAnd && val == L_FALSE)))
      {
        return;
      }
    }
    if (!intern)
    {
      if (!d_context.isSearching())
      {
        d_queue.push_back(n);
      }
      return;
    }
    if (var < d_bsNumBoolVars)
    {
      d_queue.push_back(n);
    }
  }

  void initSearchEh() override
  {
    d_bsNumBoolVars = static_cast<BoolVar>(d_context.getNumBoolVars());
  }

  void endSearchEh() override { d_bsNumBoolVars = UINT32_MAX; }

  void reset() override
  {
    d_queue.clear();
    d_head = 0;
    d_delayedQueue.reset();
    d_scopes.clear();
  }

  void pushScope() override
  {
    d_scopes.push_back(Scope{d_queue.size(), d_head});
  }

  void popScope(size_t numScopes) override
  {
    Assert(numScopes <= d_scopes.size());
    size_t newLvl = d_scopes.size() - numScopes;
    Scope& s = d_scopes[newLvl];
    d_queue.resize(s.d_queueTrail);
    d_head = s.d_headOld;
    d_scopes.resize(newLvl);
    Assert(d_head <= d_queue.size());
  }

  void nextCaseSplit(BoolVar& next, LBool& phase) override
  {
    if (d_context.getRandomValue()
        < static_cast<int>(0.02 * RandomGen::maxValue()))
    {
      next = d_context.getRandomValue() % d_context.getNumBInternalized();
      if (d_context.getAssignment(next) == L_UNDEF)
      {
        return;
      }
    }

    nextCaseSplitCore(next, phase);
    if (next != s_nullBoolVar)
    {
      return;
    }
    phase = L_UNDEF;
    while (!d_delayedQueue.empty())
    {
      next = d_delayedQueue.eraseMin();
      if (d_context.getAssignment(next) == L_UNDEF)
      {
        return;
      }
    }
    next = s_nullBoolVar;
  }

  void print(std::ostream& out) override
  {
    if (d_queue.empty())
    {
      return;
    }
    out << "case-splits:\n";
    for (size_t i = 0, sz = d_queue.size(); i < sz; ++i)
    {
      if (i == d_head)
      {
        out << "[HEAD]=> ";
      }
      out << "#" << d_queue[i].getId() << " ";
    }
    out << "\n";
  }

 private:
  void nextCaseSplitCore(BoolVar& next, LBool& phase)
  {
    phase = L_UNDEF;
    size_t sz = d_queue.size();
    for (; d_head < sz; ++d_head)
    {
      TNode curr = d_queue[d_head];
      bool isOr = curr.getKind() == Kind::OR;
      bool isAnd = curr.getKind() == Kind::AND;
      bool intern = d_context.bInternalized(curr);
      Assert(intern || isOr);
      LBool val = L_UNDEF;
      if (intern)
      {
        next = d_context.getBoolVar(curr);
        val = d_context.getAssignment(next);
      }
      else
      {
        Assert(isOr);  // a top level clause
        val = L_TRUE;
      }
      if ((isOr && val == L_TRUE) || (isAnd && val == L_FALSE))
      {
        TNode undefChild;
        if (!hasChildAssignedTo(
                d_context, curr, val, undefChild, d_params.d_relCaseSplitOrder))
        {
          Literal l = d_context.getLiteral(undefChild);
          next = l.var();
          phase = l.sign() ? L_FALSE : L_TRUE;
          return;
        }
      }
      else if (val == L_UNDEF)
      {
        Assert(intern && d_context.getBoolVar(curr) == next);
        phase = L_UNDEF;
        return;
      }
    }
    next = s_nullBoolVar;
  }

  SmtContext& d_context;
  Params& d_params;
  std::vector<Node> d_queue;
  size_t d_head;
  /** The number of Boolean variables before the search started. */
  BoolVar d_bsNumBoolVars;
  BoolVarActQueue d_delayedQueue;
  std::vector<Scope> d_scopes;
};

/** The activity queue, with priorities that theories may adjust. */
class TheoryAwareBranchingQueue : public CaseSplitQueue
{
 public:
  TheoryAwareBranchingQueue(SmtContext& ctx, Params& p)
      : d_context(ctx),
        d_params(p),
        d_queue(1024,
                TheoryAwareActLt(ctx.getActivityVector(),
                                 d_theoryVarPriority))
  {
  }

  void activityIncreasedEh(BoolVar v) override
  {
    if (d_queue.contains(v))
    {
      d_queue.decreased(v);
    }
  }

  void activityDecreasedEh(BoolVar v) override
  {
    if (d_queue.contains(v))
    {
      d_queue.increased(v);
    }
  }

  void mkVarEh(BoolVar v) override
  {
    d_queue.reserve(v + 1);
    d_queue.insert(v);
  }

  void delVarEh(BoolVar v) override
  {
    if (d_queue.contains(v))
    {
      d_queue.erase(v);
    }
  }

  void unassignVarEh(BoolVar v) override
  {
    if (!d_queue.contains(v))
    {
      d_queue.insert(v);
    }
  }

  void relevantEh(TNode n) override {}

  void initSearchEh() override {}

  void endSearchEh() override {}

  void reset() override { d_queue.reset(); }

  void pushScope() override {}

  void popScope(size_t numScopes) override {}

  void nextCaseSplit(BoolVar& next, LBool& phase) override
  {
    int threshold =
        static_cast<int>(d_params.d_randomVarFreq * RandomGen::maxValue());
    Assert(threshold >= 0);
    if (d_context.getRandomValue() < threshold)
    {
      Assert(d_context.getNumBInternalized() > 0);
      next = d_context.getRandomValue() % d_context.getNumBInternalized();
      if (d_context.getAssignment(next) == L_UNDEF)
      {
        return;
      }
    }

    while (!d_queue.empty())
    {
      next = d_queue.eraseMin();
      if (d_context.getAssignment(next) == L_UNDEF)
      {
        auto it = d_theoryVarPhase.find(next);
        phase = it == d_theoryVarPhase.end() ? L_UNDEF : it->second;
        return;
      }
    }

    next = s_nullBoolVar;
  }

  void addTheoryAwareBranchingInfo(BoolVar v,
                                   double priority,
                                   LBool phase) override
  {
    d_theoryVarPhase[v] = phase;
    d_theoryVarPriority[v] = priority;
    if (d_queue.contains(v))
    {
      if (priority > 0.0)
      {
        d_queue.decreased(v);
      }
      else
      {
        d_queue.increased(v);
      }
    }
  }

  void print(std::ostream& out) override
  {
    bool first = true;
    for (int v : d_queue)
    {
      if (d_context.getAssignment(static_cast<BoolVar>(v)) == L_UNDEF)
      {
        if (first)
        {
          out << "remaining case-splits:\n";
          first = false;
        }
        out << "#" << d_context.boolVar2Expr(static_cast<BoolVar>(v)).getId()
            << " ";
      }
    }
    if (!first)
    {
      out << "\n";
    }
  }

 private:
  SmtContext& d_context;
  Params& d_params;
  TheoryVarPriorityMap d_theoryVarPriority;
  TheoryAwareActQueue d_queue;
  std::unordered_map<BoolVar, LBool> d_theoryVarPhase;
};

}  // namespace

CaseSplitQueue* mkCaseSplitQueue(SmtContext& ctx, Params& p)
{
  bool isRelevancyStrategy = p.d_caseSplitStrategy == CS_RELEVANCY
                             || p.d_caseSplitStrategy == CS_RELEVANCY_ACTIVITY
                             || p.d_caseSplitStrategy == CS_RELEVANCY_GOAL;
  if (ctx.relevancyLvl() < 2 && isRelevancyStrategy)
  {
    Warning() << "z3: relevancy must be enabled to use a relevancy-based "
                 "case split strategy; falling back to activity"
              << std::endl;
    p.d_caseSplitStrategy = CS_ACTIVITY;
  }
  else if (p.d_autoConfig && isRelevancyStrategy)
  {
    Warning() << "z3: auto configuration (--z3-auto-config) must be disabled "
                 "to use a relevancy-based case split strategy; falling back "
                 "to activity"
              << std::endl;
    p.d_caseSplitStrategy = CS_ACTIVITY;
  }
  switch (p.d_caseSplitStrategy)
  {
    case CS_ACTIVITY_DELAY_NEW: return new DactCaseSplitQueue(ctx, p);
    case CS_ACTIVITY_WITH_CACHE: return new CactCaseSplitQueue(ctx, p);
    case CS_RELEVANCY: return new RelCaseSplitQueue(ctx, p);
    case CS_RELEVANCY_ACTIVITY: return new RelActCaseSplitQueue(ctx, p);
    case CS_RELEVANCY_GOAL:
      Warning() << "z3: the relevancy-goal case split strategy is not ported "
                   "(it depends on Z3 labels); falling back to relevancy"
                << std::endl;
      return new RelCaseSplitQueue(ctx, p);
    case CS_ACTIVITY_THEORY_AWARE_BRANCHING:
      return new TheoryAwareBranchingQueue(ctx, p);
    default: return new ActCaseSplitQueue(ctx, p);
  }
}

}  // namespace z3
}  // namespace cvc5::internal

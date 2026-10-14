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
#include "z3/prop_core.h"
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
  ActCaseSplitQueue(PropCore& core, Params& p)
      : d_core(core),
        d_params(p),
        d_queue(1024, BoolVarActLt(core.getActivityVector()))
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

  void relevantEh(TNode /*n*/) override {}

  void initSearchEh() override {}

  void endSearchEh() override {}

  void reset() override { d_queue.reset(); }

  void pushScope() override {}

  void popScope(size_t /*numScopes*/) override {}

  void nextCaseSplit(BoolVar& next, LBool& phase) override
  {
    phase = L_UNDEF;

    if (d_core.getRandomValue()
        < static_cast<int>(d_params.d_randomVarFreq * RandomGen::maxValue()))
    {
      next = d_core.getRandomValue() % d_core.getNumBInternalized();
      if (d_core.getAssignment(next) == L_UNDEF)
      {
        return;
      }
    }

    while (!d_queue.empty())
    {
      next = d_queue.eraseMin();
      if (d_core.getAssignment(next) == L_UNDEF)
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
      if (d_core.getAssignment(static_cast<BoolVar>(v)) == L_UNDEF)
      {
        if (first)
        {
          out << "remaining case-splits:\n";
          first = false;
        }
        out << "#" << d_core.boolVar2Expr(static_cast<BoolVar>(v)).getId()
            << " ";
      }
    }
    if (!first)
    {
      out << "\n";
    }
  }

 protected:
  PropCore& d_core;
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
  DactCaseSplitQueue(PropCore& core, Params& p)
      : ActCaseSplitQueue(core, p),
        d_delayedQueue(1024, BoolVarActLt(core.getActivityVector()))
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
    if (d_core.isSearching())
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
      if (d_core.getAssignment(next) == L_UNDEF)
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
  CactCaseSplitQueue(PropCore& core, Params& p) : ActCaseSplitQueue(core, p) {}

  void mkVarEh(BoolVar v) override
  {
    TNode n = d_core.boolVar2Expr(v);
    if (!n.isNull())
    {
      auto it = d_cache.find(n);
      if (it != d_cache.end())
      {
        d_core.setActivity(v, it->second);
      }
    }
    ActCaseSplitQueue::mkVarEh(v);
  }

  void delVarEh(BoolVar v) override
  {
    if (d_core.isSearching())
    {
      double act = d_core.getActivity(v);
      if (act > 0.0)
      {
        TNode n = d_core.boolVar2Expr(v);
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
bool hasChildAssignedTo(
    PropCore& core, TNode parent, LBool val, TNode& undefChild, uint32_t order)
{
  std::vector<Node> undefChildren;
  bool foundUndef = false;
  size_t numArgs = parent.getNumChildren();
  for (size_t i = 0; i < numArgs; ++i)
  {
    TNode arg = parent[i];
    LBool argVal = core.getAssignment(arg);
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
      undefChild = undefChildren[core.getRandomValue() % undefChildren.size()];
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
  RelCaseSplitQueue(PropCore& core, Params& p)
      : d_core(core),
        d_params(p),
        d_head(0),
        d_bsNumBoolVars(UINT32_MAX),
        d_head2(0)
  {
  }

  void activityIncreasedEh(BoolVar /*v*/) override {}

  void activityDecreasedEh(BoolVar /*v*/) override {}

  void mkVarEh(BoolVar /*v*/) override {}

  void delVarEh(BoolVar /*v*/) override {}

  void unassignVarEh(BoolVar /*v*/) override {}

  void relevantEh(TNode n) override
  {
    if (!n.getType().isBoolean())
    {
      return;
    }
    bool isOr = n.getKind() == Kind::OR;
    bool intern = d_core.bInternalized(n);
    if (!intern && !isOr)
    {
      return;
    }
    BoolVar var = s_nullBoolVar;
    if (intern)
    {
      var = d_core.getBoolVar(n);
      Assert(var != s_nullBoolVar);
      bool isAnd = n.getKind() == Kind::AND;
      LBool val = d_core.getAssignment(var);
      if (!(val == L_UNDEF ||            // n was not assigned yet
            (isOr && val == L_TRUE) ||   // need to justify a child
            (isAnd && val == L_FALSE)))  // need to justify a child
      {
        return;
      }
    }
    if (!intern && d_core.isSearching())
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
    d_bsNumBoolVars = static_cast<BoolVar>(d_core.getNumBoolVars());
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
    d_scopes.push_back(Scope{d_queue.size(), d_head, d_queue2.size(), d_head2});
    Trace("z3-csq-head") << "PUSH head " << d_head << std::endl;
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
    if (TraceIsOn("z3-csq-queue"))
    {
      Trace("z3-csq-queue") << "QUEUE1 head " << d_head << " size "
                            << d_queue.size() << std::endl;
      for (size_t i = d_head; i < d_queue.size(); ++i)
      {
        Trace("z3-csq-queue") << "  Q1 " << d_queue[i] << std::endl;
      }
      Trace("z3-csq-queue") << "QUEUE2 head " << d_head2 << " size "
                            << d_queue2.size() << std::endl;
      for (size_t i = d_head2; i < d_queue2.size(); ++i)
      {
        Trace("z3-csq-queue") << "  Q2 " << d_queue2[i] << std::endl;
      }
    }
    nextCaseSplitCore(d_queue, d_head, next, phase);
    if (next == s_nullBoolVar)
    {
      nextCaseSplitCore(d_queue2, d_head2, next, phase);
    }
    // Force the negative phase if next is an equality already known to be
    // disequal in the logical context.
    if (d_params.d_lookaheadDiseq && next != s_nullBoolVar && phase != L_FALSE
        && d_core.isExtDiseqAtom(next))
    {
      phase = L_FALSE;
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
      bool intern = d_core.bInternalized(curr);
      Assert(intern || isOr);
      LBool val = L_UNDEF;
      if (intern)
      {
        next = d_core.getBoolVar(curr);
        val = d_core.getAssignment(next);
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
                d_core, curr, val, undefChild, d_params.d_relCaseSplitOrder))
        {
          Trace("z3-events") << "CSQ andor" << std::endl;
          Trace("z3-csq-parent") << "ANDOR " << curr << std::endl;
          if (TraceIsOn("z3-csq-detail"))
          {
            Trace("z3-csq-detail") << "PARENT " << curr << std::endl;
            for (const Node& c : curr)
            {
              Trace("z3-csq-detail") << "  CHILD " << d_core.getAssignment(c)
                                     << " " << c << std::endl;
            }
          }
          Literal l = d_core.getLiteral(undefChild);
          next = l.var();
          phase = l.sign() ? L_FALSE : L_TRUE;
          return;
        }
      }
      else if (val == L_UNDEF)
      {
        Assert(intern && d_core.getBoolVar(curr) == next);
        Trace("z3-events") << "CSQ cand" << std::endl;
        Trace("z3-csq-parent") << "CAND " << curr << std::endl;
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

  PropCore& d_core;
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
  RelActCaseSplitQueue(PropCore& core, Params& p)
      : d_core(core),
        d_params(p),
        d_head(0),
        d_bsNumBoolVars(UINT32_MAX),
        d_delayedQueue(1024, BoolVarActLt(core.getActivityVector()))
  {
  }

  void activityIncreasedEh(BoolVar /*v*/) override {}

  void activityDecreasedEh(BoolVar /*v*/) override {}

  void mkVarEh(BoolVar v) override
  {
    if (d_core.isSearching())
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
    bool intern = d_core.bInternalized(n);
    if (!intern && !isOr)
    {
      return;
    }
    BoolVar var = s_nullBoolVar;
    if (intern)
    {
      var = d_core.getBoolVar(n);
      Assert(var != s_nullBoolVar);
      bool isAnd = n.getKind() == Kind::AND;
      LBool val = d_core.getAssignment(var);
      if (!(val == L_UNDEF || (isOr && val == L_TRUE)
            || (isAnd && val == L_FALSE)))
      {
        return;
      }
    }
    if (!intern)
    {
      if (!d_core.isSearching())
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
    d_bsNumBoolVars = static_cast<BoolVar>(d_core.getNumBoolVars());
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
    if (d_core.getRandomValue()
        < static_cast<int>(0.02 * RandomGen::maxValue()))
    {
      next = d_core.getRandomValue() % d_core.getNumBInternalized();
      if (d_core.getAssignment(next) == L_UNDEF)
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
      if (d_core.getAssignment(next) == L_UNDEF)
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
      bool intern = d_core.bInternalized(curr);
      Assert(intern || isOr);
      LBool val = L_UNDEF;
      if (intern)
      {
        next = d_core.getBoolVar(curr);
        val = d_core.getAssignment(next);
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
                d_core, curr, val, undefChild, d_params.d_relCaseSplitOrder))
        {
          Trace("z3-events") << "CSQ andor" << std::endl;
          Trace("z3-csq-parent") << "ANDOR " << curr << std::endl;
          if (TraceIsOn("z3-csq-detail"))
          {
            Trace("z3-csq-detail") << "PARENT " << curr << std::endl;
            for (const Node& c : curr)
            {
              Trace("z3-csq-detail") << "  CHILD " << d_core.getAssignment(c)
                                     << " " << c << std::endl;
            }
          }
          Literal l = d_core.getLiteral(undefChild);
          next = l.var();
          phase = l.sign() ? L_FALSE : L_TRUE;
          return;
        }
      }
      else if (val == L_UNDEF)
      {
        Assert(intern && d_core.getBoolVar(curr) == next);
        Trace("z3-events") << "CSQ cand" << std::endl;
        Trace("z3-csq-parent") << "CAND " << curr << std::endl;
        phase = L_UNDEF;
        return;
      }
    }
    next = s_nullBoolVar;
  }

  PropCore& d_core;
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
  TheoryAwareBranchingQueue(PropCore& core, Params& p)
      : d_core(core),
        d_params(p),
        d_queue(1024,
                TheoryAwareActLt(core.getActivityVector(), d_theoryVarPriority))
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

  void relevantEh(TNode /*n*/) override {}

  void initSearchEh() override {}

  void endSearchEh() override {}

  void reset() override { d_queue.reset(); }

  void pushScope() override {}

  void popScope(size_t /*numScopes*/) override {}

  void nextCaseSplit(BoolVar& next, LBool& phase) override
  {
    int threshold =
        static_cast<int>(d_params.d_randomVarFreq * RandomGen::maxValue());
    Assert(threshold >= 0);
    if (d_core.getRandomValue() < threshold)
    {
      Assert(d_core.getNumBInternalized() > 0);
      next = d_core.getRandomValue() % d_core.getNumBInternalized();
      if (d_core.getAssignment(next) == L_UNDEF)
      {
        return;
      }
    }

    while (!d_queue.empty())
    {
      next = d_queue.eraseMin();
      if (d_core.getAssignment(next) == L_UNDEF)
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
      if (d_core.getAssignment(static_cast<BoolVar>(v)) == L_UNDEF)
      {
        if (first)
        {
          out << "remaining case-splits:\n";
          first = false;
        }
        out << "#" << d_core.boolVar2Expr(static_cast<BoolVar>(v)).getId()
            << " ";
      }
    }
    if (!first)
    {
      out << "\n";
    }
  }

 private:
  PropCore& d_core;
  Params& d_params;
  TheoryVarPriorityMap d_theoryVarPriority;
  TheoryAwareActQueue d_queue;
  std::unordered_map<BoolVar, LBool> d_theoryVarPhase;
};

/**
 * A case split queue after cvc5's justification heuristic
 * (decision/justification_strategy.h), for comparing the decision heuristics
 * of the two systems (src/z3/PROPOSITIONAL_BRANCH.md, B3). Not in Z3.
 *
 * The asserted formulas, input formulas and quantifier instances alike, are
 * walked in the order they were asserted. The first that is not yet
 * justified by the current assignment is walked from the root, and the
 * first unassigned atom it needs is split on, with the polarity that
 * justifies it. An atom is a formula that is not a gate (see isGate).
 *
 * Once everything is justified, the remaining splits come from the
 * relevancy queue (RelCaseSplitQueue) at relevancy level 2, so that the
 * search stops on a partial assignment as it does with that queue, and as
 * cvc5's does once everything is justified. Without relevancy they come
 * from activity (ActCaseSplitQueue), and the assignment is completed: the
 * core has clauses that are not asserted formulas, such as those defining
 * term ITEs, which only a complete assignment or relevancy satisfies.
 */
class JustificationCaseSplitQueue : public CaseSplitQueue
{
  /** The outcome of justifying a formula with a value. */
  enum Status
  {
    /** the formula has the value, as its children justify */
    JUSTIFIED,
    /** the formula has the opposite value */
    FALSIFIED,
    /** an atom it needs is unassigned, and is the next split */
    SPLIT,
    /** it is undetermined, but nothing to split on was found */
    PENDING
  };

  /** The roots of one kind, and which of them are justified. */
  struct Roots
  {
    std::vector<Node> d_roots;
    std::vector<bool> d_justified;
    /** The roots before this one are justified. */
    size_t d_head = 0;
  };

  struct Scope
  {
    size_t d_rootsLim;
    size_t d_head;
    size_t d_permanentHead;
    size_t d_justifiedTrailLim;
  };

 public:
  JustificationCaseSplitQueue(PropCore& core, Params& p)
      : d_core(core), d_act(core, p), d_rel(core, p)
  {
  }

  void activityIncreasedEh(BoolVar v) override { d_act.activityIncreasedEh(v); }

  void activityDecreasedEh(BoolVar v) override { d_act.activityDecreasedEh(v); }

  void mkVarEh(BoolVar v) override
  {
    d_act.mkVarEh(v);
    d_rel.mkVarEh(v);
  }

  void delVarEh(BoolVar v) override
  {
    d_act.delVarEh(v);
    d_rel.delVarEh(v);
  }

  void assignLitEh(Literal l) override
  {
    d_act.assignLitEh(l);
    d_rel.assignLitEh(l);
  }

  void unassignVarEh(BoolVar v) override
  {
    d_act.unassignVarEh(v);
    d_rel.unassignVarEh(v);
  }

  void relevantEh(TNode n) override
  {
    d_act.relevantEh(n);
    d_rel.relevantEh(n);
  }

  void initSearchEh() override
  {
    d_act.initSearchEh();
    d_rel.initSearchEh();
  }

  void endSearchEh() override
  {
    d_act.endSearchEh();
    d_rel.endSearchEh();
  }

  void print(std::ostream& out) override
  {
    d_act.print(out);
    d_rel.print(out);
  }

  void rootEh(TNode n, bool permanent) override
  {
    Roots& r = permanent ? d_permanent : d_scoped;
    r.d_roots.push_back(n);
    r.d_justified.push_back(false);
  }

  void reset() override
  {
    d_act.reset();
    d_rel.reset();
    d_scoped = Roots();
    d_permanent = Roots();
    d_justifiedTrail.clear();
    d_scopes.clear();
  }

  void pushScope() override
  {
    d_act.pushScope();
    d_rel.pushScope();
    d_scopes.push_back(Scope{d_scoped.d_roots.size(),
                             d_scoped.d_head,
                             d_permanent.d_head,
                             d_justifiedTrail.size()});
  }

  void popScope(size_t numScopes) override
  {
    d_act.popScope(numScopes);
    d_rel.popScope(numScopes);
    Assert(numScopes <= d_scopes.size());
    size_t newLvl = d_scopes.size() - numScopes;
    Scope& s = d_scopes[newLvl];
    d_scoped.d_roots.resize(s.d_rootsLim);
    d_scoped.d_justified.resize(s.d_rootsLim);
    for (size_t i = s.d_justifiedTrailLim, sz = d_justifiedTrail.size(); i < sz;
         ++i)
    {
      std::pair<bool, size_t>& t = d_justifiedTrail[i];
      Roots& r = t.first ? d_permanent : d_scoped;
      if (t.second < r.d_justified.size())
      {
        r.d_justified[t.second] = false;
      }
    }
    d_justifiedTrail.resize(s.d_justifiedTrailLim);
    d_scoped.d_head = s.d_head;
    d_permanent.d_head = s.d_permanentHead;
    d_scopes.resize(newLvl);
  }

  void nextCaseSplit(BoolVar& next, LBool& phase) override
  {
    phase = L_UNDEF;
    if (nextCaseSplitCore(d_scoped, false, next, phase)
        || nextCaseSplitCore(d_permanent, true, next, phase))
    {
      return;
    }
    if (d_core.relevancyLvl() >= 2)
    {
      d_rel.nextCaseSplit(next, phase);
    }
    else
    {
      d_act.nextCaseSplit(next, phase);
    }
  }

 private:
  /**
   * Walk the roots that are not justified yet, splitting on the first atom
   * one of them needs. Returns true if there is a split. A root found
   * justified is marked until the search backtracks past the current scope,
   * and the head moves past the justified roots that come first.
   */
  bool nextCaseSplitCore(Roots& r, bool permanent, BoolVar& next, LBool& phase)
  {
    d_visited[0].clear();
    d_visited[1].clear();
    bool prefix = true;
    for (size_t i = r.d_head, sz = r.d_roots.size(); i < sz; ++i)
    {
      if (!r.d_justified[i])
      {
        Status s = justify(r.d_roots[i], true, next, phase);
        if (s == SPLIT)
        {
          return true;
        }
        if (s == JUSTIFIED)
        {
          r.d_justified[i] = true;
          d_justifiedTrail.emplace_back(permanent, i);
        }
      }
      if (prefix && r.d_justified[i])
      {
        r.d_head = i + 1;
      }
      else
      {
        prefix = false;
      }
    }
    return false;
  }

  /** The value of n, which may be a negation, if it has a variable. */
  LBool valueOf(TNode n) const
  {
    bool neg = false;
    while (n.getKind() == Kind::NOT)
    {
      n = n[0];
      neg = !neg;
    }
    LBool val = L_UNDEF;
    if (n.isConst())
    {
      val = n.getConst<bool>() ? L_TRUE : L_FALSE;
    }
    else if (d_core.bInternalized(n))
    {
      val = d_core.getAssignment(d_core.getBoolVar(n));
    }
    return neg ? ~val : val;
  }

  /** Justify that n has the value desired. */
  Status justify(TNode n, bool desired, BoolVar& next, LBool& phase)
  {
    while (n.getKind() == Kind::NOT)
    {
      n = n[0];
      desired = !desired;
    }
    std::unordered_map<Node, Status>& visited = d_visited[desired ? 1 : 0];
    auto it = visited.find(n);
    if (it != visited.end())
    {
      // a split would have been taken already
      Assert(it->second != SPLIT);
      return it->second;
    }
    Status s = justifyCore(n, desired, next, phase);
    visited[n] = s;
    return s;
  }

  Status justifyCore(TNode n, bool desired, BoolVar& next, LBool& phase)
  {
    LBool want = desired ? L_TRUE : L_FALSE;
    LBool val = valueOf(n);
    if (val != L_UNDEF && val != want)
    {
      return FALSIFIED;
    }
    if (!isGate(n))
    {
      if (val != L_UNDEF)
      {
        return JUSTIFIED;
      }
      if (!d_core.bInternalized(n))
      {
        return PENDING;
      }
      next = d_core.getBoolVar(n);
      phase = want;
      return SPLIT;
    }
    switch (n.getKind())
    {
      case Kind::OR:
      case Kind::AND:
      {
        bool one = (n.getKind() == Kind::OR) == desired;
        if (!one)
        {
          // every child must have the value
          bool pending = false;
          for (const Node& c : n)
          {
            Status s = justify(c, desired, next, phase);
            if (s == SPLIT || s == FALSIFIED)
            {
              return s;
            }
            pending = pending || s == PENDING;
          }
          return pending ? PENDING : JUSTIFIED;
        }
        // one child with the value suffices: prefer one that has it already
        for (const Node& c : n)
        {
          if (valueOf(c) == want)
          {
            Status s = justify(c, desired, next, phase);
            if (s == JUSTIFIED || s == SPLIT)
            {
              return s;
            }
          }
        }
        bool pending = false;
        for (const Node& c : n)
        {
          if (valueOf(c) == L_UNDEF)
          {
            Status s = justify(c, desired, next, phase);
            if (s == JUSTIFIED || s == SPLIT)
            {
              return s;
            }
            pending = pending || s == PENDING;
          }
        }
        return pending ? PENDING : FALSIFIED;
      }
      case Kind::ITE:
      {
        LBool cv = valueOf(n[0]);
        if (cv == L_UNDEF)
        {
          // split on the condition, towards a branch that has the value
          bool c = !(valueOf(n[2]) == want || valueOf(n[1]) == ~want);
          Status s = justify(n[0], c, next, phase);
          return s == SPLIT ? SPLIT : PENDING;
        }
        Status sc = justify(n[0], cv == L_TRUE, next, phase);
        if (sc == SPLIT)
        {
          return SPLIT;
        }
        Status sb = justify(n[cv == L_TRUE ? 1 : 2], desired, next, phase);
        if (sb == JUSTIFIED && sc == PENDING)
        {
          return PENDING;
        }
        return sb;
      }
      case Kind::EQUAL:
      {
        // both sides need a value
        size_t first = valueOf(n[0]) == L_UNDEF && valueOf(n[1]) != L_UNDEF;
        TNode a = n[first];
        TNode b = n[1 - first];
        LBool av = valueOf(a);
        if (av == L_UNDEF)
        {
          Status s = justify(a, true, next, phase);
          return s == SPLIT ? SPLIT : PENDING;
        }
        Status sa = justify(a, av == L_TRUE, next, phase);
        if (sa == SPLIT)
        {
          return SPLIT;
        }
        Status sb = justify(b, (av == L_TRUE) == desired, next, phase);
        if (sb == JUSTIFIED && sa == PENDING)
        {
          return PENDING;
        }
        return sb;
      }
      default: Unreachable();
    }
    return PENDING;
  }

  PropCore& d_core;
  /** The splits once everything is justified, without relevancy. */
  ActCaseSplitQueue d_act;
  /** The splits once everything is justified, at relevancy level 2. */
  RelCaseSplitQueue d_rel;
  /** The formulas asserted at the scopes of the search. */
  Roots d_scoped;
  /** The formulas that survive backtracking. */
  Roots d_permanent;
  /** The roots marked justified, in order, as (permanent, index). */
  std::vector<std::pair<bool, size_t>> d_justifiedTrail;
  std::vector<Scope> d_scopes;
  /** The formulas walked by the current split, for each desired value. */
  std::unordered_map<Node, Status> d_visited[2];
};

}  // namespace

CaseSplitQueue* mkCaseSplitQueue(PropCore& core, Params& p)
{
  bool isRelevancyStrategy = p.d_caseSplitStrategy == CS_RELEVANCY
                             || p.d_caseSplitStrategy == CS_RELEVANCY_ACTIVITY
                             || p.d_caseSplitStrategy == CS_RELEVANCY_GOAL;
  if (core.relevancyLvl() < 2 && isRelevancyStrategy)
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
    case CS_ACTIVITY_DELAY_NEW: return new DactCaseSplitQueue(core, p);
    case CS_ACTIVITY_WITH_CACHE: return new CactCaseSplitQueue(core, p);
    case CS_RELEVANCY: return new RelCaseSplitQueue(core, p);
    case CS_RELEVANCY_ACTIVITY: return new RelActCaseSplitQueue(core, p);
    case CS_RELEVANCY_GOAL:
      Warning() << "z3: the relevancy-goal case split strategy is not ported "
                   "(it depends on Z3 labels); falling back to relevancy"
                << std::endl;
      return new RelCaseSplitQueue(core, p);
    case CS_ACTIVITY_THEORY_AWARE_BRANCHING:
      return new TheoryAwareBranchingQueue(core, p);
    case CS_JUSTIFICATION: return new JustificationCaseSplitQueue(core, p);
    default: return new ActCaseSplitQueue(core, p);
  }
}

}  // namespace z3
}  // namespace cvc5::internal

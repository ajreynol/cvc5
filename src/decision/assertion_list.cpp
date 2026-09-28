/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of assertion list
 */

#include "decision/assertion_list.h"

#include "context/cdhashmap.h"

namespace cvc5::internal {
namespace decision {

/**
 * A permutation of the grouped slots in an AssertionList. Queues and slot
 * membership have assertion lifetime; all consumption state backtracks with
 * the assertion index. Thus a grouped slot always has a pending group member,
 * including after new lemmas arrive during search or after backtracking.
 */
class AssertionList::RoundRobin
{
 public:
  struct Group
  {
    Group(context::Context* ac, context::Context* ic) : d_queue(ac), d_index(ic)
    {
    }
    context::CDList<Node> d_queue;
    context::CDO<size_t> d_index;
  };

  RoundRobin(context::Context* ac, context::Context* ic)
      : d_ac(ac),
        d_ic(ic),
        d_slots(ac),
        d_order(ac),
        d_groups(ac),
        d_nextGroup(ic)
  {
  }

  void presolve()
  {
    d_nextGroup = 0;
    for (const auto& entry : d_groups)
    {
      entry.second->d_index = 0;
    }
  }

  void add(TNode n, TNode group)
  {
    d_slots.push_back(!group.isNull());
    if (group.isNull())
    {
      return;
    }
    auto it = d_groups.find(group);
    if (it == d_groups.end())
    {
      d_groups.insert(group, std::make_shared<Group>(d_ac, d_ic));
      d_order.push_back(group);
      it = d_groups.find(group);
    }
    it->second->d_queue.push_back(n);
    Trace("jh-inst-round-robin")
        << "enqueue " << group << " : " << n << std::endl;
  }

  TNode next(size_t slot, TNode original)
  {
    if (!d_slots[slot])
    {
      return original;
    }
    const size_t size = d_order.size();
    for (size_t i = 0; i < size; ++i)
    {
      size_t index = d_nextGroup.get() % size;
      d_nextGroup = index + 1;
      TNode q = d_order[index];
      Group& group = *d_groups.find(q)->second;
      size_t qi = group.d_index.get();
      if (qi < group.d_queue.size())
      {
        group.d_index = qi + 1;
        TNode n = group.d_queue[qi];
        Trace("jh-inst-round-robin")
            << "select " << q << " : " << n << std::endl;
        return n;
      }
    }
    Unreachable() << "Grouped assertion slot without a pending assertion";
  }

 private:
  context::Context* d_ac;
  context::Context* d_ic;
  context::CDList<bool> d_slots;
  context::CDList<Node> d_order;
  context::CDHashMap<Node, std::shared_ptr<Group>> d_groups;
  context::CDO<size_t> d_nextGroup;
};

const char* toString(DecisionStatus s)
{
  switch (s)
  {
    case DecisionStatus::INACTIVE: return "INACTIVE";
    case DecisionStatus::NO_DECISION: return "NO_DECISION";
    case DecisionStatus::DECISION: return "DECISION";
    case DecisionStatus::BACKTRACK: return "BACKTRACK";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, DecisionStatus s)
{
  out << toString(s);
  return out;
}

AssertionList::AssertionList(context::Context* ac,
                             context::Context* ic,
                             bool useDyn,
                             bool useRoundRobin)
    : d_assertions(ac),
      d_assertionIndex(ic),
      d_roundRobin(useRoundRobin ? std::make_unique<RoundRobin>(ac, ic)
                                 : nullptr),
      d_usingDynamic(useDyn),
      d_dindex(ic)
{
}

AssertionList::~AssertionList() = default;

void AssertionList::presolve()
{
  Trace("jh-status") << "AssertionList::presolve" << std::endl;
  d_assertionIndex = 0;
  d_dlist.clear();
  d_dindex = 0;
  if (d_roundRobin != nullptr)
  {
    d_roundRobin->presolve();
  }
}

void AssertionList::addAssertion(TNode n, TNode group)
{
  d_assertions.push_back(n);
  if (d_roundRobin != nullptr)
  {
    d_roundRobin->add(n, group);
  }
}

TNode AssertionList::getNextAssertion()
{
  size_t fromIndex;
  if (d_usingDynamic)
  {
    // is a dynamic assertion ready?
    fromIndex = d_dindex.get();
    if (fromIndex < d_dlist.size())
    {
      d_dindex = d_dindex.get() + 1;
      Trace("jh-status") << "Assertion " << d_dlist[fromIndex].getId()
                         << " from dynamic list" << std::endl;
      return d_dlist[fromIndex];
    }
  }
  // check if dynamic assertions
  fromIndex = d_assertionIndex.get();
  Assert(fromIndex <= d_assertions.size());
  if (fromIndex == d_assertions.size())
  {
    return Node::null();
  }
  // increment for the next iteration
  d_assertionIndex = d_assertionIndex + 1;
  Trace("jh-status") << "Assertion " << d_assertions[fromIndex].getId()
                     << std::endl;
  return d_roundRobin == nullptr
             ? TNode(d_assertions[fromIndex])
             : d_roundRobin->next(fromIndex, d_assertions[fromIndex]);
}
size_t AssertionList::size() const { return d_assertions.size(); }

void AssertionList::notifyStatus(TNode n, DecisionStatus s)
{
  Trace("jh-status") << "Assertion status " << s << " for " << n.getId()
                     << ", current " << d_dindex.get() << "/" << d_dlist.size()
                     << std::endl;
  if (!d_usingDynamic)
  {
    // not using dynamic ordering, return
    return;
  }
  if (s == DecisionStatus::NO_DECISION)
  {
    // no decision does not impact the decision order
    return;
  }
  std::unordered_set<TNode>::iterator it = d_dlistSet.find(n);
  if (s == DecisionStatus::DECISION)
  {
    if (it == d_dlistSet.end())
    {
      // if we just had a status on an assertion and it didn't occur in dlist,
      // then our index should have exhausted dlist
      Assert(d_dindex.get() == d_dlist.size());
      if (d_dindex.get() == d_dlist.size())
      {
        d_dindex = d_dindex.get() + 1;
      }
      // add to back of the decision list if not already there
      d_dlist.push_back(n);
      d_dlistSet.insert(n);
      Trace("jh-status") << "...push due to decision" << std::endl;
    }
    return;
  }
  if (s == DecisionStatus::BACKTRACK)
  {
    // backtrack inserts at the current position
    if (it == d_dlistSet.end())
    {
      d_dlist.insert(d_dlist.begin(), n);
      d_dlistSet.insert(n);
    }
  }
}

}  // namespace decision
}  // namespace cvc5::internal

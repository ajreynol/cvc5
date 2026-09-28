/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Tests for grouped assertion ordering in the justification heuristic.
 */

#include "decision/assertion_list.h"
#include "decision/justification_strategy.h"
#include "test_node.h"

namespace cvc5::internal {
namespace test {

using decision::AssertionList;
using decision::JustificationStrategy;

class TestDecisionWhiteJustification : public TestNode
{
 protected:
  Node atom() { return d_nodeManager->mkVar(*d_boolTypeNode); }
  void expect(AssertionList& list, const std::vector<Node>& nodes)
  {
    for (const Node& n : nodes)
    {
      ASSERT_EQ(list.getNextAssertion(), n);
    }
    ASSERT_TRUE(list.getNextAssertion().isNull());
  }
};

TEST_F(TestDecisionWhiteJustification, roundRobinSlots)
{
  context::Context ac, ic;
  AssertionList list(&ac, &ic, false, true);
  Node a = atom(), b = atom();
  Node a1 = atom(), a2 = atom(), a3 = atom();
  Node b1 = atom(), b2 = atom(), ordinary = atom();
  list.addAssertion(a1, a);
  list.addAssertion(a2, a);
  list.addAssertion(ordinary);
  list.addAssertion(a3, a);
  list.addAssertion(b1, b);
  list.addAssertion(b2, b);
  expect(list, {a1, b1, ordinary, a2, b2, a3});
  list.presolve();
  expect(list, {a1, b1, ordinary, a2, b2, a3});
}

TEST_F(TestDecisionWhiteJustification, disabledIsFifo)
{
  context::Context ac, ic;
  AssertionList list(&ac, &ic);
  Node a = atom(), b = atom(), a1 = atom(), a2 = atom(), b1 = atom();
  list.addAssertion(a1, a);
  list.addAssertion(a2, a);
  list.addAssertion(b1, b);
  expect(list, {a1, a2, b1});
}

TEST_F(TestDecisionWhiteJustification, satBacktrackAndLateArrival)
{
  context::Context ac, ic;
  AssertionList list(&ac, &ic, false, true);
  Node a = atom(), b = atom(), c = atom();
  Node a1 = atom(), a2 = atom(), b1 = atom(), c1 = atom(), a3 = atom();
  list.addAssertion(a1, a);
  list.addAssertion(a2, a);
  list.addAssertion(b1, b);
  ASSERT_EQ(list.getNextAssertion(), a1);
  ic.push();
  expect(list, {b1, a2});
  // New groups and entries persist when we backtrack the SAT context.
  list.addAssertion(c1, c);
  list.addAssertion(a3, a);
  expect(list, {c1, a3});
  ic.pop();
  expect(list, {b1, c1, a2, a3});
}

TEST_F(TestDecisionWhiteJustification, userPopAndReuseGroup)
{
  context::Context ac, ic;
  AssertionList list(&ac, &ic, false, true);
  Node a = atom(), b = atom(), a1 = atom(), a2 = atom(), b1 = atom();
  list.addAssertion(a1, a);
  ac.push();
  ic.push();
  list.addAssertion(a2, a);
  list.addAssertion(b1, b);
  expect(list, {a1, b1, a2});
  ic.pop();
  ac.pop();
  list.presolve();
  expect(list, {a1});
  list.addAssertion(b1, b);
  list.addAssertion(a2, a);
  expect(list, {b1, a2});
}

TEST_F(TestDecisionWhiteJustification, activityOrderThenRoundRobin)
{
  context::Context ac, ic;
  AssertionList list(&ac, &ic, true, true);
  Node a = atom(), b = atom(), a1 = atom(), a2 = atom(), b1 = atom();
  list.addAssertion(a1, a);
  list.addAssertion(a2, a);
  list.addAssertion(b1, b);
  list.notifyStatus(a2, decision::DecisionStatus::BACKTRACK);
  // Activity has priority; the normal traversal still covers every slot.
  expect(list, {a2, a1, b1, a2});
}

TEST_F(TestDecisionWhiteJustification, quantifierGuard)
{
  Node x = d_nodeManager->mkBoundVar(*d_boolTypeNode);
  Node bvl = d_nodeManager->mkNode(Kind::BOUND_VAR_LIST, x);
  Node q = d_nodeManager->mkNode(Kind::FORALL, bvl, x);
  Node r = d_nodeManager->mkNode(Kind::FORALL, bvl, x.notNode());
  Node body = atom();
  EXPECT_EQ(JustificationStrategy::getInstQuantifier(
                d_nodeManager->mkNode(Kind::IMPLIES, q, body)),
            q);
  EXPECT_EQ(JustificationStrategy::getInstQuantifier(
                d_nodeManager->mkNode(Kind::OR, body, q.notNode())),
            q);
  EXPECT_TRUE(JustificationStrategy::getInstQuantifier(body).isNull());
  EXPECT_TRUE(JustificationStrategy::getInstQuantifier(
                  d_nodeManager->mkNode(Kind::OR, q, body))
                  .isNull());
  EXPECT_TRUE(
      JustificationStrategy::getInstQuantifier(
          d_nodeManager->mkNode(Kind::OR, q.notNode(), r.notNode(), body))
          .isNull());
}

}  // namespace test
}  // namespace cvc5::internal

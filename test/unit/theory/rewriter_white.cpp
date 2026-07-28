/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of the core rewriter.
 */

#include <utility>

#include "rewriter/rewrite_db_exec.h"
#include "test_smt.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace test {

using namespace theory;

class TestTheoryWhiteRewriter : public TestSmt
{
};

TEST_F(TestTheoryWhiteRewriter, deepFullRewrite)
{
  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  TypeNode intType = d_nodeManager->integerType();
  TypeNode setType = d_nodeManager->mkSetType(intType);
  Node x = d_skolemManager->mkDummySkolem("x", intType);
  Node tail = d_skolemManager->mkDummySkolem("tail", setType);
  Node set = tail;

  constexpr size_t kDepth = 4000;
  for (size_t i = 0; i < kDepth; ++i)
  {
    Node elem = d_nodeManager->mkConstInt(Rational(i));
    Node singleton = d_nodeManager->mkNode(Kind::SET_SINGLETON, elem);
    set = d_nodeManager->mkNode(Kind::SET_UNION, singleton, set);
  }

  Node mem = d_nodeManager->mkNode(Kind::SET_MEMBER, x, set);
  Node rewritten = rr->rewrite(mem);

  ASSERT_EQ(rewritten.getKind(), Kind::OR);
  ASSERT_EQ(rewritten.getNumChildren(), kDepth + 1);

  Node memberTail = d_nodeManager->mkNode(Kind::SET_MEMBER, x, tail);
  bool foundTail = false;
  for (const Node& c : rewritten)
  {
    if (c == memberTail)
    {
      foundTail = true;
      break;
    }
  }
  ASSERT_TRUE(foundTail);
}

TEST_F(TestTheoryWhiteRewriter, execRewriteStratification)
{
  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  Node vtrue = d_nodeManager->mkConst(true);
  Node two = d_nodeManager->mkConstInt(Rational(2));
  TypeNode realType = d_nodeManager->realType();

  auto mkSineDouble = [&](Node x) {
    Node sinx = d_nodeManager->mkNode(Kind::SINE, x);
    Node cosx = d_nodeManager->mkNode(Kind::COSINE, x);
    Node lhs = d_nodeManager->mkNode(
        Kind::SINE, d_nodeManager->mkNode(Kind::MULT, two, x));
    Node rhs = d_nodeManager->mkNode(Kind::MULT, two, sinx, cosx);
    return std::make_pair(lhs, rhs);
  };

  // The full and base caches must remain distinct regardless of which is
  // populated first.
  Node x = d_skolemManager->mkDummySkolem("x", realType);
  std::pair<Node, Node> sx = mkSineDouble(x);
  Node xfull = rr->rewrite(sx.first);
  Node xbase = rr->rewriteWithoutExec(sx.first);
  ASSERT_NE(xfull, xbase);
  ASSERT_EQ(rr->rewrite(sx.first), xfull);
  ASSERT_EQ(rr->rewriteWithoutExec(sx.first), xbase);

  Node y = d_skolemManager->mkDummySkolem("y", realType);
  std::pair<Node, Node> sy = mkSineDouble(y);
  Node ybase = rr->rewriteWithoutExec(sy.first);
  Node yfull = rr->rewrite(sy.first);
  ASSERT_NE(ybase, yfull);
  ASSERT_EQ(rr->rewriteWithoutExec(sy.first), ybase);
  ASSERT_EQ(rr->rewrite(sy.first), yfull);

  // Add a rule whose condition can be established only by the executable
  // sine-double rule. Even if the full cache for the condition is warm, the
  // condition lookup must use the base cache and reject this rule.
  rewriter::RewriteDbExec db(d_nodeManager.get());
  Node pv = NodeManager::mkBoundVar("pv", realType);
  std::pair<Node, Node> spv = mkSineDouble(pv);
  Node condition = spv.first.eqNode(spv.second);
  Node lhs = d_nodeManager->mkNode(Kind::COSINE, pv);
  db.addRule(ProofRewriteRule::ARITH_SINE_DOUBLE, {condition}, lhs, pv);

  Node z = d_skolemManager->mkDummySkolem("z", realType);
  std::pair<Node, Node> sz = mkSineDouble(z);
  Node conditionInst = sz.first.eqNode(sz.second);
  ASSERT_EQ(rr->rewrite(conditionInst), vtrue);

  ProofRewriteRule id = ProofRewriteRule::NONE;
  Node candidate = d_nodeManager->mkNode(Kind::COSINE, z);
  ASSERT_TRUE(db.rewrite(candidate, rr, nullptr, id).isNull());
  ASSERT_NE(rr->rewriteWithoutExec(conditionInst), vtrue);
}

}  // namespace test
}  // namespace cvc5::internal

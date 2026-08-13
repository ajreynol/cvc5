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

TEST_F(TestTheoryWhiteRewriter, execRewriteConditions)
{
  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  Node vtrue = d_nodeManager->mkConst(true);
  Node two = d_nodeManager->mkConstInt(Rational(2));
  Node four = d_nodeManager->mkConstInt(Rational(4));
  TypeNode realType = d_nodeManager->realType();

  // (sin (* 2 x)) = (* 2 (sin x) (cos x)), the conclusion of the unconditional
  // :exec rule arith-sine-double.
  auto mkSineDouble = [&](Node x) {
    Node sinx = d_nodeManager->mkNode(Kind::SINE, x);
    Node cosx = d_nodeManager->mkNode(Kind::COSINE, x);
    Node lhs = d_nodeManager->mkNode(Kind::SINE,
                                     d_nodeManager->mkNode(Kind::MULT, two, x));
    Node rhs = d_nodeManager->mkNode(Kind::MULT, two, sinx, cosx);
    return std::make_pair(lhs, rhs);
  };

  Node x = d_skolemManager->mkDummySkolem("x", realType);
  std::pair<Node, Node> sx = mkSineDouble(x);
  // The executable rule applies, hence both sides rewrite to the same thing.
  ASSERT_EQ(rr->rewrite(sx.first), rr->rewrite(sx.second));
  ASSERT_EQ(rr->rewrite(sx.first.eqNode(sx.second)), vtrue);

  // The conditional :exec rule arith-sine-quad rewrites (sin (* 4 x)) to
  // (* 2 (sin (* 2 x)) (cos (* 2 x))). Its condition is the equality above,
  // which holds only by applying arith-sine-double, i.e. executable rules are
  // applied when rewriting the conditions of executable rules as well.
  Node sin4x = d_nodeManager->mkNode(
      Kind::SINE, d_nodeManager->mkNode(Kind::MULT, four, x));
  Node sin2x = d_nodeManager->mkNode(Kind::SINE,
                                     d_nodeManager->mkNode(Kind::MULT, two, x));
  Node cos2x = d_nodeManager->mkNode(Kind::COSINE,
                                     d_nodeManager->mkNode(Kind::MULT, two, x));
  Node quad = d_nodeManager->mkNode(Kind::MULT, two, sin2x, cos2x);
  ASSERT_EQ(rr->rewrite(sin4x), rr->rewrite(quad));
  ASSERT_EQ(rr->rewrite(sin4x.eqNode(quad)), vtrue);
  // The rewritten form is cached, rewriting again gives the same result.
  ASSERT_EQ(rr->rewrite(sin4x), rr->rewrite(quad));
}

}  // namespace test
}  // namespace cvc5::internal

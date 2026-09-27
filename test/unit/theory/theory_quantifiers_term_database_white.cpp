/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Tests for equivalence-class term indices retained across rounds.
 */

#include "smt/smt_solver.h"
#include "test_smt.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/theory_engine.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace test {

using namespace theory;
using namespace theory::quantifiers;

class TestTheoryWhiteQuantifiersTermDatabase : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_slvEngine->setLogic(std::string("UF"));
    d_slvEngine->setOption("term-db-reuse-eqc", "true");
    d_slvEngine->setOption("term-db-mode", "relevant");
    d_slvEngine->finishInit();
    Env& env = d_slvEngine->getEnv();
    d_context = env.getContext();
    d_ee = std::make_unique<eq::EqualityEngine>(env, d_context, "test", false);
    d_ee->addFunctionKind(Kind::APPLY_UF);
    TheoryEngine* te = d_slvEngine->d_smtSolver->getTheoryEngine();
    d_qstate = std::make_unique<QuantifiersState>(
        env, Valuation(te), env.getLogicInfo());
    d_qstate->setEqualityEngine(d_ee.get());
    d_qreg = std::make_unique<QuantifiersRegistry>(env);
    d_tdb = std::make_unique<TermDb>(env, *d_qstate, *d_qreg);
    TypeNode u = d_nodeManager->mkSort("U");
    d_f = d_nodeManager->mkVar("f", d_nodeManager->mkFunctionType(u, u));
    d_a = d_nodeManager->mkVar("a", u);
    d_b = d_nodeManager->mkVar("b", u);
    d_c = d_nodeManager->mkVar("c", u);
    d_fa = d_nodeManager->mkNode(Kind::APPLY_UF, d_f, d_a);
    d_fb = d_nodeManager->mkNode(Kind::APPLY_UF, d_f, d_b);
    d_fc = d_nodeManager->mkNode(Kind::APPLY_UF, d_f, d_c);
  }

  void add(Node n, bool relevant = true)
  {
    d_ee->addTerm(n);
    d_tdb->addTerm(n);
    if (relevant)
    {
      d_tdb->setHasTerm(n);
    }
  }

  TNodeTrie* nextRound()
  {
    EXPECT_TRUE(d_tdb->reset(Theory::EFFORT_FULL));
    return d_tdb->getTermArgTrie(Node::null(), d_f);
  }

  /** Check both result-class membership and the argument key. */
  void expectTerm(TNodeTrie* index, Node n)
  {
    auto it = index->d_data.find(d_ee->getRepresentative(n));
    ASSERT_NE(it, index->d_data.end());
    ASSERT_EQ(it->second.existsTerm({d_ee->getRepresentative(n[0])}), n);
  }

  context::Context* d_context;
  std::unique_ptr<eq::EqualityEngine> d_ee;
  std::unique_ptr<QuantifiersState> d_qstate;
  std::unique_ptr<QuantifiersRegistry> d_qreg;
  std::unique_ptr<TermDb> d_tdb;
  Node d_f, d_a, d_b, d_c, d_fa, d_fb, d_fc;
};

TEST_F(TestTheoryWhiteQuantifiersTermDatabase, mergesAndBacktracking)
{
  add(d_fa);
  add(d_fb);
  expectTerm(nextRound(), d_fa);
  expectTerm(nextRound(), d_fb);
  d_context->push();
  Node eq = d_a.eqNode(d_b);
  d_ee->assertEquality(eq, true, eq);
  TNodeTrie* index = nextRound();
  ASSERT_EQ(index->d_data.size(), 1);
  // The first term in database order still wins a duplicate key.
  expectTerm(index, d_fa);
  d_context->pop();
  index = nextRound();
  ASSERT_EQ(index->d_data.size(), 2);
  expectTerm(index, d_fa);
  expectTerm(index, d_fb);
}

TEST_F(TestTheoryWhiteQuantifiersTermDatabase, resultClassMerge)
{
  add(d_fa);
  add(d_fb);
  ASSERT_EQ(nextRound()->d_data.size(), 2);
  d_context->push();
  Node eq = d_fa.eqNode(d_fb);
  d_ee->assertEquality(eq, true, eq);
  TNodeTrie* index = nextRound();
  ASSERT_EQ(index->d_data.size(), 1);
  expectTerm(index, d_fa);
  expectTerm(index, d_fb);
  d_context->pop();
  ASSERT_EQ(nextRound()->d_data.size(), 2);
}

TEST_F(TestTheoryWhiteQuantifiersTermDatabase, relevanceAndActivity)
{
  add(d_fa);
  add(d_fb, false);
  ASSERT_EQ(nextRound()->d_data.size(), 1);
  d_context->push();
  d_tdb->setHasTerm(d_fb);
  ASSERT_EQ(nextRound()->d_data.size(), 2);
  d_tdb->setTermInactive(d_fa);
  TNodeTrie* index = nextRound();
  ASSERT_EQ(index->d_data.size(), 1);
  expectTerm(index, d_fb);
  d_context->pop();
  index = nextRound();
  ASSERT_EQ(index->d_data.size(), 1);
  expectTerm(index, d_fa);
}

TEST_F(TestTheoryWhiteQuantifiersTermDatabase, sameSizeReplacement)
{
  add(d_fa);
  d_context->push();
  add(d_fb);
  expectTerm(nextRound(), d_fb);
  d_context->pop();
  d_context->push();
  add(d_fc);
  TNodeTrie* index = nextRound();
  ASSERT_EQ(index->d_data.size(), 2);
  expectTerm(index, d_fa);
  expectTerm(index, d_fc);
  ASSERT_EQ(index->d_data.count(d_fb), 0);
  d_context->pop();
}

TEST_F(TestTheoryWhiteQuantifiersTermDatabase, emptyAndNewTerms)
{
  ASSERT_TRUE(nextRound()->empty());
  ASSERT_TRUE(nextRound()->empty());
  d_context->push();
  add(d_fa);
  expectTerm(nextRound(), d_fa);
  d_context->pop();
  ASSERT_TRUE(nextRound()->empty());
  d_tdb->presolve();
  ASSERT_TRUE(nextRound()->empty());
}

}  // namespace test
}  // namespace cvc5::internal

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for the bit-vector arithmetic abstraction refinement lemmas.
 *
 * Verifies that every refinement lemma scheme `l[x,s,t]` is a sound over-
 * approximation of its operator, i.e. that `(x <op> s = t) => l` is valid,
 * and that this guarded form is what ProofRule::BV_ABSTRACTION accepts.
 */

#include <memory>
#include <optional>
#include <vector>

#include "expr/node.h"
#include "test_smt.h"
#include "theory/bv/abstract/abstraction_lemmas.h"
#include "theory/bv/proof_checker.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"
#include "util/result.h"

namespace cvc5::internal {

using namespace theory;
using namespace theory::bv;
using namespace theory::bv::abstract;

namespace test {

class TestTheoryWhiteBvAbstractionLemmas : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_slvEngine->setOption("incremental", "true");
    d_slvEngine->finishInit();
  }

  /** Check if Boolean node `pred` is T_BV-valid (i.e. ~pred is unsat). */
  void assertValid(TNode pred, Kind op, LemmaKind kind, uint32_t w)
  {
    Result res = d_slvEngine->checkSat(pred.notNode());
    ASSERT_EQ(res.getStatus(), Result::UNSAT)
        << "lemma is not valid: op=" << op << " kind=" << kind << " w=" << w
        << "\n  " << pred;
  }

  /**
   * Check all symbolic (non-value) lemmas for the given operator.
   * A purely symbolic lemma implements the 3-argument `instance(x, s, t)`
   * and returns a null Node for `instance(x, s, t, xval, sval)`.
   */
  void checkSymbolicLemma(Kind op)
  {
    NodeManager* nm = d_nodeManager.get();
    LemmaRegistry reg(nm);
    for (uint32_t w : {4u, 8u, 16u})
    {
      Node x = nm->mkVar("x", nm->mkBitVectorType(w));
      Node s = nm->mkVar("s", nm->mkBitVectorType(w));
      // t is bound to the true operator semantics.
      Node t = nm->mkNode(op, x, s);
      for (const std::unique_ptr<AbstractionLemma>& lemma : reg.lemmas(op))
      {
        Node inst = lemma->instance(x, s, t);
        if (inst.isNull())
        {
          continue;
        }
        assertValid(inst, op, lemma->getKind(), w);
      }
    }
  }

  /**
   * Check all model-value-based (power-of-two) lemmas for the given operator.
   * A model-value-based lemma returns a null node for `instance(x, s, t)`
   * and implements the 5-argument `instance(x, s, t, xval, sval)`.
   */
  void checkModelValueBasedLemma(Kind op)
  {
    NodeManager* nm = d_nodeManager.get();
    LemmaRegistry reg(nm);
    for (uint32_t w : {4u, 8u, 16u})
    {
      Node x = nm->mkVar("x", nm->mkBitVectorType(w));
      Node s = nm->mkVar("s", nm->mkBitVectorType(w));
      Node t = nm->mkNode(op, x, s);
      for (const std::unique_ptr<AbstractionLemma>& lemma : reg.lemmas(op))
      {
        // Exercise the lemma with every (negated) power-of-two operand value;
        // the builder selects the applicable ones (pow2 for *_POW2, negated
        // pow2 for MUL_NEG_POW2) and returns null otherwise.
        for (uint32_t i = 0; i < w; ++i)
        {
          Node pos = utils::mkConst(nm, w, static_cast<unsigned>(1u << i));
          Node neg = utils::mkConst(
              nm, w, static_cast<unsigned>((1u << w) - (1u << i)));
          for (const Node& val : {pos, neg})
          {
            // val_x and val_s both set to the candidate; the builder reads the
            // operand relevant to its operator and ignores the other.
            Node inst = lemma->instance(x, s, t, val, val);
            if (inst.isNull())
            {
              continue;
            }
            assertValid(inst, op, lemma->getKind(), w);
          }
        }
      }
    }
  }

  /**
   * @return All instantiations of `lemma` for the given operands: the single
   *         symbolic one for a purely symbolic scheme, or one instantiation
   *         per applicable (negated) power-of-two operand value otherwise.
   */
  std::vector<Node> instances(
      const AbstractionLemma& lemma, TNode x, TNode s, TNode t, uint32_t w)
  {
    NodeManager* nm = d_nodeManager.get();
    Node inst = lemma.instance(x, s, t);
    if (!inst.isNull())
    {
      return {inst};
    }
    std::vector<Node> insts;
    for (uint32_t i = 0; i < w; ++i)
    {
      Node pos = utils::mkConst(nm, w, static_cast<unsigned>(1u << i));
      Node neg =
          utils::mkConst(nm, w, static_cast<unsigned>((1u << w) - (1u << i)));
      for (const Node& val : {pos, neg})
      {
        inst = lemma.instance(x, s, t, val, val);
        if (!inst.isNull())
        {
          insts.push_back(inst);
        }
      }
    }
    return insts;
  }

  /**
   * Check that the guarded form `(=> (= (op x s) t) l)` of every instantiation
   * of every scheme for `op` is recognized as an abstraction lemma, both by
   * the registry and by the checker of ProofRule::BV_ABSTRACTION.
   */
  void checkProofRule(Kind op)
  {
    NodeManager* nm = d_nodeManager.get();
    LemmaRegistry reg(nm);
    bv::BVProofRuleChecker checker(nm);
    for (uint32_t w : {4u, 8u, 16u})
    {
      Node x = nm->mkVar("x", nm->mkBitVectorType(w));
      Node s = nm->mkVar("s", nm->mkBitVectorType(w));
      // t stands for the (unconstrained) abstraction of (op x s).
      Node t = nm->mkVar("t", nm->mkBitVectorType(w));
      Node guard = nm->mkNode(op, x, s).eqNode(t);
      for (const std::unique_ptr<AbstractionLemma>& lemma : reg.lemmas(op))
      {
        for (const Node& inst : instances(*lemma, x, s, t, w))
        {
          Node glem = guard.impNode(inst);
          std::optional<LemmaKind> kind = reg.isAbstractionLemma(glem);
          ASSERT_TRUE(kind.has_value())
              << "not matched: kind=" << lemma->getKind() << " w=" << w
              << "\n  " << glem;
          ASSERT_EQ(*kind, lemma->getKind());
          ASSERT_EQ(checker.check(ProofRule::BV_ABSTRACTION, {}, {glem}), glem);
          // The guard is required: the schemes are in general not valid for an
          // arbitrary t, hence the bare instantiation is not accepted.
          ASSERT_FALSE(reg.isAbstractionLemma(inst).has_value());
          ASSERT_TRUE(
              checker.check(ProofRule::BV_ABSTRACTION, {}, {inst}).isNull());
        }
      }
    }
  }
};

TEST_F(TestTheoryWhiteBvAbstractionLemmas, mul_symbolic)
{
  checkSymbolicLemma(Kind::BITVECTOR_MULT);
}

TEST_F(TestTheoryWhiteBvAbstractionLemmas, udiv_symbolic)
{
  checkSymbolicLemma(Kind::BITVECTOR_UDIV);
}

TEST_F(TestTheoryWhiteBvAbstractionLemmas, urem_symbolic)
{
  checkSymbolicLemma(Kind::BITVECTOR_UREM);
}

TEST_F(TestTheoryWhiteBvAbstractionLemmas, mul_value)
{
  checkModelValueBasedLemma(Kind::BITVECTOR_MULT);
}

TEST_F(TestTheoryWhiteBvAbstractionLemmas, udiv_value)
{
  checkModelValueBasedLemma(Kind::BITVECTOR_UDIV);
}

TEST_F(TestTheoryWhiteBvAbstractionLemmas, urem_value)
{
  checkModelValueBasedLemma(Kind::BITVECTOR_UREM);
}

TEST_F(TestTheoryWhiteBvAbstractionLemmas, mul_proof_rule)
{
  checkProofRule(Kind::BITVECTOR_MULT);
}

TEST_F(TestTheoryWhiteBvAbstractionLemmas, udiv_proof_rule)
{
  checkProofRule(Kind::BITVECTOR_UDIV);
}

TEST_F(TestTheoryWhiteBvAbstractionLemmas, urem_proof_rule)
{
  checkProofRule(Kind::BITVECTOR_UREM);
}

TEST_F(TestTheoryWhiteBvAbstractionLemmas, proof_rule_negative)
{
  NodeManager* nm = d_nodeManager.get();
  LemmaRegistry reg(nm);
  bv::BVProofRuleChecker checker(nm);
  uint32_t w = 8;
  Node x = nm->mkVar("x", nm->mkBitVectorType(w));
  Node s = nm->mkVar("s", nm->mkBitVectorType(w));
  Node t = nm->mkVar("t", nm->mkBitVectorType(w));
  Node t2 = nm->mkVar("t2", nm->mkBitVectorType(w));
  Node mul = nm->mkNode(Kind::BITVECTOR_MULT, x, s);
  // MUL3_IC for x, s, t
  Node inst;
  for (const std::unique_ptr<AbstractionLemma>& lemma :
       reg.lemmas(Kind::BITVECTOR_MULT))
  {
    if (lemma->getKind() == LemmaKind::MUL3_IC)
    {
      inst = lemma->instance(x, s, t);
    }
  }
  ASSERT_FALSE(inst.isNull());
  ASSERT_EQ(reg.isAbstractionLemma(mul.eqNode(t).impNode(inst)),
            LemmaKind::MUL3_IC);
  // the equality of the guard must have the abstracted term on the left
  Node reverseGuardLemma = t.eqNode(mul).impNode(inst);
  ASSERT_FALSE(reg.isAbstractionLemma(reverseGuardLemma));
  ASSERT_TRUE(checker.check(ProofRule::BV_ABSTRACTION,
                            {},
                            {reverseGuardLemma})
                  .isNull());
  // guard for a different abstraction constant
  ASSERT_FALSE(reg.isAbstractionLemma(mul.eqNode(t2).impNode(inst)));
  // guard for a different term
  Node mul2 = nm->mkNode(Kind::BITVECTOR_MULT, x, x);
  ASSERT_FALSE(reg.isAbstractionLemma(mul2.eqNode(t).impNode(inst)));
  // guard for an operator that is not abstracted
  Node add = nm->mkNode(Kind::BITVECTOR_ADD, x, s);
  ASSERT_FALSE(reg.isAbstractionLemma(add.eqNode(t).impNode(inst)));
  // the lemma is not an instantiation of any scheme
  ASSERT_FALSE(reg.isAbstractionLemma(mul.eqNode(t).impNode(inst.notNode())));
  // no guard at all
  ASSERT_FALSE(reg.isAbstractionLemma(inst));
  ASSERT_TRUE(checker.check(ProofRule::BV_ABSTRACTION, {}, {inst}).isNull());
  // Bit-widths below 3 are not accepted: some schemes are not valid for them,
  // which is why the abstraction module never considers such terms.
  Node x1 = nm->mkVar("x1", nm->mkBitVectorType(2));
  Node s1 = nm->mkVar("s1", nm->mkBitVectorType(2));
  Node t1 = nm->mkVar("t1", nm->mkBitVectorType(2));
  // (= (bvand (bvor (bvneg s1) s1) t1) t1), i.e. MUL3_IC for bit-width 2
  Node inst1 = nm->mkNode(Kind::BITVECTOR_AND,
                          nm->mkNode(Kind::BITVECTOR_OR,
                                     nm->mkNode(Kind::BITVECTOR_NEG, s1),
                                     s1),
                          t1)
                   .eqNode(t1);
  Node guard1 = nm->mkNode(Kind::BITVECTOR_MULT, x1, s1).eqNode(t1);
  ASSERT_FALSE(reg.isAbstractionLemma(guard1.impNode(inst1)));
}

}  // namespace test
}  // namespace cvc5::internal

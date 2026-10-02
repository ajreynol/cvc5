/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for proof node merging.
 */

#include "proof/proof.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "proof/proof_node_updater.h"
#include "test_smt.h"
#include "theory/builtin/proof_checker.h"

namespace cvc5::internal {
namespace test {

class TestProofNodeUpdater : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_slvEngine->setOption("produce-proofs", "true");
    d_slvEngine->setOption("proof-check", "eager");
    d_slvEngine->setOption("proof-pre-simp-lookahead", "0");
    d_slvEngine->finishInit();
    d_pnm = d_slvEngine->getEnv().getProofNodeManager();
    d_x = d_skolemManager->mkDummySkolem("x", d_nodeManager->integerType());
  }

  std::shared_ptr<ProofNode> mkTrust(ProofRule rule, Node result)
  {
    if (rule == ProofRule::TRUST)
    {
      return d_pnm->mkTrustedNode(TrustId::THEORY_LEMMA, {}, {}, result);
    }
    return d_pnm->mkNode(
        rule,
        {},
        {result,
         theory::builtin::BuiltinProofRuleChecker::mkTheoryIdNode(
             d_nodeManager.get(), theory::THEORY_ARITH),
         mkMethodId(d_nodeManager.get(), MethodId::RW_REWRITE)});
  }

  void checkTrustFree(std::shared_ptr<ProofNode> proof)
  {
    std::vector<std::shared_ptr<ProofNode>> trusted;
    expr::getSubproofRules(
        proof, {ProofRule::TRUST, ProofRule::TRUST_THEORY_REWRITE}, trusted);
    EXPECT_TRUE(trusted.empty());
  }

  ProofNodeManager* d_pnm;
  Node d_x;
};

TEST_F(TestProofNodeUpdater, prefer_without_reconstruction)
{
  for (ProofRule rule : {ProofRule::TRUST, ProofRule::TRUST_THEORY_REWRITE})
  {
    for (bool trustedFirst : {false, true})
    {
      for (bool nested : {false, true})
      {
        auto complete = d_pnm->mkNode(ProofRule::REFL, {}, {d_x});
        auto trusted = mkTrust(rule, complete->getResult());
        if (nested)
        {
          complete = d_pnm->mkNode(ProofRule::TRUE_INTRO, {complete}, {});
          trusted = d_pnm->mkNode(ProofRule::TRUE_INTRO, {trusted}, {});
        }
        // Children are visited in reverse order.
        auto root = d_pnm->mkNode(ProofRule::AND_INTRO,
                                  trustedFirst ? std::vector{complete, trusted}
                                               : std::vector{trusted, complete},
                                  {});
        ProofNodeUpdaterCallback cb;
        ProofNodeUpdater updater(d_slvEngine->getEnv(), cb, true);
        updater.process(root);
        checkTrustFree(root);
        EXPECT_EQ(root->getChildren()[0], root->getChildren()[1]);
        EXPECT_EQ(root->getChildren()[0]->getRule(),
                  nested ? ProofRule::TRUE_INTRO : ProofRule::REFL);
      }
    }
  }
}

TEST_F(TestProofNodeUpdater, update_finalized_parents)
{
  auto complete = d_pnm->mkNode(ProofRule::REFL, {}, {d_x});
  auto trusted = mkTrust(ProofRule::TRUST, complete->getResult());
  auto parent = d_pnm->mkNode(ProofRule::TRUE_INTRO, {trusted}, {});
  auto root = d_pnm->mkNode(ProofRule::AND_INTRO, {complete, parent}, {});
  ProofNodeUpdaterCallback cb;
  ProofNodeUpdater updater(d_slvEngine->getEnv(), cb, true);
  updater.process(root);
  checkTrustFree(root);
  EXPECT_EQ(trusted->getRule(), ProofRule::REFL);
}

TEST_F(TestProofNodeUpdater, cached_parent_becomes_complete)
{
  auto complete = d_pnm->mkNode(ProofRule::REFL, {}, {d_x});
  auto trusted = mkTrust(ProofRule::TRUST, complete->getResult());
  auto parent = d_pnm->mkNode(ProofRule::TRUE_INTRO, {trusted}, {});
  auto duplicate = d_pnm->mkNode(ProofRule::TRUE_INTRO, {complete}, {});
  auto root =
      d_pnm->mkNode(ProofRule::AND_INTRO, {duplicate, complete, parent}, {});
  ProofNodeUpdaterCallback cb;
  ProofNodeUpdater updater(d_slvEngine->getEnv(), cb, true);
  updater.process(root);
  // Improving the trusted child also improves the cached parent. Reusing that
  // parent must not rely on a stale record that it contains trusted steps.
  checkTrustFree(root);
  EXPECT_EQ(root->getChildren()[0], root->getChildren()[2]);
  EXPECT_EQ(root->clone()->getResult(), root->getResult());
}

TEST_F(TestProofNodeUpdater, merge_when_both_require_reconstruction)
{
  Node result = d_x.eqNode(d_x);
  auto first = mkTrust(ProofRule::TRUST, result);
  auto second = mkTrust(ProofRule::TRUST_THEORY_REWRITE, result);
  auto root = d_pnm->mkNode(ProofRule::AND_INTRO, {second, first}, {});
  ProofNodeUpdaterCallback cb;
  ProofNodeUpdater updater(d_slvEngine->getEnv(), cb, true);
  updater.process(root);
  EXPECT_EQ(root->getChildren()[0], root->getChildren()[1]);
  EXPECT_EQ(root->getChildren()[0]->getRule(), ProofRule::TRUST);
}

TEST_F(TestProofNodeUpdater, respect_allowed_assumptions)
{
  for (bool allowed : {false, true})
  {
    for (bool trustedFirst : {false, true})
    {
      Node result = d_x.eqNode(d_x);
      auto assumption = d_pnm->mkAssume(result);
      auto trusted = mkTrust(ProofRule::TRUST, result);
      auto root = d_pnm->mkNode(ProofRule::AND_INTRO,
                                trustedFirst ? std::vector{assumption, trusted}
                                             : std::vector{trusted, assumption},
                                {});
      ProofNodeUpdaterCallback cb;
      ProofNodeUpdater updater(d_slvEngine->getEnv(), cb, true);
      // The initially open proof is only closed by merging when !allowed.
      updater.setFreeAssumptions(
          allowed ? std::vector{result} : std::vector<Node>{}, allowed);
      updater.process(root);
      EXPECT_EQ(root->getChildren()[0], root->getChildren()[1]);
      EXPECT_EQ(root->getChildren()[0]->getRule(),
                allowed ? ProofRule::ASSUME : ProofRule::TRUST);
      EXPECT_EQ(root->isClosed(), !allowed);
    }
  }
}

TEST_F(TestProofNodeUpdater, merge_disabled)
{
  auto complete = d_pnm->mkNode(ProofRule::REFL, {}, {d_x});
  auto trusted = mkTrust(ProofRule::TRUST, complete->getResult());
  auto root = d_pnm->mkNode(ProofRule::AND_INTRO, {complete, trusted}, {});
  ProofNodeUpdaterCallback cb;
  ProofNodeUpdater updater(d_slvEngine->getEnv(), cb, false);
  updater.process(root);
  EXPECT_EQ(trusted->getRule(), ProofRule::TRUST);
  EXPECT_EQ(complete->getRule(), ProofRule::REFL);
}

TEST_F(TestProofNodeUpdater, local_scope_does_not_escape)
{
  Node result = d_x.eqNode(d_x);
  auto assumption = d_pnm->mkAssume(result);
  auto scoped = d_pnm->mkNode(ProofRule::SCOPE, {assumption}, {result});
  auto trusted = mkTrust(ProofRule::TRUST, result);
  // Visit the trusted proof first, then a proof using a local assumption.
  auto root = d_pnm->mkNode(ProofRule::AND_INTRO, {scoped, trusted}, {});
  ProofNodeUpdaterCallback cb;
  ProofNodeUpdater updater(d_slvEngine->getEnv(), cb, true);
  updater.setFreeAssumptions({}, true);
  updater.process(root);
  EXPECT_EQ(trusted->getRule(), ProofRule::TRUST);
  EXPECT_TRUE(root->isClosed());
}

/** Replace the selected trusted proof with REFL at post-visit. */
class ReconstructPostCallback : public ProofNodeUpdaterCallback
{
 public:
  explicit ReconstructPostCallback(std::shared_ptr<ProofNode> target)
      : d_target(target)
  {
  }
  bool shouldUpdatePost(std::shared_ptr<ProofNode> pn,
                        const std::vector<Node>&) override
  {
    return pn == d_target && pn->getRule() == ProofRule::TRUST;
  }
  bool updatePost(Node res,
                  ProofRule,
                  const std::vector<Node>&,
                  const std::vector<Node>&,
                  CDProof* cdp) override
  {
    return cdp->addStep(res, ProofRule::REFL, {}, {res[0]});
  }

 private:
  std::shared_ptr<ProofNode> d_target;
};

TEST_F(TestProofNodeUpdater, prefer_after_post_update)
{
  Node result = d_x.eqNode(d_x);
  auto first = mkTrust(ProofRule::TRUST, result);
  auto second = mkTrust(ProofRule::TRUST, result);
  auto root = d_pnm->mkNode(ProofRule::AND_INTRO, {second, first}, {});
  ReconstructPostCallback cb(second);
  ProofNodeUpdater updater(d_slvEngine->getEnv(), cb, true);
  updater.process(root);
  checkTrustFree(root);
}

}  // namespace test
}  // namespace cvc5::internal

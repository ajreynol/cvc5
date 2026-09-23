/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof generator for equalities proven by the rewrite database proof
 * reconstructor.
 */

#include "cvc5_private.h"

#ifndef CVC5__REWRITER__REWRITE_DB_PROOF_GENERATOR_H
#define CVC5__REWRITER__REWRITE_DB_PROOF_GENERATOR_H

#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "proof/proof.h"
#include "proof/proof_generator.h"
#include "rewriter/rewrite_proof_status.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

namespace theory {
class Evaluator;
}

namespace rewriter {

class BasicRewriteRCons;
class RewriteDb;

/**
 * Proven info, which stores information for each equality we attempt to
 * prove, including whether we were successful and what is the maximum
 * depth we have tried if we have failed.
 */
class ProvenInfo
{
 public:
  ProvenInfo()
      : d_id(RewriteProofStatus::FAIL),
        d_dslId(ProofRewriteRule::NONE),
        d_failMaxDepth(-1)
  {
  }
  /** The identifier of the proof rule, or fail if we failed */
  RewriteProofStatus d_id;
  /** The identifier of the DSL proof rule if d_id is DSL */
  ProofRewriteRule d_dslId;
  /** The substitution used, if successful */
  std::vector<Node> d_vars;
  std::vector<Node> d_subs;
  /**
   * The maximum depth tried for rules that have failed, where -1 indicates
   * that the formula is unprovable at any depth.
   */
  int64_t d_failMaxDepth;
  /**
   * Is internal rule? these rules store children (if any) in d_vars.
   */
  bool isInternalRule() const
  {
    return d_id != RewriteProofStatus::DSL
           && d_id != RewriteProofStatus::THEORY_REWRITE;
  }
};

/**
 * Constructs the formal proof of equalities that have been proven by
 * RewriteDbProofCons. It does not search for proofs itself; instead it reads
 * the proven infos computed by the reconstructor during proof search and
 * converts them into proof steps. For details, see IV.B of Noetzli et al
 * FMCAD 2022.
 *
 * This class references the caches of the reconstructor, which are cleared at
 * the beginning of each call to RewriteDbProofCons::prove. Hence, proofs
 * must be requested from this class before the next call to prove.
 */
class RewriteDbProofGenerator : protected EnvObj, public ProofGenerator
{
 public:
  /**
   * @param env Reference to the environment.
   * @param db Pointer to the rewrite database, used for DSL rules.
   * @param trrc The basic utility, used for expanding THEORY_REWRITE steps.
   * @param pcache The proven info cache of the reconstructor.
   * @param eval The evaluator of the reconstructor.
   * @param evalCache The evaluation cache of the reconstructor.
   */
  RewriteDbProofGenerator(Env& env,
                          RewriteDb* db,
                          BasicRewriteRCons& trrc,
                          const std::unordered_map<Node, ProvenInfo>& pcache,
                          theory::Evaluator& eval,
                          std::unordered_map<Node, Node>& evalCache);
  /**
   * Ensure proof for proven fact exists in cdp. This method is called on
   * equalities eqi after they have been successfully proven by the
   * reconstructor. Based on the information in proven infos, it constructs
   * the formal proof of eqi, which may involve recursing to premises of rules
   * that prove eqi. Steps already in cdp are reused.
   *
   * @param cdp The proof to add the proof of eqi to
   * @param eqi The proven equality
   * @return true if we successfully added a proof of eqi to cdp.
   */
  bool ensureProof(CDProof* cdp, const Node& eqi);
  /** Get the proof for proven fact f. */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Is f currently proven, according to the proven info cache? */
  bool hasProofFor(Node f) override;
  /** Identify this generator (for debugging, etc..) */
  std::string identify() const override;

 private:
  /** Return the evaluation of n, which uses the evaluation cache. */
  Node doEvaluate(const Node& n);
  /** Pointer to rewrite database */
  RewriteDb* d_db;
  /** Reference to the basic utility */
  BasicRewriteRCons& d_trrc;
  /** Reference to the proven info cache */
  const std::unordered_map<Node, ProvenInfo>& d_pcache;
  /** Reference to the evaluator */
  theory::Evaluator& d_eval;
  /** Reference to the evaluation cache */
  std::unordered_map<Node, Node>& d_evalCache;
  /** The true node */
  Node d_true;
};

}  // namespace rewriter
}  // namespace cvc5::internal

#endif /* CVC5__REWRITER__REWRITE_DB_PROOF_GENERATOR_H */

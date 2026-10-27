/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The proofs of the lemmas of the ported Z3 core.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__QUANTIFIERS__LEMMA_PROOF_GENERATOR_H
#define CVC5__Z3__QUANTIFIERS__LEMMA_PROOF_GENERATOR_H

#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "proof/proof_generator.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace z3 {

/**
 * Proves the lemmas the core sends, when their proofs are asked for:
 * - an instance, cvc5's instantiation lemma (=> q (q[1] * sigma)), where
 *   sigma substitutes the terms the core found by E-matching for the
 *   variables of q, by the instantiation, under the assumption q, and its
 *   scope, as for cvc5's own instantiations;
 * - a lemma weakened by the negation of a decision d (a delayed unit, see
 *   SmtContext::delayUnit), (or l1 ... ln (not d)), from the proof of the
 *   lemma (or l1 ... ln), in the form cvc5's preprocessing gives it.
 */
class LemmaProofGenerator : protected EnvObj, public ProofGenerator
{
 public:
  LemmaProofGenerator(Env& env);
  /**
   * Make the instance of q for terms, which this proves; terms are the
   * terms for the variables of q, in order.
   */
  Node mkInstance(TNode q, const std::vector<Node>& terms);
  /**
   * Note that the lemma lem, which trn proves (an instance, or the definition
   * of a skolem), is preprocessed by cvc5 to form, as proven by the rewrite
   * pp, which is null if form is lem.
   */
  void notifyPreprocessed(const Node& form,
                          const TrustNode& trn,
                          const TrustNode& pp);
  /** The lemma that cvc5 is sent for form, see notifyPreprocessed. */
  TrustNode getLemmaFor(const Node& form) const;
  /**
   * Make the lemma form weakened by the negation of d, (or form (not d))
   * flattened, which this proves; or null if this has no proof of form.
   */
  Node mkWeakened(const Node& form, const Node& d);
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  bool hasProofFor(Node f) override;
  std::string identify() const override { return "z3::LemmaProofGenerator"; }

 private:
  /** The proof of the lemma form, see notifyPreprocessed. */
  std::shared_ptr<ProofNode> getFormProof(const Node& form);
  /** The proof of the instance f, made by mkInstance. */
  std::shared_ptr<ProofNode> getInstanceProof(const Node& f);
  /** For each instance, the terms of its instantiation. */
  std::unordered_map<Node, std::vector<Node>> d_terms;
  /** See notifyPreprocessed. */
  std::unordered_map<Node, std::pair<TrustNode, TrustNode>> d_forms;
  /** For each weakened lemma, the lemma and the decision, see mkWeakened. */
  std::unordered_map<Node, std::pair<Node, Node>> d_weakened;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIERS__LEMMA_PROOF_GENERATOR_H */

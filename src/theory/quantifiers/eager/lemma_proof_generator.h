/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The proofs of the lemmas of the eager E-matching core.
 *
 * Not ported from Z3: original cvc5 code.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__LEMMA_PROOF_GENERATOR_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__LEMMA_PROOF_GENERATOR_H

#include <unordered_map>
#include <vector>

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "proof/proof_generator.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

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
  /** The maps of preprocessed and weakened lemmas are in env's user context. */
  LemmaProofGenerator(Env& env);
  /**
   * Make the instance of q for terms, which this proves; terms are the
   * terms for the variables of q, in order.
   */
  Node mkInstance(TNode q, const std::vector<Node>& terms);
  /**
   * Note that the lemma lem, which trn proves (an instance, or the definition
   * of a skolem), is preprocessed by cvc5 to form, as proven by the rewrite
   * pp, which is null if form is lem, and that norm is its core's form.
   */
  void notifyPreprocessed(const Node& norm,
                          const Node& form,
                          const TrustNode& trn,
                          const TrustNode& pp);
  /** The lemma that cvc5 is sent for form, see notifyPreprocessed. */
  TrustNode getLemmaFor(const Node& form) const;
  /**
   * The form of cvc5 that the lemma norm of the core was made from, which
   * has a proof, or null if proofs are not produced. Alpha-equivalent forms
   * of cvc5 have the same core's form, which cvc5's form given back by the
   * core's renaming is then one of, without a proof.
   */
  Node getHostForm(const Node& norm) const;
  /**
   * Make the lemma form weakened by the negation of d, (or form (not d))
   * flattened, which this proves; or null if this has no proof of form.
   */
  Node mkWeakened(const Node& form, const Node& d);
  /**
   * The proof of f, an instance made by mkInstance or a lemma weakened by
   * mkWeakened.
   */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Whether f is an instance made by mkInstance or a weakened lemma. */
  bool hasProofFor(Node f) override;
  /** The name of this proof generator. */
  std::string identify() const override
  {
    return "quantifiers::eager::LemmaProofGenerator";
  }

 private:
  /** The proof of the lemma form, see notifyPreprocessed. */
  std::shared_ptr<ProofNode> getFormProof(const Node& form);
  /** The proof of the instance f, made by mkInstance. */
  std::shared_ptr<ProofNode> getInstanceProof(const Node& f);
  /** For each instance, the terms of its instantiation. */
  std::unordered_map<Node, std::vector<Node>> d_terms;
  /**
   * See notifyPreprocessed. This and the maps below are in the user context,
   * as the proofs of cvc5's preprocessing are, which gives a lemma again,
   * with its skolem definitions, after a user pop.
   */
  context::CDHashMap<Node, std::pair<TrustNode, TrustNode>> d_forms;
  /** See getHostForm. */
  context::CDHashMap<Node, Node> d_hostForms;
  /** For each weakened lemma, the lemma and the decision, see mkWeakened. */
  context::CDHashMap<Node, std::pair<Node, Node>> d_weakened;
};

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER__LEMMA_PROOF_GENERATOR_H */

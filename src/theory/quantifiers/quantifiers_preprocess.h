/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Preprocessor for the theory of quantifiers.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_PREPROCESS_H
#define CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_PREPROCESS_H

#include "proof/trust_node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/quantifiers_rewriter.h"

namespace cvc5::internal {

class CDProof;
class EagerProofGenerator;

namespace theory {
namespace quantifiers {

/**
 * Module for doing preprocessing that is pertinent to quantifiers. These
 * operations cannot be done in the rewriter since e.g. preskolemization
 * depends on knowing the polarity of the position in which quantifiers occur.
 */
class QuantifiersPreprocess : protected EnvObj
{
 public:
  QuantifiersPreprocess(Env& env);
  ~QuantifiersPreprocess();
  /** preprocess
   *
   * This returns the result of applying simple quantifiers-specific
   * pre-processing to n, including but not limited to:
   * - pre-skolemization,
   * - aggressive prenexing.
   * The argument isInst is set to true if n is an instance of a previously
   * registered quantified formula. If this flag is true, we do not apply
   * certain steps like pre-skolemization since we know they will have no
   * effect.
   *
   * The result is wrapped in a trust node of kind TrustNodeKind::REWRITE.
   * If proofs are enabled, its generator provides a proof of the rewrite.
   * Pre-skolemization of top-level quantified formulas is justified by
   * SKOLEMIZE and INSTANTIATE steps. Steps that are not yet supported (nested
   * pre-skolemization, aggressive mode, inductive strengthening and prenexing)
   * are justified by trusted steps.
   */
  TrustNode preprocess(Node n, bool isInst = false) const;

 private:
  using NodePolPairHashFunction = PairHashFunction<Node, bool, std::hash<Node>>;
  /**
   * Pre-skolemize quantifiers. Return the pre-skolemized form of n.
   *
   * @param n The formula to preskolemize.
   * @param polarity The polarity of n in the input.
   * @param fvs The free variables
   * @param visited Cache of visited (node, polarity) pairs.
   * @param cdp If non-null, we add a proof of (= n ret) to cdp, where ret is
   * the returned node, if ret is different from n.
   */
  Node preSkolemizeQuantifiers(
      Node n,
      bool polarity,
      std::vector<TNode>& fvs,
      std::unordered_map<std::pair<Node, bool>, Node, NodePolPairHashFunction>&
          visited,
      CDProof* cdp) const;
  /**
   * Add to cdp a proof of (= q body), where q is a closed quantified formula
   * (forall x. F) and body is F{x -> k}, where k are the skolems of q, as
   * given by Skolemize::getSkolemConstants. This equivalence holds since k is
   * a witness for (not F). We prove (=> q body) by INSTANTIATE and
   * (=> (not q) (not body)) by SKOLEMIZE, and combine them via resolution.
   */
  void proveSkolemizeEq(CDProof* cdp, const Node& q, const Node& body) const;
  /**
   * Add to cdp a proof of (= a c) from proofs of (= a b) and (= b c), where
   * b is not added if it is equal to a or c.
   */
  void addTrans(CDProof* cdp, const Node& a, const Node& b, const Node& c) const;
  /**
   * Apply prenexing aggressively. Returns the prenex normal form of n.
   */
  Node computePrenexAgg(Node n, std::map<Node, Node>& visited) const;
  /** A quantifiers rewrite */
  QuantifiersRewriter d_qrew;
  /** Generator for the proofs of the rewrites returned by preprocess */
  std::unique_ptr<EagerProofGenerator> d_epg;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H */

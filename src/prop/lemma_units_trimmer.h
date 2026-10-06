/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Trims lemmas based on unit facts asserted to the SAT solver.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__LEMMA_UNITS_TRIMMER_H
#define CVC5__PROP__LEMMA_UNITS_TRIMMER_H

#include <vector>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "expr/node.h"
#include "proof/proof_generator.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class LazyCDProof;

namespace prop {

/**
 * This class trims lemmas, conflicts and explained propagations before they
 * are given to the SAT solver, based on the unit facts that have been asserted
 * to the SAT solver. In incremental mode, we only consider unit facts asserted
 * at user context level zero.
 *
 * For example, if A_1 is a unit fact and we are given the lemma
 *   (=> (and A_1 A_2) F)
 * whose proof is (SCOPE P :args (A_1 A_2)), then we instead give the lemma
 *   (=> A_2 F)
 * to the SAT solver, whose proof is (SCOPE P' :args (A_2)), where P' is P
 * where the (now free) assumption of A_1 is replaced by the proof of the unit
 * fact A_1 from the proof of the CNF stream. Thus, the SAT solver does not
 * need to resolve the clause of this lemma with the unit A_1.
 *
 * This class is also the proof generator for the trimmed lemmas.
 */
class LemmaUnitsTrimmer : protected EnvObj, public ProofGenerator
{
 public:
  /**
   * @param env The environment
   * @param cnfProof The proof of the CNF stream, which is used to get the
   * proofs of unit facts.
   */
  LemmaUnitsTrimmer(Env& env, LazyCDProof* cnfProof);
  ~LemmaUnitsTrimmer() {}
  /**
   * Notify that lit was asserted as a unit fact to the SAT solver, whose proof
   * is available from the proof of the CNF stream.
   */
  void notifyUnitFact(const Node& lit);
  /**
   * Notify that the formula f was asserted to the prop engine, i.e. as an
   * input or as a lemma.
   */
  void notifyAsserted(const Node& f);
  /**
   * Trim the given lemma, conflict or explained propagation. Returns the
   * trimmed trust node, whose generator is this class, or trn itself if it
   * cannot be trimmed.
   */
  TrustNode trim(const TrustNode& trn);
  /** Get proof for the conclusion of a trimmed lemma */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Identify */
  std::string identify() const override;

 private:
  /** Information on how we trimmed a lemma */
  struct TrimInfo
  {
    /** The original lemma and its generator */
    Node d_origProven;
    ProofGenerator* d_origGen;
    /** The antecedents of the original lemma */
    std::vector<Node> d_ante;
    /** The antecedents that were eliminated */
    std::vector<Node> d_elim;
    /** The remaining antecedents */
    std::vector<Node> d_remaining;
    /** The consequent of the lemma, or null if it is false */
    Node d_conc;
  };
  /**
   * Get the proof of the formula proven by the SCOPE with the given body and
   * assumptions, or the body itself if assumps is empty.
   */
  std::shared_ptr<ProofNode> mkScope(std::shared_ptr<ProofNode> body,
                                     const std::vector<Node>& assumps,
                                     const Node& expected);
  /** The proof of the CNF stream */
  LazyCDProof* d_cnfProof;
  /** The unit facts */
  context::CDHashSet<Node> d_facts;
  /**
   * The formulas asserted to the prop engine. We do not trim lemmas to these
   * formulas, since this may introduce cyclic proofs, e.g. if a trimmed lemma
   * concludes an input assertion F and depends on unit facts derived from F.
   */
  context::CDHashSet<Node> d_asserted;
  /** Maps the trimmed lemmas to how they were trimmed */
  context::CDHashMap<Node, std::shared_ptr<TrimInfo>> d_trimmed;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for processing proof nodes in the prop engine.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__PROOF_POST_PROCESSOR_H
#define CVC5__PROP__PROOF_POST_PROCESSOR_H

#include <map>
#include <unordered_set>

#include "context/cdhashset.h"
#include "proof/proof_generator.h"
#include "proof/proof_node_updater.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace prop {

/**
 * A callback class used by PropEngine for post-processing proof nodes by
 * connecting proofs of resolution, whose leaves are clausified preprocessed
 * assertions and lemmas, with the CNF transformation of these formulas, while
 * expanding the generators of lemmas.
 */
class ProofPostprocessCallback : protected EnvObj,
                                 public ProofNodeUpdaterCallback
{
 public:
  ProofPostprocessCallback(Env& env, ProofGenerator* pg);
  ~ProofPostprocessCallback() {}
  /**
   * Initialize, called once for each new ProofNode to process. This initializes
   * static information to be used by successive calls to update. For this
   * callback it resets d_assumpToProof.
   */
  void initializeUpdate();
  /** Should proof pn be updated?
   *
   * For this callback a proof node is updatable if it's an assumption for which
   * the proof cnf straem has a proof. However if the proof node is blocked
   * (which is the case for proof nodes introduced into the proof cnf stream's
   * proof via expansion of its generators) then traversal is the proof node is
   * cancelled, i.e., continueUpdate is set to false.
   */
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;
  /** Update the proof rule application.
   *
   * Replaces assumptions by their proof in proof cnf stream. Note that in doing
   * this the proof node is blocked, so that future post-processing does not
   * traverse it.
   *
   * This method uses the cache in d_assumpToProof to avoid recomputing proofs
   * for the same assumption (in the same scope).
   */
  bool update(Node res,
              ProofRule id,
              const std::vector<Node>& children,
              const std::vector<Node>& args,
              CDProof* cdp,
              bool& continueUpdate) override;
  /**
   * Whether a given proof is blocked for further updates.  An example of a
   * blocked proof node is one integrated into this class via an external proof
   * generator. */
  bool isBlocked(std::shared_ptr<ProofNode> pfn);

 private:
  /**
   * Blocks a proof, so that it is not further updated by a post processor of
   * this class's proof. */
  void addBlocked(std::shared_ptr<ProofNode> pfn);
  /** The cnf stream proof generator */
  ProofGenerator* d_pg;
  /** Blocked proofs.
   *
   * These are proof nodes added to this class by external generators. */
  context::CDHashSet<std::shared_ptr<ProofNode>, ProofNodeHashFunction>
      d_blocked;
  //---------------------------------reset at the begining of each update
  /** Mapping assumptions to their proof from cnf transformation */
  std::map<Node, std::shared_ptr<ProofNode> > d_assumpToProof;
  //---------------------------------end reset at the begining of each update
};

/**
 * The proof postprocessor module. This postprocesses the refutation proof
 * produced by the SAT solver. Its main task is to connect the refutation's
 * assumptions to the CNF transformation proof in ProofGenerator.
 */
class ProofPostprocess : protected EnvObj
{
 public:
  ProofPostprocess(Env& env, ProofGenerator* pg);
  ~ProofPostprocess();
  /** post-process
   *
   * The post-processing is done via a proof node updater run on pf with this
   * class's callback d_cb.
   */
  void process(std::shared_ptr<ProofNode> pf);

 private:
  /**
   * Shorten lemmas in the resolution steps of pf using unit premises.
   *
   * For each (CHAIN_/CHAIN_M_)RESOLUTION step of the propositional proof pf
   * (i.e. not within the proofs of lemmas or preprocessed assertions), if one
   * of its premises is a clause derived from a proof
   *   (SCOPE P :args (A_1 ... A_n))
   * using only clausification steps, and the step has unit premises proving
   * each of the A_i, then we replace the assumptions A_i in P by the proofs of
   * those units, remove the units from the resolution, and replace the
   * premise by P itself, avoiding SCOPE and clausification steps altogether.
   *
   * Each modified resolution step is checked by the proof checker, and we
   * leave the step unchanged if this check fails.
   */
  void shortenLemmasWithUnits(std::shared_ptr<ProofNode> pf);
  /**
   * Apply the above technique to resolution step pn, return true if pn
   * was modified.
   */
  bool shortenLemmasWithUnitsStep(ProofNode* pn);
  /**
   * Get the literal eliminated from the i^th premise of a resolution step
   * whose polarities and pivots are given by pols and pivs.
   */
  static Node getEliminatedLiteral(const std::vector<Node>& pols,
                                   const std::vector<Node>& pivs,
                                   size_t i);
  /**
   * Find a SCOPE that pn is derived from using only clausification steps,
   * return nullptr if none exists.
   */
  std::shared_ptr<ProofNode> findLemmaScope(std::shared_ptr<ProofNode> pn);
  /**
   * Make a proof node, checked by the proof checker, or return nullptr if
   * it does not check. If expected is non-null, we also require the
   * conclusion to be expected.
   */
  std::shared_ptr<ProofNode> mkCheckedNode(
      ProofRule id,
      const std::vector<std::shared_ptr<ProofNode>>& children,
      const std::vector<Node>& args,
      Node expected = Node::null());
  /** The post process callback */
  ProofPostprocessCallback d_cb;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif

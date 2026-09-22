/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Datatypes inference manager.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__DATATYPES__INFERENCE_MANAGER_H
#define CVC5__THEORY__DATATYPES__INFERENCE_MANAGER_H

#include <cstdint>
#include <memory>
#include <vector>

#include "context/cdhashset.h"
#include "expr/node.h"
#include "theory/datatypes/infer_proof_cons.h"
#include "theory/inference_manager_buffered.h"

namespace cvc5::internal {

class EagerProofGenerator;

namespace theory {
namespace datatypes {

class TheoryDatatypes;

/**
 * The datatypes inference manager, which uses the above class for
 * inferences.
 */
class InferenceManager : public InferenceManagerBuffered
{
  friend class DatatypesInference;

 public:
  InferenceManager(Env& env, TheoryDatatypes& t, TheoryState& state);
  ~InferenceManager();
  /**
   * Add pending inference, which may be processed as either a fact or
   * a lemma based on mustCommunicateFact in DatatypesInference above.
   *
   * @param conc The conclusion of the inference
   * @param exp The explanation of the inference
   * @param id The inference, used for stats and as a hint for constructing
   * the proof of (conc => exp)
   * @param forceLemma Whether this inference *must* be processed as a lemma.
   * Otherwise, it may be processed as a fact or lemma based on
   * mustCommunicateFact.
   */
  void addPendingInference(Node conc,
                           InferenceId id,
                           Node exp,
                           bool forceLemma = false);
  /**
   * Add pending lemma lem with property p, with proof generator pg.
   */
  bool addPendingLemma(Node lem,
                       InferenceId id,
                       LemmaProperty p = LemmaProperty::NONE,
                       ProofGenerator* pg = nullptr,
                       bool checkCache = true);
  /**
   * Add pending lemma, where lemma can be a derived theory inference.
   */
  void addPendingLemma(std::unique_ptr<TheoryInference> lemma);
  /**
   * Add pending fact conc with explanation exp and proof generator pg.
   */
  void addPendingFact(Node conc,
                      InferenceId id,
                      Node exp,
                      ProofGenerator* pg = nullptr);
  /**
   * Add pending fact, where fact can be a derived theory inference.
   */
  void addPendingFact(std::unique_ptr<TheoryInference> fact);
  /**
   * Process the current lemmas and facts. This is a custom method that can
   * be seen as overriding the behavior of calling both doPendingLemmas and
   * doPendingFacts. It determines whether facts should be sent as lemmas
   * or processed internally.
   */
  void process();
  /** Clear pending facts, lemmas, and phase requirements without processing. */
  void clearPending();
  /** Clear pending facts, without processing. */
  void clearPendingFacts();
  /** Clear pending lemmas, without processing. */
  void clearPendingLemmas();
  /** Notify this inference manager that a conflict was sent. */
  void notifyInConflict() override;
  /**
   * Send lemma immediately on the output channel
   */
  bool sendDtLemma(Node lem,
                   InferenceId id,
                   LemmaProperty p = LemmaProperty::NONE);
  /**
   * Send conflict immediately on the output channel
   */
  void sendDtConflict(const std::vector<Node>& conf, InferenceId id);

 private:
  /**
   * Process datatype inference as a lemma
   */
  TrustNode processDtLemma(Node conc, Node exp, InferenceId id);
  /**
   * Process datatype inference as a fact
   */
  Node processDtFact(Node conc, Node exp, InferenceId id, ProofGenerator*& pg);
  /**
   * Helper function for the above methods. Returns the conclusion, which
   * may be modified so that it is compatible with proofs. If proofs are
   * enabled, it ensures the proof constructor is ready to provide a proof
   * of (=> exp conc).
   *
   * In particular, if conc is a Boolean equality, it is rewritten. This is
   * to ensure that we do not assert equalities of the form (= t true)
   * or (= t false) to the equality engine, which have a reserved internal
   * status for proof generation. If this is not done, then it is possible
   * to have proofs with missing connections and hence free assumptions.
   */
  Node prepareDtInference(Node conc,
                          Node exp,
                          InferenceId id,
                          InferProofCons* ipc);
  /** Make a new SAT-context-dependent pending inference id. */
  uint64_t allocatePendingId();
  /** Process pending lemmas that are still valid in the current SAT context. */
  void processPendingLemmas();
  /**
   * Return whether pending inference id is still valid in the current SAT
   * context.
   */
  bool isPendingIdValid(uint64_t id) const;
  /** The theory of datatypes, which owns this inference manager */
  TheoryDatatypes& d_dt;
  /** The false node */
  Node d_false;
  /** The next pending inference id. */
  uint64_t d_nextPendingId;
  /** SAT-context-dependent set of currently valid pending inferences. */
  context::CDHashSet<uint64_t> d_validPendingIds;
  /** The ids corresponding to d_pendingLem. */
  std::vector<uint64_t> d_pendingLemmaIds;
  /** The ids corresponding to d_pendingFact. */
  std::vector<uint64_t> d_pendingFactIds;
  /** The inference to proof converter */
  std::unique_ptr<InferProofCons> d_ipc;
  /** An eager proof generator for lemmas */
  std::unique_ptr<EagerProofGenerator> d_lemPg;
};

}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal

#endif

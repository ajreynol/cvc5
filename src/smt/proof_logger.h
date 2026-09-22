/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof logger utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__PROOF_LOGGER_H
#define CVC5__SMT__PROOF_LOGGER_H

#include <string>
#include <unordered_set>

#include "context/cdhashset.h"
#include "proof/eo/eo_node_converter.h"
#include "proof/eo/eo_printer.h"
#include "proof/proof_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

namespace smt {
class Assertions;
class PfManager;
class ProofPostprocess;
}  // namespace smt

/**
 * The purpose of this class is to output proofs for all reasoning the solver
 * does on-the-fly. It is enabled when proof logging is enabled.
 *
 * This class receives notifications for three things:
 * (1) When preprocessing has completed, determining the set of input clauses.
 * (2) When theory lemmas are learned
 * (3) When a SAT refutation is derived.
 *
 * Dependending on the proof mode, the notifications for the above three things
 * may be in the form of ProofNode (if proofs are enabled for that component),
 * or Node (if proofs are disabled for that component).
 *
 * As with dumped proofs, the granularity of the proofs is subject to the
 * option `proof-granularity`.
 */
class ProofLogger : protected EnvObj
{
 public:
  /** */
  ProofLogger(Env& env) : EnvObj(env) {}
  virtual ~ProofLogger() {}
  /**
   * Called when preprocessing is complete with the list of input clauses,
   * after preprocessing and conversion to CNF.
   * @param input The list of input clauses.
   */
  virtual void logCnfPreprocessInputs(
      CVC5_UNUSED const std::vector<Node>& inputs)
  {
  }
  /**
   * Called when preprocessing is complete with the proofs of the preprocessed
   * inputs. The free assumptions of proofs in pfns are the preprocessed input
   * formulas. If preprocess proofs are avialable, this method connects pfn to
   * the original input formulas.
   * @param pfns Proofs of the preprocessed inputs.
   */
  virtual void logCnfPreprocessInputProofs(
      CVC5_UNUSED std::vector<std::shared_ptr<ProofNode>>& pfns)
  {
  }
  /**
   * Called when clause `n` is added to the SAT solver, where `n` is
   * (the CNF conversion of) a theory lemma.
   * @param n The theory lemma.
   */
  virtual void logTheoryLemma(CVC5_UNUSED const Node& n) {}
  /**
   * Called when clause `pfn` is added to the SAT solver, where `pfn`
   * is a closed proof of (the CNF conversion of) a theory lemma.
   * @param pfn The closed proof of a theory lemma.
   */
  virtual void logTheoryLemmaProof(CVC5_UNUSED std::shared_ptr<ProofNode>& pfn)
  {
  }
  /**
   * Called when the SAT solver derives false. The SAT refutation should be
   * derivable by propositional reasoning via the notified preprocessed input
   * and theory lemmas as given above.
   */
  virtual void logSatRefutation() {}

  /**
   * Called when the SAT solver generates a proof of false. The free assumptions
   * of this proof is the union of the CNF conversion of input and theory lemmas
   * as notified above.
   * @param pfn The refutation proof.
   */
  virtual void logSatRefutationProof(
      CVC5_UNUSED std::shared_ptr<ProofNode>& pfn)
  {
  }
  /** Called when the user issues a push command. */
  virtual void notifyPush() {}
  /** Called when the user issues a pop command. */
  virtual void notifyPop() {}
};

/**
 * The default implementation of a proof logger, which prints proofs in the
 * CPC format.
 */
class ProofLoggerCpc : public ProofLogger
{
 public:
  /** */
  ProofLoggerCpc(Env& env,
                 std::ostream& out,
                 smt::PfManager* pm,
                 smt::Assertions& as);
  ~ProofLoggerCpc();
  /** Log preprocessing input */
  void logCnfPreprocessInputs(const std::vector<Node>& inputs) override;
  /** Log preprocessing input proof */
  void logCnfPreprocessInputProofs(
      std::vector<std::shared_ptr<ProofNode>>& pfns) override;
  /** Log theory lemma */
  void logTheoryLemma(const Node& n) override;
  /** Log theory lemma proof */
  void logTheoryLemmaProof(std::shared_ptr<ProofNode>& pfn) override;
  /** Log SAT refutation */
  void logSatRefutation() override;
  /** Log SAT refutation proof */
  void logSatRefutationProof(std::shared_ptr<ProofNode>& pfn) override;
  /** Notify that the user pushed a context. */
  void notifyPush() override;
  /** Notify that the user popped a context. */
  void notifyPop() override;

 private:
  /** Synchronize the emitted script context with the current user level. */
  void syncScriptContext();
  /** Print only declaration/definition lines that have not been printed yet. */
  void printDeclarationsOnce(const std::vector<Node>& definitions,
                             const std::vector<Node>& assertions);
  /** Mark that we emitted proof script output. */
  void notifyOutput();
  /** Are we streaming a single incremental dump-proofs CPC script? */
  bool d_isIncrementalDump;
  /** Have we already printed an exit command? */
  bool d_printedExit;
  /** Has this logger emitted any output? */
  bool d_hasOutput;
  /** The current level of the emitted script context. */
  uint32_t d_scriptLevel;
  /** Context for tracking which clauses have been emitted in the script. */
  context::Context d_scriptCtx;
  /** The set of input clauses already emitted for the current script scope. */
  context::CDHashSet<Node> d_printedInputs;
  /** The set of lemma clauses already emitted for the current script scope. */
  context::CDHashSet<Node> d_printedLemmas;
  /** Preamble commands that were already emitted. */
  std::unordered_set<std::string> d_preambleLines;
  /** Pointer to the proof manager, for connecting proofs to inputsw */
  smt::PfManager* d_pm;
  /** Pointer to the proof node manager */
  ProofNodeManager* d_pnm;
  /** Reference to the assertions of SMT solver */
  smt::Assertions& d_as;
  /** The node converter, used for printing */
  proof::EoNodeConverter d_atp;
  /** The proof printer */
  proof::EoPrinter d_eop;
  /** The output channel we are using */
  proof::EoPrintChannelOut d_eout;
  /** The preprocessing proof we were notified of, which we may have created */
  std::shared_ptr<ProofNode> d_ppProof;
  /**
   * The list of theory lemma proofs we were notified of, which we may have
   * created.
   */
  std::vector<std::shared_ptr<ProofNode>> d_lemmaPfs;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__PROOF_LOGGER_H */

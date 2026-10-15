/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory engine of the ported Z3 core.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__Z3_THEORY_ENGINE_H
#define CVC5__Z3__Z3_THEORY_ENGINE_H

#include <memory>
#include <vector>

#include "theory/theory_engine.h"
#include "z3/host_core.h"
#include "z3/shared_backend.h"

namespace cvc5::internal {
namespace z3 {

/**
 * The theory engine used with --z3, paired by smt::EngineFactory with
 * Z3PropEngine, or, with --z3-prop-engine=cvc5, with Z3HostedPropEngine.
 *
 * The theory reasoning of the search happens in the theory side of the
 * ported core, SmtContext, which this class owns, with the propositional
 * side, through its SharedBackend; see that class for how their lifetime
 * follows this engine's.
 *
 * The inherited TheoryEngine, with cvc5's theories, is kept as a service to
 * cvc5's preprocessing, which uses it for theory rewriting and
 * preprocessing, static learning, solving equalities and sort inference, and
 * through which the theory rewriters are registered. It also holds what
 * preprocessing reports through setRefutationUnsound and setModelUnsound,
 * which Z3PropEngine applies to the result of the search. The theories never
 * receive an assertion, so anything else asked of them is not about the
 * problem. The commands that would ask are refused through
 * Z3PropEngine::supports, and the options through
 * SetDefaults::checkZ3Capabilities.
 *
 * Hosted (--z3-prop-engine=cvc5), this class also implements the search
 * contract that cvc5's prop engine uses (preRegister, assertFact, check,
 * propagations, explanations), through HostCore, with what the core learns
 * sent to the prop engine directly.
 */
class Z3TheoryEngine : public TheoryEngine
{
 public:
  Z3TheoryEngine(Env& env, bool hosted = false);
  ~Z3TheoryEngine() override;
  /** Get the state shared with the paired Z3PropEngine. */
  SharedBackend& getBackend() { return d_backend; }
  /** The core under cvc5's prop engine, hosted. */
  HostCore& getCore() { return *d_core; }
  /** Whether cvc5's prop engine drives this engine. */
  bool isHosted() const { return d_hosted; }

  // ------------------------------------------- the search contract, hosted
  void preRegister(TNode atom) override;
  void assertFact(TNode literal) override;
  void check(theory::Theory::Effort effort) override;
  bool presolve() override;
  void postsolve(prop::SatValue result) override;
  void notifyRestart() override;
  void getPropagatedLiterals(std::vector<TNode>& literals) override;
  Node getNextDecisionRequest() override;
  TrustNode getExplanation(TNode literal) override;
  bool needCheck() const override;

 private:
  /** Sends what the core learns to the prop engine directly. */
  class Output : public HostCoreOutput
  {
   public:
    Output(Z3TheoryEngine& te) : d_te(te) {}
    void lemma(const Node& lem,
               theory::LemmaProperty p,
               bool notifyDecisions) override;
    void propagate(const Node& lit) override;
    void preferPhase(TNode atom, bool phase) override;
    void setModelUnsound(theory::IncompleteId id) override;

   private:
    Z3TheoryEngine& d_te;
  };

  /** The ported core. */
  SharedBackend d_backend;
  /** Whether cvc5's prop engine drives this engine. */
  bool d_hosted;
  /** The output of the core, hosted. */
  Output d_output;
  /** The core under cvc5's prop engine, hosted. */
  std::unique_ptr<HostCore> d_core;
  /** The propagations not yet given to cvc5. */
  std::vector<Node> d_propagations;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__Z3_THEORY_ENGINE_H */

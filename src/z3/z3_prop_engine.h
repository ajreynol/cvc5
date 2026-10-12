/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The propositional engine of the ported Z3 core.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__Z3_PROP_ENGINE_H
#define CVC5__Z3__Z3_PROP_ENGINE_H

#include "prop/prop_engine.h"
#include "z3/assertion_preparation.h"

namespace cvc5::internal {
namespace z3 {

class SharedBackend;
class Z3TheoryEngine;

/**
 * The propositional engine used with --z3, paired with Z3TheoryEngine by
 * smt::EngineFactory.
 *
 * This implements the search contract of PropEngine by running the search of
 * the ported core, in the SmtContext shared with the theory engine; see
 * SharedBackend. SmtSolver drives it as it drives cvc5's own engine:
 * preprocessed assertions arrive through assertInputFormulas, where they are
 * prepared for the core (see AssertionPreparation) in place of the CNF
 * conversion, and checkSat translates the outcome of the search into a
 * Result, applying what preprocessing reported to the theory engine about
 * its soundness.
 *
 * The inherited PropEngine is kept as a service to cvc5's preprocessing,
 * which uses it for theory preprocessing, term formula removal and the
 * notification of top-level substitutions. Its SAT solver never searches, so
 * nothing else asked of it is about the problem. The commands that would ask
 * are refused through supports, and the options through
 * SetDefaults::checkZ3Capabilities.
 */
class Z3PropEngine : public prop::PropEngine
{
 public:
  Z3PropEngine(Env& env, Z3TheoryEngine* te);
  ~Z3PropEngine() override;

  /** Replace the SmtContext of the shared backend with a fresh one. */
  void finishInit() override;
  /**
   * Prepare the assertions for the core and assert them. The skolem map is
   * not used: the core has no decision heuristic that distinguishes skolem
   * definitions from other assertions.
   */
  void assertInputFormulas(
      const std::vector<Node>& assertions,
      std::unordered_map<size_t, Node>& skolemMap) override;
  /** Run the search of the core. */
  Result checkSat() override;
  void push() override;
  void pop() override;
  /** Backtrack the core to its base level. */
  void resetTrail() override;
  /** The number of user scopes of the core. */
  uint32_t getAssertionLevel() const override;
  void interrupt() override;
  /** None of the optional features are supported; see the implementation. */
  bool supports(prop::SearchFeature f) const override;

 private:
  /** The paired theory engine. */
  Z3TheoryEngine* d_te;
  /** The state shared with d_te, which owns it. */
  SharedBackend& d_backend;
  /** The preparation of assertions for the core. */
  AssertionPreparation d_prep;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__Z3_PROP_ENGINE_H */

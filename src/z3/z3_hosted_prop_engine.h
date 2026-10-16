/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * cvc5's propositional engine over the theory engine of the ported Z3 core.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__Z3_HOSTED_PROP_ENGINE_H
#define CVC5__Z3__Z3_HOSTED_PROP_ENGINE_H

#include "prop/prop_engine.h"
#include "z3/assertion_preparation.h"

namespace cvc5::internal {
namespace z3 {

class HostCore;
class SharedBackend;

/**
 * The propositional engine used with --z3: cvc5's own PropEngine (CNF
 * conversion, CDCL(T) solver, decision heuristic), over cvc5's TheoryEngine
 * with the ported core in its quantifiers engine (Z3QuantifiersEngine).
 *
 * It differs from PropEngine only in its input: the preprocessed assertions
 * are first prepared for the core (AssertionPreparation), and the prepared
 * formulas go both to the core's propositional side, which mirrors the
 * search for the theory side, and to cvc5's CNF conversion.
 */
class Z3HostedPropEngine : public prop::PropEngine
{
 public:
  /**
   * @param te The paired theory engine.
   * @param backend The ported core.
   * @param core The core under cvc5's prop engine, which te drives.
   */
  Z3HostedPropEngine(Env& env,
                     TheoryEngine* te,
                     SharedBackend& backend,
                     HostCore& core);
  ~Z3HostedPropEngine() override;

  /** Make a fresh core. */
  void finishInit() override;
  /**
   * Prepare the assertions for the core, assert them to it, and convert the
   * prepared formulas. The skolem map is not passed on, since its indices
   * refer to the assertions before preparation; skolem definitions are then
   * ordinary assertions for the decision heuristic.
   */
  void assertInputFormulas(
      const std::vector<Node>& assertions,
      std::unordered_map<size_t, Node>& skolemMap) override;
  /** The core supports none of the optional features. */
  bool supports(prop::SearchFeature f) const override;

 private:
  /** The paired theory engine. */
  TheoryEngine* d_te;
  /** The ported core. */
  SharedBackend& d_backend;
  /** The core under cvc5's prop engine. */
  HostCore& d_core;
  /** The preparation of assertions for the core. */
  AssertionPreparation d_prep;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__Z3_HOSTED_PROP_ENGINE_H */

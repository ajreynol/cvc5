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

#include "theory/theory_engine.h"
#include "z3/shared_backend.h"

namespace cvc5::internal {
namespace z3 {

/**
 * The theory engine used with --z3, paired with Z3PropEngine by
 * smt::EngineFactory.
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
 */
class Z3TheoryEngine : public TheoryEngine
{
 public:
  Z3TheoryEngine(Env& env);
  ~Z3TheoryEngine() override;
  /** Get the state shared with the paired Z3PropEngine. */
  SharedBackend& getBackend() { return d_backend; }

 private:
  /** The ported core. */
  SharedBackend d_backend;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__Z3_THEORY_ENGINE_H */

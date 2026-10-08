/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An alternative solver for SMT queries that runs a port of Z3's SMT core.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__Z3_SMT_SOLVER_H
#define CVC5__SMT__Z3_SMT_SOLVER_H

#include <memory>

#include "smt/smt_solver.h"
#include "z3/params.h"

namespace cvc5::internal {

namespace z3 {
class SmtContext;
}

namespace smt {

/**
 * A solver for SMT queries that replaces cvc5's CDCL(T) engine with a port of
 * Z3's SMT core, enabled by the --z3 option.
 *
 * Preprocessing, the term representation and the rewriter are cvc5's: this
 * class takes the output of cvc5's Preprocessor and, instead of handing it to
 * the PropEngine, internalizes it into a z3::SmtContext. That context owns the
 * search: its own CDCL loop, congruence closure, relevancy propagation,
 * case-split queue and E-matching engine, all ported from Z3.
 *
 * The TheoryEngine and PropEngine that the base class builds are still
 * constructed, since the preprocessor and the model-building paths of
 * SolverEngine are written against them, but the PropEngine is not used to
 * search.
 */
class Z3SmtSolver : public SmtSolver
{
 public:
  Z3SmtSolver(Env& env, SolverEngineStatistics& stats);
  ~Z3SmtSolver() override;

  void finishInit() override;
  void resetAssertions() override;
  void interrupt() override;
  void pushPropContext() override;
  void popPropContext() override;
  void resetTrail() override;
  /** Internalize the preprocessed assertions into the Z3 core. */
  void assertToInternal(preprocessing::AssertionPipeline& ap) override;
  /** Run the Z3 core's search. */
  Result checkSatInternal() override;

 private:
  /** The parameters of the Z3 core, defaulted as in Z3. */
  z3::Params d_params;
  /** The Z3 core. */
  std::unique_ptr<z3::SmtContext> d_ctx;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif /* CVC5__SMT__Z3_SMT_SOLVER_H */

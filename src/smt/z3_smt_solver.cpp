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

#include "smt/z3_smt_solver.h"

#include "preprocessing/assertion_pipeline.h"
#include "smt/env.h"
#include "smt/logic_exception.h"

namespace cvc5::internal {
namespace smt {

Z3SmtSolver::Z3SmtSolver(Env& env, SolverEngineStatistics& stats)
    : SmtSolver(env, stats), d_ctx(nullptr)
{
  d_params.initialize(env.getOptions());
}

Z3SmtSolver::~Z3SmtSolver() {}

void Z3SmtSolver::finishInit()
{
  // Build the TheoryEngine and PropEngine, which the preprocessor and the
  // model-building paths still require.
  SmtSolver::finishInit();
}

void Z3SmtSolver::resetAssertions() { SmtSolver::resetAssertions(); }

void Z3SmtSolver::interrupt() { SmtSolver::interrupt(); }

void Z3SmtSolver::pushPropContext() {}

void Z3SmtSolver::popPropContext() {}

void Z3SmtSolver::resetTrail() {}

void Z3SmtSolver::assertToInternal(preprocessing::AssertionPipeline& ap) {}

Result Z3SmtSolver::checkSatInternal()
{
  throw LogicException(
      "The ported Z3 core (--z3) is not yet able to answer check-sat.");
}

}  // namespace smt
}  // namespace cvc5::internal

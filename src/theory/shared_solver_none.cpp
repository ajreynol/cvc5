/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The shared solver of --ee-mode=none.
 */

#include "theory/shared_solver_none.h"

#include "theory/theory_engine.h"

namespace cvc5::internal {
namespace theory {

SharedSolverNone::SharedSolverNone(Env& env, TheoryEngine& te)
    : SharedSolver(env, te)
{
}

void SharedSolverNone::setEqualityEngine(CVC5_UNUSED eq::EqualityEngine* ee)
{
  Unreachable() << "SharedSolverNone has no equality engine";
}

TrustNode SharedSolverNone::explain(TNode literal, TheoryId id)
{
  Assert(id != THEORY_BUILTIN);
  return d_te.theoryOf(id)->explain(literal);
}

void SharedSolverNone::assertShared(CVC5_UNUSED TNode n,
                                    CVC5_UNUSED bool polarity,
                                    TNode reason)
{
  d_te.theoryOf(THEORY_BUILTIN)->assertFact(reason, true);
}

void SharedSolverNone::preRegisterSharedInternal(CVC5_UNUSED TNode t) {}

}  // namespace theory
}  // namespace cvc5::internal

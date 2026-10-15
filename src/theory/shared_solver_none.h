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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SHARED_SOLVER_NONE__H
#define CVC5__THEORY__SHARED_SOLVER_NONE__H

#include "expr/node.h"
#include "theory/shared_solver.h"

namespace cvc5::internal {
namespace theory {

/**
 * The shared solver when there are no equality engines (--ee-mode=none). It
 * keeps no shared terms, since the theory solvers of that mode share their
 * own equality reasoning: terms are preregistered as without sharing, and
 * the equalities TheoryEngine hands to the shared solver are asserted to
 * THEORY_BUILTIN.
 */
class SharedSolverNone : public SharedSolver
{
 public:
  SharedSolverNone(Env& env, TheoryEngine& te);
  ~SharedSolverNone() {}
  void setEqualityEngine(eq::EqualityEngine* ee) override;
  /** Ask the theory that propagated literal for its explanation. */
  TrustNode explain(TNode literal, TheoryId id) override;
  /** Assert reason to THEORY_BUILTIN. */
  void assertShared(TNode n, bool polarity, TNode reason) override;

 protected:
  void preRegisterSharedInternal(TNode t) override;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SHARED_SOLVER_NONE__H */

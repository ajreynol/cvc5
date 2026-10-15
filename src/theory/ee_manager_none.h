/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The equality engine manager of --ee-mode=none.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__EE_MANAGER_NONE__H
#define CVC5__THEORY__EE_MANAGER_NONE__H

#include "theory/ee_manager.h"

namespace cvc5::internal {
namespace theory {

/**
 * Allocates no equality engine, for theory solvers that keep their own
 * equality reasoning: the components of the ported Z3 core, which share one
 * E-graph (see src/z3/ARCHITECTURE_PLAN.md, section 16). A theory that asks
 * for an equality engine is an error.
 */
class EqEngineManagerNone : public EqEngineManager
{
 public:
  EqEngineManagerNone(Env& env, TheoryEngine& te, SharedSolver& shs);
  ~EqEngineManagerNone() {}
  /** Record that no theory has an equality engine. */
  void initializeTheories() override;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__EE_MANAGER_NONE__H */

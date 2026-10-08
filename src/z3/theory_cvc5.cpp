/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bridges from cvc5's own theory solvers into the ported Z3 core.
 */

#include "z3/theory_cvc5.h"

namespace cvc5::internal {
namespace z3 {

Theory* mkTheoryArithBridge(SmtContext& ctx) { return nullptr; }

Theory* mkTheoryBvBridge(SmtContext& ctx) { return nullptr; }

}  // namespace z3
}  // namespace cvc5::internal

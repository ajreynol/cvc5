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
 *
 * Unlike the rest of src/z3, nothing here is ported from Z3: these are
 * adapters that let cvc5's bit-vector and arithmetic solvers act as plugins
 * behind z3::Theory, so that only the parts of Z3 that matter for quantifier
 * performance -- the CDCL core, relevancy, congruence closure and E-matching
 * -- are duplicated.
 *
 * Status: not implemented yet. While a bridge is absent, the core treats the
 * theory's terms as uninterpreted, which drops constraints rather than adding
 * them: an "unsat" answer stays sound, and a satisfying assignment is
 * reported as "unknown" (see SmtContext::markModelUnsound).
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__THEORY_CVC5_H
#define CVC5__Z3__THEORY_CVC5_H

namespace cvc5::internal {
namespace z3 {

class SmtContext;
class Theory;

/**
 * Create the bridge to cvc5's arithmetic solver, or null if the bridge is
 * unavailable.
 */
Theory* mkTheoryArithBridge(SmtContext& ctx);

/**
 * Create the bridge to cvc5's bit-vector solver, or null if the bridge is
 * unavailable.
 */
Theory* mkTheoryBvBridge(SmtContext& ctx);

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__THEORY_CVC5_H */

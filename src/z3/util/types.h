/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Basic types for the ported Z3 SMT engine.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_types.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__TYPES_H
#define CVC5__Z3__UTIL__TYPES_H

#include <vector>

#include "prop/sat_solver_types.h"

namespace cvc5::internal {
namespace z3 {

/** A lifted Boolean, as cvc5's SAT solvers have: true, false or unknown. */
using prop::SAT_VALUE_FALSE;
using prop::SAT_VALUE_TRUE;
using prop::SAT_VALUE_UNKNOWN;
using prop::SatValue;

class ENode;

using ENodeVector = std::vector<ENode*>;

class SmtContext;

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__TYPES_H */

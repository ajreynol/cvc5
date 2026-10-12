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

#include "z3/z3_theory_engine.h"

namespace cvc5::internal {
namespace z3 {

Z3TheoryEngine::Z3TheoryEngine(Env& env) : TheoryEngine(env), d_backend(env) {}

Z3TheoryEngine::~Z3TheoryEngine() {}

}  // namespace z3
}  // namespace cvc5::internal

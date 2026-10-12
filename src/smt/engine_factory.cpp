/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Construction of the theory and propositional engines of an SmtSolver.
 */

#include "smt/engine_factory.h"

#include "options/z3_options.h"
#include "prop/prop_engine.h"
#include "smt/env.h"
#include "theory/theory_engine.h"
#include "z3/z3_prop_engine.h"
#include "z3/z3_theory_engine.h"

namespace cvc5::internal {
namespace smt {

std::unique_ptr<TheoryEngine> EngineFactory::mkTheoryEngine(Env& env)
{
  if (env.getOptions().z3.z3)
  {
    return std::make_unique<z3::Z3TheoryEngine>(env);
  }
  return std::make_unique<TheoryEngine>(env);
}

std::unique_ptr<prop::PropEngine> EngineFactory::mkPropEngine(Env& env,
                                                              TheoryEngine* te)
{
  if (env.getOptions().z3.z3)
  {
    Assert(dynamic_cast<z3::Z3TheoryEngine*>(te) != nullptr);
    return std::make_unique<z3::Z3PropEngine>(
        env, static_cast<z3::Z3TheoryEngine*>(te));
  }
  return std::make_unique<prop::PropEngine>(env, te);
}

}  // namespace smt
}  // namespace cvc5::internal

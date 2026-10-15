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
#include "z3/theory_slot.h"
#include "z3/z3_hosted_prop_engine.h"
#include "z3/z3_prop_engine.h"
#include "z3/z3_theory_engine.h"

namespace cvc5::internal {
namespace smt {

std::unique_ptr<TheoryEngine> EngineFactory::mkTheoryEngine(Env& env)
{
  if (env.getOptions().z3.z3)
  {
    if (env.getOptions().z3.z3TheoryEngine == options::Z3TheoryEngineMode::CVC5)
    {
      // cvc5's own theory engine, with the port's components in its theory
      // slots (addTheories)
      return std::make_unique<TheoryEngine>(env);
    }
    // With cvc5's prop engine, the theory engine is driven through the
    // search contract of TheoryEngine itself.
    bool hosted =
        env.getOptions().z3.z3PropEngine == options::Z3PropEngineMode::CVC5;
    return std::make_unique<z3::Z3TheoryEngine>(env, hosted);
  }
  return std::make_unique<TheoryEngine>(env);
}

bool EngineFactory::addTheories(Env& env, TheoryEngine* te)
{
  if (env.getOptions().z3.z3
      && env.getOptions().z3.z3TheoryEngine
             == options::Z3TheoryEngineMode::CVC5)
  {
    z3::addTheorySlots(env, *te);
    return true;
  }
  return false;
}

std::unique_ptr<prop::PropEngine> EngineFactory::mkPropEngine(Env& env,
                                                              TheoryEngine* te)
{
  if (env.getOptions().z3.z3)
  {
    if (env.getOptions().z3.z3TheoryEngine == options::Z3TheoryEngineMode::CVC5)
    {
      z3::SlotBackend& sb = z3::getSlotBackend(*te);
      return std::make_unique<z3::Z3HostedPropEngine>(
          env, te, sb.getBackend(), sb.getCore());
    }
    Assert(dynamic_cast<z3::Z3TheoryEngine*>(te) != nullptr);
    z3::Z3TheoryEngine* zte = static_cast<z3::Z3TheoryEngine*>(te);
    if (zte->isHosted())
    {
      return std::make_unique<z3::Z3HostedPropEngine>(
          env, te, zte->getBackend(), zte->getCore());
    }
    return std::make_unique<z3::Z3PropEngine>(env, zte);
  }
  return std::make_unique<prop::PropEngine>(env, te);
}

}  // namespace smt
}  // namespace cvc5::internal

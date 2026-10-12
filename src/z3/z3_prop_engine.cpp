/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The propositional engine of the ported Z3 core.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "z3/z3_prop_engine.h"

#include "options/base_options.h"
#include "smt/env.h"
#include "z3/shared_backend.h"
#include "z3/smt_context.h"
#include "z3/z3_theory_engine.h"

namespace cvc5::internal {
namespace z3 {

Z3PropEngine::Z3PropEngine(Env& env, Z3TheoryEngine* te)
    : PropEngine(env, te), d_te(te), d_backend(te->getBackend()), d_prep(env)
{
}

Z3PropEngine::~Z3PropEngine() {}

void Z3PropEngine::finishInit()
{
  PropEngine::finishInit();
  // A new propositional engine is made when the engines are first made and
  // on reset-assertions, and either way the search starts over.
  d_backend.resetContext();
}

void Z3PropEngine::assertInputFormulas(
    const std::vector<Node>& assertions,
    std::unordered_map<size_t, Node>& /* skolemMap */)
{
  d_prep.apply(d_backend.getContext(), assertions);
}

Result Z3PropEngine::checkSat()
{
  if (options().base.preprocessOnly)
  {
    return Result(Result::UNKNOWN, UnknownExplanation::REQUIRES_FULL_CHECK);
  }
  SmtContext& ctx = d_backend.getContext();
  LBool r = ctx.check();
  if (r == L_TRUE)
  {
    // as in PropEngine::checkSat, a model that preprocessing may have made
    // unsound is not a model of the input
    if (d_te->isModelUnsound())
    {
      verbose(1) << "z3: unknown: model unsound: " << d_te->getModelUnsoundId()
                 << std::endl;
      return Result(Result::UNKNOWN, UnknownExplanation::INCOMPLETE);
    }
    return Result(Result::SAT);
  }
  if (r == L_FALSE)
  {
    if (d_te->isRefutationUnsound())
    {
      verbose(1) << "z3: unknown: refutation unsound: "
                 << d_te->getRefutationUnsoundId() << std::endl;
      return Result(Result::UNKNOWN, UnknownExplanation::INCOMPLETE);
    }
    return Result(Result::UNSAT);
  }
  verbose(1) << "z3: unknown: " << ctx.getLastSearchFailure() << ": "
             << ctx.getReasonUnknown() << std::endl;
  UnknownExplanation why = UnknownExplanation::UNKNOWN_REASON;
  switch (ctx.getLastSearchFailure())
  {
    case MEMOUT:
    case RESOURCE_LIMIT: why = UnknownExplanation::RESOURCEOUT; break;
    case CANCELED: why = UnknownExplanation::INTERRUPTED; break;
    case NUM_CONFLICTS:
    case THEORY:
    case QUANTIFIERS: why = UnknownExplanation::INCOMPLETE; break;
    default: break;
  }
  return Result(Result::UNKNOWN, why);
}

void Z3PropEngine::push() { d_backend.getContext().push(); }

void Z3PropEngine::pop() { d_backend.getContext().pop(1); }

void Z3PropEngine::resetTrail()
{
  if (d_backend.hasContext())
  {
    d_backend.getContext().popToBaseLvl();
  }
}

uint32_t Z3PropEngine::getAssertionLevel() const
{
  return d_backend.getContext().getBaseLevel();
}

void Z3PropEngine::interrupt()
{
  if (d_backend.hasContext())
  {
    d_backend.getContext().interrupt();
  }
}

}  // namespace z3
}  // namespace cvc5::internal

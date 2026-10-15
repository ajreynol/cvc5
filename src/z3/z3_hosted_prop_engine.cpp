/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * cvc5's propositional engine over the theory engine of the ported Z3 core.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "z3/z3_hosted_prop_engine.h"

#include "prop/cnf_stream.h"
#include "z3/host_core.h"
#include "z3/shared_backend.h"
#include "z3/smt_context.h"

namespace cvc5::internal {
namespace z3 {

Z3HostedPropEngine::Z3HostedPropEngine(Env& env,
                                       TheoryEngine* te,
                                       SharedBackend& backend,
                                       HostCore& core)
    // Boolean variables are asserted to the theory engine like atoms: the
    // core derives the values of its gates from those of their leaves, for
    // relevancy, and Boolean variables are leaves.
    : PropEngine(env, te, prop::FormulaLitPolicy::TRACK_AND_NOTIFY_VAR),
      d_backend(backend),
      d_core(core),
      d_prep(env)
{
}

Z3HostedPropEngine::~Z3HostedPropEngine() {}

void Z3HostedPropEngine::finishInit()
{
  PropEngine::finishInit();
  d_backend.resetContext();
  d_core.reset();
}

void Z3HostedPropEngine::assertInputFormulas(
    const std::vector<Node>& assertions,
    std::unordered_map<size_t, Node>& /* skolemMap */)
{
  std::vector<Node> prepared;
  d_prep.apply(
      d_backend.getContext(), d_backend.getPropCore(), assertions, &prepared);
  std::unordered_map<size_t, Node> noSkolems;
  PropEngine::assertInputFormulas(prepared, noSkolems);
}

bool Z3HostedPropEngine::supports(prop::SearchFeature /* f */) const
{
  return false;
}

}  // namespace z3
}  // namespace cvc5::internal

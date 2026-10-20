/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module of the theory engine that gives the ported Z3 core the
 * assignment of the SAT solver.
 */

#include "z3/relevancy_tracker.h"

#include "theory/theory_state.h"
#include "z3/host_core.h"

namespace cvc5::internal {
namespace z3 {

RelevancyTracker::RelevancyTracker(Env& env,
                                   TheoryEngine* engine,
                                   HostCore& core)
    : TheoryEngineModule(env, engine, "z3::RelevancyTracker"),
      d_core(core),
      d_facts(context()),
      d_factsHead(context(), 0)
{
}

void RelevancyTracker::notifyFact(TNode literal) { d_facts.push_back(literal); }

void RelevancyTracker::flush(const theory::TheoryState& state)
{
  while (d_factsHead < d_facts.size() && !state.isInConflict())
  {
    size_t i = d_factsHead;
    d_factsHead = i + 1;
    d_core.assertFact(d_facts[i]);
  }
}

}  // namespace z3
}  // namespace cvc5::internal

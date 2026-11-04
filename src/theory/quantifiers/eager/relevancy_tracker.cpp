/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module of the theory engine that gives the eager E-matching core the
 * assignment of the SAT solver.
 */

#include "theory/quantifiers/eager/relevancy_tracker.h"

#include "theory/quantifiers/eager/eager_e_matching.h"
#include "theory/theory_state.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

RelevancyTracker::RelevancyTracker(Env& env,
                                   TheoryEngine* engine,
                                   EagerEMatching& core)
    : TheoryEngineModule(env, engine, "quantifiers::eager::RelevancyTracker"),
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

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The equality engine manager of --ee-mode=none.
 */

#include "theory/ee_manager_none.h"

#include "theory/shared_solver.h"
#include "theory/theory_engine.h"

namespace cvc5::internal {
namespace theory {

EqEngineManagerNone::EqEngineManagerNone(Env& env,
                                         TheoryEngine& te,
                                         SharedSolver& shs)
    : EqEngineManager(env, te, shs)
{
}

void EqEngineManagerNone::initializeTheories()
{
  EeSetupInfo esis;
  if (d_sharedSolver.needsEqualityEngine(esis))
  {
    Unhandled() << "The shared solver requires an equality engine, which "
                   "--ee-mode=none does not provide";
  }
  for (TheoryId theoryId = theory::THEORY_FIRST;
       theoryId != theory::THEORY_LAST;
       ++theoryId)
  {
    Theory* t = d_te.theoryOf(theoryId);
    if (t == nullptr)
    {
      continue;
    }
    // no equality engine
    d_einfo[theoryId];
    EeSetupInfo esi;
    if (t->needsEqualityEngine(esi))
    {
      Unhandled() << "Theory " << theoryId
                  << " requires an equality engine, which --ee-mode=none does "
                     "not provide";
    }
  }
}

}  // namespace theory
}  // namespace cvc5::internal

/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of relevance manager.
 */

#include "theory/sub_conflict_find.h"

#include "options/smt_options.h"
#include "options/theory_options.h"
#include "proof/unsat_core.h"
#include "smt/set_defaults.h"
#include "theory/theory_engine.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

SubConflictFind::SubConflictFind(Env& env, TheoryEngine* engine)
    : TheoryEngineModule(env, engine, "SubConflictFind")
{
  // determine the options to use for the verification subsolvers we spawn
  // we start with the provided options
  d_subOptions.copyValues(options());
  // if we are getting theory lemmas, we need proofs
  if (options().theory.subConflictTheoryLem)
  {
    d_subOptions.write_smt().produceProofs = true;
  }
  // want small core so set simplification to none
  d_subOptions.write_smt().simplificationMode =
      options::SimplificationMode::NONE;
  // requires cores
  d_subOptions.write_smt().produceUnsatCores = true;
  // don't do this strategy
  d_subOptions.write_theory().subConflictFind = false;
}

void SubConflictFind::check(Theory::Effort effort)
{
  Theory::Effort erun = options().theory.subConflictLastCall
                            ? Theory::EFFORT_LAST_CALL
                            : Theory::EFFORT_FULL;
  if (effort != erun)
  {
    return;
  }

  double clSet = 0;
  if (TraceIsOn("scf"))
  {
    clSet = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("scf") << "---Subconflict Find Engine Round, effort = " << effort << "---" << std::endl;
  }
  std::vector<Node> assertions;
  const LogicInfo& info = logicInfo();
  for (TheoryId tid = THEORY_FIRST; tid < THEORY_LAST; ++tid)
  {
    if (!info.isTheoryEnabled(tid))
    {
      continue;
    }
    Theory* t = d_engine->theoryOf(tid);
    // collect all assertions from theory
    for (context::CDList<Assertion>::const_iterator it = t->facts_begin(),
                                                    itEnd = t->facts_end();
         it != itEnd;
         ++it)
    {
      Node a = (*it).d_assertion;
      assertions.push_back(a);
    }
  }
  // do subsolver check
  SubsolverSetupInfo ssi(d_env, d_subOptions);
  uint64_t timeout = options().theory.subConflictTimeout;
  initializeSubsolver(
      nodeManager(), d_findConflict, ssi, timeout != 0, timeout);
  // assert and check-sat
  for (const Node& a : assertions)
  {
    d_findConflict->assertFormula(a);
  }
  Trace("scf") << ">>> Check subsolver..." << std::endl;
  Result r = d_findConflict->checkSat();
  Trace("scf") << "<<< ...result is " << r << std::endl;
  size_t addedLemmas = 0;
  if (r.getStatus() == Result::UNSAT)
  {
    addedLemmas = 1;
    // Add the computed unsat core as a conflict, which will cause a backtrack.
    UnsatCore uc = d_findConflict->getUnsatCore();
    Node ucc = nodeManager()->mkAnd(uc.getCore());
    Trace("scf-debug") << "Unsat core is " << ucc << std::endl;
    Trace("scf") << "Core size = " << uc.getCore().size() << std::endl;
    d_out.lemma(ucc.notNode(), InferenceId::SUB_CONFLICT_UC);
    if (options().theory.subConflictTheoryLem)
    {
      // get unsat core theory lemmas
      std::vector<Node> ucl = d_findConflict->getUnsatCoreLemmas();
      Trace("scf") << "Lemma size = " << ucl.size() << std::endl;
      for (const Node& l : ucl)
      {
        // TODO: ensure only over atoms we've seen???
        d_out.lemma(l, InferenceId::SUB_CONFLICT_UC_LEMMA);
      }
      addedLemmas += ucl.size();
    }
  }
  else if (r.getStatus() == Result::SAT)
  {
    d_out.setSubsolverResult(d_findConflict.get());
  }

  if (TraceIsOn("scf"))
  {
    double clSet2 = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("scf") << "Finished subconflict find engine, time = "
                 << (clSet2 - clSet);
    Trace("scf") << ", result = " << r;
    if (addedLemmas > 0)
    {
      Trace("scf") << ", addedLemmas = " << addedLemmas;
    }
    Trace("scf") << std::endl;
  }
}

}  // namespace theory
}  // namespace cvc5::internal

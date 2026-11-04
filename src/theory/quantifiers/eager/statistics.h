/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Statistics of the eager E-matching core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_statistics.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__STATISTICS_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__STATISTICS_H

#include "util/statistics_registry.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

/** The statistics of the core, which cvc5's --stats shows. */
struct Statistics
{
  Statistics(StatisticsRegistry& sr);

  IntStat d_numPropagations;
  IntStat d_numBinPropagations;
  IntStat d_numAddEq;
  IntStat d_numFinalChecks;
  IntStat d_numMkBoolVar;
  IntStat d_numDelBoolVar;
  IntStat d_numMkENode;
  IntStat d_numDelENode;
  IntStat d_numMkClause;
  IntStat d_numDelClause;
  IntStat d_numMkBinClause;
  IntStat d_numMkLits;
  IntStat d_maxGeneration;
  IntStat d_numAssignments;
  /** assertions handed to the core */
  IntStat d_numAssertedFormulas;
  /** skolemizations of quantifiers assigned false */
  IntStat d_numSkolemizations;
  /** quantifier instantiations produced by E-matching */
  IntStat d_numInstances;
  /** instances the checker found already satisfied */
  IntStat d_numInstancesCheckerSat;
  /** instances whose body simplified to true */
  IntStat d_numInstancesSimplifyTrue;
  /** checks at standard and full effort */
  IntStat d_numHostChecks;
  IntStat d_numHostFullChecks;
  /** pops of the core's scopes, and scopes popped */
  IntStat d_numHostPops;
  IntStat d_numHostScopesPopped;
  /** pops to the base level, which are cvc5's restarts */
  IntStat d_numHostRestarts;
  /** lemmas sent, and lemmas not sent again */
  IntStat d_numHostLemmas;
  IntStat d_numHostDuplicateLemmas;
  /** merges of the shadow from cvc5's theories */
  IntStat d_numShadowMerges;
  /** conflicts of the shadow, left to cvc5's theories */
  IntStat d_numShadowConflicts;
  /** lemmas sent weakened, see SmtContext::delayUnit */
  IntStat d_numHostDelayedUnits;
  /** matches that were already instantiated (Z3's missed instantiations) */
  IntStat d_numMissedInstances;
  /** notifyRelevant calls the matcher received */
  IntStat d_numMamNotifyRelevant;
  /** notifyRelevant calls for an enode with arguments */
  IntStat d_numMamRelevantApp;
  /** code trees created */
  IntStat d_numMamTrees;
  /** expressions marked relevant */
  IntStat d_numSetRelevant;
  /** candidates found by the inverted path index when classes merge */
  IntStat d_numMamEqCandidates;
  /** calls to the inverted path index */
  IntStat d_numMamAddEq;
  /** enodes offered to a code tree as E-matching candidates */
  IntStat d_numMamCandidates;
  /** code trees executed */
  IntStat d_numMamExecs;
  /** matches the matching abstract machine reported */
  IntStat d_numMamMatches;
};

inline Statistics::Statistics(StatisticsRegistry& sr)
    : d_numPropagations(
          sr.registerInt("quantifiers::eager::propagations", false)),
      d_numBinPropagations(
          sr.registerInt("quantifiers::eager::binPropagations", false)),
      d_numAddEq(sr.registerInt("quantifiers::eager::addEq", false)),
      d_numFinalChecks(
          sr.registerInt("quantifiers::eager::finalChecks", false)),
      d_numMkBoolVar(sr.registerInt("quantifiers::eager::mkBoolVar", false)),
      d_numDelBoolVar(sr.registerInt("quantifiers::eager::delBoolVar", false)),
      d_numMkENode(sr.registerInt("quantifiers::eager::mkENode", false)),
      d_numDelENode(sr.registerInt("quantifiers::eager::delENode", false)),
      d_numMkClause(sr.registerInt("quantifiers::eager::mkClause", false)),
      d_numDelClause(sr.registerInt("quantifiers::eager::delClause", false)),
      d_numMkBinClause(
          sr.registerInt("quantifiers::eager::mkBinClause", false)),
      d_numMkLits(sr.registerInt("quantifiers::eager::mkLits", false)),
      d_maxGeneration(
          sr.registerInt("quantifiers::eager::maxGeneration", false)),
      d_numAssignments(
          sr.registerInt("quantifiers::eager::assignments", false)),
      d_numAssertedFormulas(
          sr.registerInt("quantifiers::eager::assertedFormulas", false)),
      d_numSkolemizations(
          sr.registerInt("quantifiers::eager::skolemizations", false)),
      d_numInstances(sr.registerInt("quantifiers::eager::instances", false)),
      d_numInstancesCheckerSat(
          sr.registerInt("quantifiers::eager::instancesCheckerSat", false)),
      d_numInstancesSimplifyTrue(
          sr.registerInt("quantifiers::eager::instancesSimplifyTrue", false)),
      d_numHostChecks(sr.registerInt("quantifiers::eager::hostChecks", false)),
      d_numHostFullChecks(
          sr.registerInt("quantifiers::eager::hostFullChecks", false)),
      d_numHostPops(sr.registerInt("quantifiers::eager::hostPops", false)),
      d_numHostScopesPopped(
          sr.registerInt("quantifiers::eager::hostScopesPopped", false)),
      d_numHostRestarts(
          sr.registerInt("quantifiers::eager::hostRestarts", false)),
      d_numHostLemmas(sr.registerInt("quantifiers::eager::hostLemmas", false)),
      d_numHostDuplicateLemmas(
          sr.registerInt("quantifiers::eager::hostDuplicateLemmas", false)),
      d_numShadowMerges(
          sr.registerInt("quantifiers::eager::shadowMerges", false)),
      d_numShadowConflicts(
          sr.registerInt("quantifiers::eager::shadowConflicts", false)),
      d_numHostDelayedUnits(
          sr.registerInt("quantifiers::eager::hostDelayedUnits", false)),
      d_numMissedInstances(
          sr.registerInt("quantifiers::eager::missedInstances", false)),
      d_numMamNotifyRelevant(
          sr.registerInt("quantifiers::eager::mamRelevantEh", false)),
      d_numMamRelevantApp(
          sr.registerInt("quantifiers::eager::mamRelevantApp", false)),
      d_numMamTrees(sr.registerInt("quantifiers::eager::mamTrees", false)),
      d_numSetRelevant(
          sr.registerInt("quantifiers::eager::setRelevant", false)),
      d_numMamEqCandidates(
          sr.registerInt("quantifiers::eager::mamEqCandidates", false)),
      d_numMamAddEq(sr.registerInt("quantifiers::eager::mamAddEq", false)),
      d_numMamCandidates(
          sr.registerInt("quantifiers::eager::mamCandidates", false)),
      d_numMamExecs(sr.registerInt("quantifiers::eager::mamExecs", false)),
      d_numMamMatches(sr.registerInt("quantifiers::eager::mamMatches", false))
{
}

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER__STATISTICS_H */

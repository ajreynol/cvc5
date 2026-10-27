/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Statistics of the ported Z3 SMT core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_statistics.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__STATISTICS_H
#define CVC5__Z3__UTIL__STATISTICS_H

#include "util/statistics_registry.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace z3 {

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
  /** instantiations dropped because their cost exceeded the lazy threshold */
  IntStat d_numLazyInstances;
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
  /** splitting lemmas for relevant, unassigned variables */
  IntStat d_numHostSplits;
  /** merges of the shadow from cvc5's theories */
  IntStat d_numShadowMerges;
  /** conflicts of the shadow, left to cvc5's theories */
  IntStat d_numShadowConflicts;
  /** lemmas sent weakened, see HostCore::delayUnit */
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
    : d_numPropagations(sr.registerInt("z3::propagations", false)),
      d_numBinPropagations(sr.registerInt("z3::binPropagations", false)),
      d_numAddEq(sr.registerInt("z3::addEq", false)),
      d_numFinalChecks(sr.registerInt("z3::finalChecks", false)),
      d_numMkBoolVar(sr.registerInt("z3::mkBoolVar", false)),
      d_numDelBoolVar(sr.registerInt("z3::delBoolVar", false)),
      d_numMkENode(sr.registerInt("z3::mkENode", false)),
      d_numDelENode(sr.registerInt("z3::delENode", false)),
      d_numMkClause(sr.registerInt("z3::mkClause", false)),
      d_numDelClause(sr.registerInt("z3::delClause", false)),
      d_numMkBinClause(sr.registerInt("z3::mkBinClause", false)),
      d_numMkLits(sr.registerInt("z3::mkLits", false)),
      d_maxGeneration(sr.registerInt("z3::maxGeneration", false)),
      d_numAssignments(sr.registerInt("z3::assignments", false)),
      d_numAssertedFormulas(sr.registerInt("z3::assertedFormulas", false)),
      d_numSkolemizations(sr.registerInt("z3::skolemizations", false)),
      d_numInstances(sr.registerInt("z3::instances", false)),
      d_numLazyInstances(sr.registerInt("z3::lazyInstances", false)),
      d_numInstancesCheckerSat(
          sr.registerInt("z3::instancesCheckerSat", false)),
      d_numInstancesSimplifyTrue(
          sr.registerInt("z3::instancesSimplifyTrue", false)),
      d_numHostChecks(sr.registerInt("z3::hostChecks", false)),
      d_numHostFullChecks(sr.registerInt("z3::hostFullChecks", false)),
      d_numHostPops(sr.registerInt("z3::hostPops", false)),
      d_numHostScopesPopped(sr.registerInt("z3::hostScopesPopped", false)),
      d_numHostRestarts(sr.registerInt("z3::hostRestarts", false)),
      d_numHostLemmas(sr.registerInt("z3::hostLemmas", false)),
      d_numHostDuplicateLemmas(
          sr.registerInt("z3::hostDuplicateLemmas", false)),
      d_numHostSplits(sr.registerInt("z3::hostSplits", false)),
      d_numShadowMerges(sr.registerInt("z3::shadowMerges", false)),
      d_numShadowConflicts(sr.registerInt("z3::shadowConflicts", false)),
      d_numHostDelayedUnits(sr.registerInt("z3::hostDelayedUnits", false)),
      d_numMissedInstances(sr.registerInt("z3::missedInstances", false)),
      d_numMamNotifyRelevant(sr.registerInt("z3::mamRelevantEh", false)),
      d_numMamRelevantApp(sr.registerInt("z3::mamRelevantApp", false)),
      d_numMamTrees(sr.registerInt("z3::mamTrees", false)),
      d_numSetRelevant(sr.registerInt("z3::setRelevant", false)),
      d_numMamEqCandidates(sr.registerInt("z3::mamEqCandidates", false)),
      d_numMamAddEq(sr.registerInt("z3::mamAddEq", false)),
      d_numMamCandidates(sr.registerInt("z3::mamCandidates", false)),
      d_numMamExecs(sr.registerInt("z3::mamExecs", false)),
      d_numMamMatches(sr.registerInt("z3::mamMatches", false))
{
}

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__STATISTICS_H */

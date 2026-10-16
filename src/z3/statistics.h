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

#ifndef CVC5__Z3__STATISTICS_H
#define CVC5__Z3__STATISTICS_H

#include <cstdint>
#include <cstring>

namespace cvc5::internal {
namespace z3 {

struct Statistics
{
  uint64_t d_numPropagations;
  uint64_t d_numBinPropagations;
  uint64_t d_numAddEq;
  uint64_t d_numFinalChecks;
  uint64_t d_numMkBoolVar;
  uint64_t d_numDelBoolVar;
  uint64_t d_numMkENode;
  uint64_t d_numDelENode;
  uint64_t d_numMkClause;
  uint64_t d_numDelClause;
  uint64_t d_numMkBinClause;
  uint64_t d_numMkLits;
  uint64_t d_maxGeneration;
  uint64_t d_numAssignments;
  /** assertions handed to the core */
  uint64_t d_numAssertedFormulas;
  /** skolemizations of quantifiers assigned false */
  uint64_t d_numSkolemizations;
  /** quantifier instantiations produced by E-matching */
  uint64_t d_numInstances;
  /** instantiations dropped because their cost exceeded the lazy threshold */
  uint64_t d_numLazyInstances;
  /** instances the checker found already satisfied */
  uint64_t d_numInstancesCheckerSat;
  /** instances whose body simplified to true */
  uint64_t d_numInstancesSimplifyTrue;
  /** checks at standard and full effort */
  uint64_t d_numHostChecks;
  uint64_t d_numHostFullChecks;
  /** pops of the core's scopes, and scopes popped */
  uint64_t d_numHostPops;
  uint64_t d_numHostScopesPopped;
  /** pops to the base level, which are cvc5's restarts */
  uint64_t d_numHostRestarts;
  /** lemmas sent, and lemmas not sent again */
  uint64_t d_numHostLemmas;
  uint64_t d_numHostDuplicateLemmas;
  /** splitting lemmas for relevant, unassigned variables */
  uint64_t d_numHostSplits;
  /** merges of the shadow from cvc5's theories */
  uint64_t d_numShadowMerges;
  /** conflicts of the shadow, left to cvc5's theories */
  uint64_t d_numShadowConflicts;
  /** lemmas sent weakened, see HostCore::delayUnit */
  uint64_t d_numHostDelayedUnits;
  /** matches that were already instantiated (Z3's missed instantiations) */
  uint64_t d_numMissedInstances;
  /** relevantEh calls the matcher received */
  uint64_t d_numMamRelevantEh;
  /** relevantEh calls for an enode with arguments */
  uint64_t d_numMamRelevantApp;
  /** code trees created */
  uint64_t d_numMamTrees;
  /** expressions marked relevant */
  uint64_t d_numSetRelevant;
  /** candidates found by the inverted path index when classes merge */
  uint64_t d_numMamEqCandidates;
  /** calls to the inverted path index */
  uint64_t d_numMamAddEq;
  /** enodes offered to a code tree as E-matching candidates */
  uint64_t d_numMamCandidates;
  /** code trees executed */
  uint64_t d_numMamExecs;
  /** matches the matching abstract machine reported */
  uint64_t d_numMamMatches;

  Statistics() { reset(); }

  void reset() { std::memset(this, 0, sizeof(Statistics)); }
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__STATISTICS_H */

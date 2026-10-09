/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Parameters of the ported Z3 SMT core.
 */

#include "z3/params.h"

#include "options/options.h"
#include "options/z3_options.h"

namespace cvc5::internal {
namespace z3 {

namespace {

CaseSplitStrategy toCaseSplitStrategy(options::Z3CaseSplitMode m)
{
  switch (m)
  {
    case options::Z3CaseSplitMode::ACTIVITY: return CS_ACTIVITY;
    case options::Z3CaseSplitMode::ACTIVITY_DELAY_NEW:
      return CS_ACTIVITY_DELAY_NEW;
    case options::Z3CaseSplitMode::ACTIVITY_WITH_CACHE:
      return CS_ACTIVITY_WITH_CACHE;
    case options::Z3CaseSplitMode::RELEVANCY: return CS_RELEVANCY;
    case options::Z3CaseSplitMode::RELEVANCY_ACTIVITY:
      return CS_RELEVANCY_ACTIVITY;
    case options::Z3CaseSplitMode::RELEVANCY_GOAL: return CS_RELEVANCY_GOAL;
    case options::Z3CaseSplitMode::ACTIVITY_THEORY_AWARE_BRANCHING:
      return CS_ACTIVITY_THEORY_AWARE_BRANCHING;
    default: return CS_ACTIVITY_DELAY_NEW;
  }
}

PhaseSelection toPhaseSelection(options::Z3PhaseSelectionMode m)
{
  switch (m)
  {
    case options::Z3PhaseSelectionMode::ALWAYS_FALSE: return PS_ALWAYS_FALSE;
    case options::Z3PhaseSelectionMode::ALWAYS_TRUE: return PS_ALWAYS_TRUE;
    case options::Z3PhaseSelectionMode::CACHING: return PS_CACHING;
    case options::Z3PhaseSelectionMode::CACHING_CONSERVATIVE:
      return PS_CACHING_CONSERVATIVE;
    case options::Z3PhaseSelectionMode::CACHING_CONSERVATIVE2:
      return PS_CACHING_CONSERVATIVE2;
    case options::Z3PhaseSelectionMode::RANDOM: return PS_RANDOM;
    case options::Z3PhaseSelectionMode::OCCURRENCE: return PS_OCCURRENCE;
    case options::Z3PhaseSelectionMode::THEORY: return PS_THEORY;
    default: return PS_CACHING_CONSERVATIVE;
  }
}

RestartStrategy toRestartStrategy(options::Z3RestartStrategyMode m)
{
  switch (m)
  {
    case options::Z3RestartStrategyMode::GEOMETRIC: return RS_GEOMETRIC;
    case options::Z3RestartStrategyMode::IN_OUT_GEOMETRIC:
      return RS_IN_OUT_GEOMETRIC;
    case options::Z3RestartStrategyMode::LUBY: return RS_LUBY;
    case options::Z3RestartStrategyMode::FIXED: return RS_FIXED;
    case options::Z3RestartStrategyMode::ARITHMETIC: return RS_ARITHMETIC;
    default: return RS_IN_OUT_GEOMETRIC;
  }
}

InitialActivity toInitialActivity(options::Z3InitialActivityMode m)
{
  switch (m)
  {
    case options::Z3InitialActivityMode::ZERO: return IA_ZERO;
    case options::Z3InitialActivityMode::RANDOM: return IA_RANDOM;
    case options::Z3InitialActivityMode::RANDOM_WHEN_SEARCHING:
      return IA_RANDOM_WHEN_SEARCHING;
    default: return IA_RANDOM_WHEN_SEARCHING;
  }
}

}  // namespace

void Params::initialize(const Options& opts)
{
  d_autoConfig = opts.z3.z3AutoConfig;
  d_relevancyLvl = static_cast<uint32_t>(opts.z3.z3Relevancy);
  d_caseSplitStrategy = toCaseSplitStrategy(opts.z3.z3CaseSplit);
  d_phaseSelection = toPhaseSelection(opts.z3.z3PhaseSelection);
  d_restartStrategy = toRestartStrategy(opts.z3.z3RestartStrategy);
  d_randomInitialActivity = toInitialActivity(opts.z3.z3RandomInitialActivity);
  d_restartInitial = static_cast<uint32_t>(opts.z3.z3RestartInitial);
  d_restartFactor = opts.z3.z3RestartFactor;
  d_delayUnits = opts.z3.z3DelayUnits;
  d_randomSeed = static_cast<uint32_t>(opts.z3.z3RandomSeed);
  d_ematching = opts.z3.z3Ematching;
  d_qiLazyQuickChecker = opts.z3.z3QiLazyQuickChecker;
  d_qiQuickCheckerConservative = opts.z3.z3QiQuickCheckerConservative;
  d_enumInst = opts.z3.z3EnumInst;
  d_enumInstFallback = opts.z3.z3EnumInstFallback;
  d_enumInstMaxPerRound = static_cast<uint32_t>(opts.z3.z3EnumInstMaxPerRound);
  d_bridgeEager = opts.z3.z3BridgeEager;
  d_forceRematch = opts.z3.z3ForceRematch;
  d_mbqi = opts.z3.z3Mbqi;
  d_qiCost = opts.z3.z3QiCost;
  d_qiProfile = opts.z3.z3QiProfile;
  d_qiNewGen = opts.z3.z3QiNewGen;
  d_qiEagerThreshold = opts.z3.z3QiEagerThreshold;
  d_qiLazyThreshold = opts.z3.z3QiLazyThreshold;
  d_qiMaxEagerMultipatterns =
      static_cast<uint32_t>(opts.z3.z3QiMaxMultiPatterns);
  uint64_t maxInst = opts.z3.z3QiMaxInstances;
  d_qiMaxInstances =
      maxInst > UINT32_MAX ? UINT32_MAX : static_cast<uint32_t>(maxInst);
  d_piEnabled = opts.z3.z3PatternInference;
  d_arithNl = opts.z3.z3ArithNl;
  d_arithNative = opts.z3.z3Arith == options::Z3ArithMode::NATIVE;
  if (opts.z3.z3Preset == options::Z3PresetMode::VERUS)
  {
    // The options Verus passes to Z3 (auto_config=false smt.mbqi=false
    // smt.case_split=3 smt.qi.eager_threshold=100 smt.delay_units=true
    // pi.enabled=false smt.arith.nl=false smt.arith.solver=2).
    // rewriter.sort_disjunctions=false has no counterpart, since the
    // rewriter is cvc5's.
    const options::HolderZ3& z = opts.z3;
    if (!z.z3AutoConfigWasSetByUser) d_autoConfig = false;
    if (!z.z3MbqiWasSetByUser) d_mbqi = false;
    if (!z.z3CaseSplitWasSetByUser) d_caseSplitStrategy = CS_RELEVANCY;
    if (!z.z3QiEagerThresholdWasSetByUser) d_qiEagerThreshold = 100.0;
    if (!z.z3DelayUnitsWasSetByUser) d_delayUnits = true;
    if (!z.z3PatternInferenceWasSetByUser) d_piEnabled = false;
    if (!z.z3ArithNlWasSetByUser) d_arithNl = false;
    // smt.arith.solver=2
    if (!z.z3ArithWasSetByUser) d_arithNative = true;
  }
  switch (opts.z3.z3NgLiftIte)
  {
    case options::Z3LiftIteMode::NONE: d_ngLiftIte = LI_NONE; break;
    case options::Z3LiftIteMode::CONSERVATIVE:
      d_ngLiftIte = LI_CONSERVATIVE;
      break;
    case options::Z3LiftIteMode::FULL: d_ngLiftIte = LI_FULL; break;
    default:
      // In Z3 the default is LI_NONE and setup_AUFLIA / setup_AUFLIRA, which
      // setup_unknown(st) reaches for any quantified input under auto
      // configuration, raise it to LI_CONSERVATIVE. The lifting only applies
      // to non-ground terms, so on an input without quantifiers the two are
      // the same. It has to be decided here rather than in Setup, because the
      // port preprocesses each assertion as it is asserted, before the first
      // check configures the context.
      d_ngLiftIte = d_autoConfig ? LI_CONSERVATIVE : LI_NONE;
      break;
  }
}

}  // namespace z3
}  // namespace cvc5::internal

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
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), files
 * src/params/smt_params.h and src/params/qi_params.h, and recast in cvc5
 * style. The default values are Z3's, verbatim: they are part of what is
 * being replicated, so they are kept here rather than being re-derived from
 * cvc5's own defaults.
 *
 * Note that Z3 overrides several of these per logic when auto_config is on
 * (see setup.cpp), which is replicated separately.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__PARAMS_H
#define CVC5__Z3__PARAMS_H

#include <climits>
#include <cstdint>
#include <string>

namespace cvc5::internal {

class Options;

namespace z3 {

/** How the next case split is chosen. Z3's case_split_strategy. */
enum CaseSplitStrategy
{
  /** based on activity */
  CS_ACTIVITY,
  /** based on activity, but delaying splits created during the search */
  CS_ACTIVITY_DELAY_NEW,
  /** based on activity, caching the activity */
  CS_ACTIVITY_WITH_CACHE,
  /** based on relevancy */
  CS_RELEVANCY,
  /** based on relevancy and activity */
  CS_RELEVANCY_ACTIVITY,
  /** based on relevancy and the current goal */
  CS_RELEVANCY_GOAL,
  /** activity based, but theory solvers may manipulate the activity */
  CS_ACTIVITY_THEORY_AWARE_BRANCHING
};

/** How the phase of a case split is chosen. Z3's phase_selection. */
enum PhaseSelection
{
  PS_ALWAYS_FALSE,
  PS_ALWAYS_TRUE,
  PS_CACHING,
  PS_CACHING_CONSERVATIVE,
  /** like the previous one, but alternating the default from time to time */
  PS_CACHING_CONSERVATIVE2,
  PS_RANDOM,
  PS_OCCURRENCE,
  PS_THEORY
};

/** Z3's restart_strategy. */
enum RestartStrategy
{
  RS_GEOMETRIC,
  RS_IN_OUT_GEOMETRIC,
  RS_LUBY,
  RS_FIXED,
  RS_ARITHMETIC
};

/** Z3's lemma_gc_strategy. */
enum LemmaGcStrategy
{
  LGC_FIXED,
  LGC_GEOMETRIC,
  LGC_AT_RESTART,
  LGC_NONE
};

/** Z3's initial_activity. */
enum InitialActivity
{
  IA_ZERO,
  IA_RANDOM_WHEN_SEARCHING,
  IA_RANDOM
};

/** Z3's dyn_ack_strategy. */
enum DynAckStrategy
{
  DACK_DISABLED,
  /** congruence is the root of the conflict */
  DACK_ROOT,
  /** congruence used during conflict resolution */
  DACK_CR
};

/** Z3's quick_checker_mode. */
enum QuickCheckerMode
{
  /** do not use (cheap) model checking based instantiation */
  MC_NO,
  /** instantiate unsatisfied instances */
  MC_UNSAT,
  /** instantiate unsatisfied and not-satisfied instances */
  MC_NO_SAT
};

/**
 * The parameters of the ported core, mirroring the subset of Z3's smt_params
 * that the ported components consult.
 */
struct Params
{
  /** Initialize from cvc5's options, leaving Z3's defaults where unset. */
  void initialize(const Options& opts);

  // ---------------------------------------------------- core search
  bool d_eqPropagation = true;
  bool d_binaryClauseOpt = true;
  uint32_t d_relevancyLvl = 2;
  bool d_relevancyLemma = false;
  uint32_t d_randomSeed = 0;
  double d_randomVarFreq = 0.01;
  double d_invDecay = 1.052;
  uint32_t d_clauseDecay = 1;
  InitialActivity d_randomInitialActivity = IA_RANDOM_WHEN_SEARCHING;
  PhaseSelection d_phaseSelection = PS_CACHING_CONSERVATIVE;
  uint32_t d_phaseCachingOn = 700;
  uint32_t d_phaseCachingOff = 100;
  bool d_minimizeLemmas = true;
  uint32_t d_maxConflicts = UINT_MAX;
  uint32_t d_restartMax = UINT_MAX;
  bool d_simplifyClauses = true;
  uint32_t d_tick = 1000;
  bool d_newCore2ThEq = true;
  bool d_ematching = true;

  // ---------------------------------------------------- case split
  CaseSplitStrategy d_caseSplitStrategy = CS_ACTIVITY_DELAY_NEW;
  uint32_t d_relCaseSplitOrder = 0;
  bool d_lookaheadDiseq = false;
  bool d_theoryCaseSplit = false;
  bool d_theoryAwareBranching = false;

  // ---------------------------------------------------- delay units
  bool d_delayUnits = false;
  uint32_t d_delayUnitsThreshold = 32;

  // ---------------------------------------------------- conflict resolution
  bool d_theoryResolve = false;

  // ---------------------------------------------------- restarts
  RestartStrategy d_restartStrategy = RS_IN_OUT_GEOMETRIC;
  uint32_t d_restartInitial = 100;
  double d_restartFactor = 1.1;
  bool d_restartAdaptive = true;
  double d_agilityFactor = 0.9999;
  double d_restartAgilityThreshold = 0.18;

  // ---------------------------------------------------- lemma gc
  LemmaGcStrategy d_lemmaGcStrategy = LGC_FIXED;
  bool d_lemmaGcHalf = false;
  uint32_t d_recentLemmasSize = 100;
  uint32_t d_lemmaGcInitial = 5000;
  double d_lemmaGcFactor = 1.1;
  /** the ratio of new and old clauses */
  uint32_t d_newOldRatio = 16;
  uint32_t d_newClauseActivity = 10;
  uint32_t d_oldClauseActivity = 500;
  /** max. number of unassigned literals for a new clause to be relevant */
  uint32_t d_newClauseRelevancy = 45;
  /** max. number of unassigned literals for an old clause to be relevant */
  uint32_t d_oldClauseRelevancy = 6;
  double d_invClauseDecay = 1;

  // ---------------------------------------------------- dynamic
  // ackermannization
  DynAckStrategy d_dack = DACK_ROOT;
  bool d_dackEq = false;
  double d_dackFactor = 0.1;
  uint32_t d_dackThreshold = 10;
  uint32_t d_dackGc = 2000;
  double d_dackGcInvDecay = 0.8;

  // ---------------------------------------------------- quantifier
  // instantiation
  /**
   * The cost of a quantifier instantiation, as an arithmetic expression over
   * "weight", "generation", "cost", "min_top_generation" and
   * "max_top_generation". Instances above d_qiEagerThreshold are delayed and
   * those above d_qiLazyThreshold are dropped.
   *
   * The default must keep weight > 0 contributing, otherwise matching loops
   * are never broken; see the long comment in Z3's qi_params.h.
   */
  std::string d_qiCost = "(+ weight generation)";
  /** How the generation of enodes created by an instantiation is set. */
  std::string d_qiNewGen = "cost";
  double d_qiEagerThreshold = 10.0;
  double d_qiLazyThreshold = 20.0;
  uint32_t d_qiMaxEagerMultipatterns = 0;
  uint32_t d_qiMaxLazyMultipatternMatching = 2;
  bool d_qiProfile = false;
  uint32_t d_qiProfileFreq = UINT_MAX;
  QuickCheckerMode d_qiQuickChecker = MC_NO;
  bool d_qiLazyQuickChecker = true;
  bool d_qiPromoteUnsat = true;
  uint32_t d_qiMaxInstances = UINT_MAX;
  bool d_qiLazyInstantiation = false;
  bool d_qiConservativeFinalCheck = false;

  // ---------------------------------------------------- mbqi
  bool d_mbqi = true;
  uint32_t d_mbqiMaxCexs = 1;
  uint32_t d_mbqiMaxCexsIncr = 1;
  uint32_t d_mbqiMaxIterations = 1000;
  bool d_mbqiTrace = false;
  uint32_t d_mbqiForceTemplate = 10;

  // ---------------------------------------------------- pattern inference
  /** How arithmetic symbols may be used in an inferred pattern. */
  enum ArithPatternInferenceKind
  {
    /** do not infer patterns with arithmetic terms */
    AP_NO,
    /** infer patterns with arithmetic terms only if there is no other option */
    AP_CONSERVATIVE,
    /** always use patterns with arithmetic terms */
    AP_FULL
  };

  bool d_piEnabled = true;
  uint32_t d_piMaxMultiPatterns = 0;
  bool d_piBlockLoopPatterns = true;
  bool d_piDecomposePatterns = true;
  ArithPatternInferenceKind d_piArith = AP_CONSERVATIVE;
  uint32_t d_piArithWeight = 5;
  uint32_t d_piNonNestedArithWeight = 10;
  int32_t d_piNopatWeight = -1;
  bool d_piAvoidSkolems = true;
  bool d_piWarnings = false;

  // ---------------------------------------------------- datatypes
  /** 0 - eager, 1 - lazy for infinite types, 2 - lazy */
  uint32_t d_dtLazySplits = 1;

  // ---------------------------------------------------- misc
  bool d_autoConfig = true;
  bool d_model = true;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__PARAMS_H */

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Pattern inference for eager E-matching.
 *
 * A port of z3's ast/pattern/pattern_inference.cpp. It is used for the
 * quantified formulas that carry no usable pattern annotation, which in
 * practice is most of them, and it determines which instances exist at all, so
 * it has to agree with z3 for the instances to agree.
 *
 * This is deliberately not cvc5's PatternTermSelector: that makes different
 * choices (it does not decompose, it ranks differently, and it does not block
 * looping patterns the same way), so using it would make the instances differ
 * from z3's for reasons that have nothing to do with the matcher.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__PATTERN_INFERENCE_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__PATTERN_INFERENCE_H

#include <map>
#include <set>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

/**
 * Infers the patterns of a quantified formula.
 */
class PatternInference : protected EnvObj
{
 public:
  PatternInference(Env& env);
  ~PatternInference();

  /**
   * Append to pats the INST_PATTERN nodes inferred for q, which must be a
   * FORALL with no usable pattern annotation. z3:
   * pattern_inference_cfg::reduce_quantifier.
   */
  void getPatterns(TNode q, std::vector<Node>& pats);

 private:
  /** The set of bound variable indices a candidate contains */
  using VarSet = std::set<size_t>;
  /** What is known about a subterm of the body. z3: collect::info */
  struct Info
  {
    /** the variables of the quantifier it contains */
    VarSet d_freeVars;
    /** whether it contains a variable bound inside the body */
    bool d_hasForeignVar = false;
    /** its tree size */
    size_t d_size = 0;
    /** whether it can occur inside a pattern at all */
    bool d_valid = true;
  };
  /** A multi-pattern under construction. z3: struct pre_pattern */
  struct PrePattern
  {
    std::vector<Node> d_exprs;
    VarSet d_freeVars;
    size_t d_idx = 0;
  };

  /**
   * One pass of the inference. Returns the inferred patterns, which is empty if
   * none was found. z3: pattern_inference_cfg::mk_patterns.
   */
  void mkPatterns(TNode q,
                  TNode body,
                  const std::vector<Node>& noPatterns,
                  std::vector<Node>& result);
  /** Collect the candidate patterns of body. z3: collect::operator() */
  void collect(TNode body);
  /** Process one subterm of the body. z3: collect::save_candidate */
  void saveCandidate(TNode n);
  /** Record n as a candidate. z3: pattern_inference_cfg::add_candidate */
  void addCandidate(TNode n, const VarSet& freeVars, size_t size);
  /** Can n occur inside a pattern? z3: pattern_inference_cfg::is_forbidden */
  bool isForbidden(TNode n) const;
  /** Is n an application of an arithmetic operator? */
  static bool isArith(TNode n);
  /** May an application of this arithmetic operator be a candidate itself? */
  bool isArithCandidateKind(Kind k) const;
  /**
   * Is every instance of p2 also an instance of p1? z3: smaller_pattern.
   */
  bool isSmallerPattern(TNode p1, TNode p2) const;
  /** z3: pattern_inference_cfg::filter_looping_patterns */
  void filterLoopingPatterns(std::vector<Node>& result);
  /** z3: pattern_inference_cfg::filter_bigger_patterns */
  void filterBiggerPatterns(const std::vector<Node>& patterns,
                            std::vector<Node>& result);
  /** z3: pattern_inference_cfg::contains_subpattern */
  bool containsSubpattern(TNode n) const;
  /** z3: pattern_inference_cfg::candidates2unary_patterns */
  void candidatesToUnaryPatterns(const std::vector<Node>& candidates,
                                 std::vector<Node>& remaining,
                                 std::vector<Node>& result);
  /** z3: pattern_inference_cfg::candidates2multi_patterns */
  void candidatesToMultiPatterns(size_t maxNumPatterns,
                                 const std::vector<Node>& candidates,
                                 std::vector<Node>& result);
  /** Build an INST_PATTERN from a candidate. z3: mk_pattern */
  Node mkPattern(TNode candidate);
  /** Build an INST_PATTERN from a list of pattern terms */
  Node mkPattern(const std::vector<Node>& terms);
  /** Order on candidates. z3: pattern_weight_lt */
  bool patternWeightLt(TNode n1, TNode n2) const;

  //------------------------------------------------- per-quantifier state
  /** The index of each bound variable of the quantifier */
  std::map<Node, size_t> d_varIndex;
  /** The number of bound variables */
  size_t d_numBindings;
  /** The patterns that must not be used, from an INST_NO_PATTERN annotation */
  std::vector<Node> d_noPatterns;
  /** What is known about each subterm of the body */
  std::map<Node, Info> d_info;
  /** The candidates, in the order they were found */
  std::vector<Node> d_candidates;
  /** The free variables and size of each candidate */
  std::map<Node, std::pair<VarSet, size_t>> d_candidateInfo;
  //--------------------------------------------- end per-quantifier state

  //------------------------------------------------- pass configuration
  /** Whether arithmetic operators may occur inside a pattern at all */
  bool d_forbidArith;
  /** Whether an arithmetic application may itself be a pattern */
  bool d_nestedArithOnly;
  /** Whether strictly smaller candidates are dropped */
  bool d_blockLoopPatterns;
  /** Whether a pattern may be decomposed into a multi-pattern */
  bool d_decomposePatterns;
  /** The number of extra multi-patterns that may be created */
  size_t d_maxMultiPatterns;
  //--------------------------------------------- end pass configuration
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif

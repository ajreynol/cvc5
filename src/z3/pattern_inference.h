/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Pattern inference for quantifiers without a :pattern annotation.
 *
 * Ported from Z3's src/ast/pattern/pattern_inference.{h,cpp}
 * (Copyright (c) 2006 Microsoft Corporation, MIT license, author Leonardo de
 * Moura) and recast in cvc5's style.
 *
 * The one structural difference from Z3 is that this port numbers quantified
 * variables by de Bruijn *level* rather than index (see z3/ast.h), so the
 * "delta" shifting Z3 performs while descending through nested binders is not
 * needed: a variable of level i belongs to the quantifier currently being
 * processed exactly when i < numDecls.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__PATTERN_INFERENCE_H
#define CVC5__Z3__PATTERN_INFERENCE_H

#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "z3/util/uint_set.h"

namespace cvc5::internal {
namespace z3 {

class Params;

/**
 * A pattern p1 is smaller than a pattern p2 iff every instance of p2 is also
 * an instance of p1. For example f(X) is smaller than f(g(X)), since every
 * instance of f(g(X)) is also an instance of f(X).
 */
class SmallerPattern
{
 public:
  bool operator()(size_t base, size_t numBindings, TNode p1, TNode p2);

 private:
  using ExprPair = std::pair<Node, Node>;
  struct ExprPairHash
  {
    size_t operator()(const ExprPair& p) const
    {
      return p.first.getId() * 7919 + p.second.getId();
    }
  };

  void save(TNode p1, TNode p2);
  bool process(TNode p1, TNode p2);

  size_t d_base = 0;
  std::vector<Node> d_bindings;
  std::vector<ExprPair> d_todo;
  std::unordered_set<ExprPair, ExprPairHash> d_cache;
};

/**
 * Infers patterns for the quantifiers of a formula that carry no pattern
 * annotation, rewriting the formula bottom-up as Z3's pattern_inference_rw
 * does.
 */
class PatternInference
{
 public:
  PatternInference(NodeManager* nm, const Params& params);
  ~PatternInference();

  /** The result of inferring patterns for every quantifier in n. */
  Node apply(TNode n);

 private:
  /** Information about a candidate pattern. */
  struct Info
  {
    Info() : d_size(0) {}
    Info(const UIntSet& vars, uint32_t size) : d_freeVars(vars), d_size(size) {}

    UIntSet d_freeVars;
    uint32_t d_size;
  };

  /** Information collected for a subterm while gathering candidates. */
  struct CollectInfo
  {
    CollectInfo(const UIntSet& fvars, const UIntSet& bvars, uint32_t sz)
        : d_freeVars(fvars), d_boundVars(bvars), d_size(sz)
    {
    }

    UIntSet d_freeVars;
    UIntSet d_boundVars;
    uint32_t d_size;
  };

  /** A multi-pattern under construction. */
  struct PrePattern
  {
    PrePattern() : d_idx(0) {}

    /** the elements of the pattern */
    std::vector<Node> d_exprs;
    /** the free variables of d_exprs */
    UIntSet d_freeVars;
    /** the index of the next candidate to process */
    size_t d_idx;
  };

  /**
   * p1 < p2 if p1 has more free variables than p2, or they have the same
   * number of free variables and p1 is smaller than p2.
   */
  struct PatternWeightLt
  {
    PatternWeightLt(const std::unordered_map<Node, Info>& i)
        : d_candidatesInfo(i)
    {
    }

    bool operator()(TNode n1, TNode n2) const;

    const std::unordered_map<Node, Info>& d_candidatesInfo;
  };

  Node applyRec(TNode n);
  /**
   * The quantifier q with inferred patterns, or q itself if nothing was
   * inferred. The body of q is already rewritten.
   */
  Node reduceQuantifier(TNode q, TNode newBody);

  void collect(TNode n);
  bool collectVisitChildren(TNode n);
  void collectSave(TNode n, CollectInfo* i);
  void collectSaveCandidate(TNode n);

  void addCandidate(TNode n, const UIntSet& freeVars, uint32_t size);
  /**
   * Copy the non-looping candidates to result, or all of them if looping
   * patterns are not blocked.
   */
  void filterLoopingPatterns(std::vector<Node>& result);
  /**
   * Copy a pattern p to result if no direct or indirect child of p is also a
   * candidate with the same set of variables.
   */
  void filterBiggerPatterns(const std::vector<Node>& patterns,
                            std::vector<Node>& result);
  /** True if n has a child that is also a candidate with the same variables */
  bool containsSubpattern(TNode n);
  bool hasPreferredPatterns(const std::vector<Node>& candidates,
                            std::vector<Node>& result);
  Node mkPattern(TNode candidate);
  /**
   * Create the unary patterns, i.e. the single terms containing all the bound
   * variables. A candidate that does not contain all of them is copied to
   * remaining instead.
   */
  void candidates2UnaryPatterns(const std::vector<Node>& candidates,
                                std::vector<Node>& remaining,
                                std::vector<Node>& result);
  void candidates2MultiPatterns(size_t maxNumPatterns,
                                const std::vector<Node>& candidates,
                                std::vector<Node>& result);
  /**
   * All the minimal unary patterns (the terms containing every bound
   * variable) are copied to result. If there are unary patterns then at most
   * numExtraMultiPatterns multi-patterns are created, otherwise at most
   * 1 + numExtraMultiPatterns are.
   */
  void mkPatterns(size_t baseLevel,
                  size_t numBindings,
                  TNode n,
                  const std::vector<Node>& noPatterns,
                  std::vector<Node>& result);

  bool isForbidden(TNode n) const;

  NodeManager* d_nm;
  const Params& d_params;
  /** true if the arithmetic symbols are currently forbidden */
  bool d_forbidArith;
  SmallerPattern d_le;
  /** the de Bruijn level of the first variable of the current quantifier */
  size_t d_baseLevel;
  size_t d_numBindings;
  const std::vector<Node>* d_noPatterns;
  bool d_nestedArithOnly;
  bool d_blockLoopPatterns;
  bool d_decomposePatterns;

  /** candidate -> its free variables and size */
  std::unordered_map<Node, Info> d_candidatesInfo;
  std::vector<Node> d_candidates;
  std::vector<Node> d_tmp1;
  std::vector<Node> d_tmp2;
  PatternWeightLt d_patternWeightLt;

  /** the cache of the candidate collector, keyed on the subterm */
  std::unordered_map<Node, std::unique_ptr<CollectInfo>> d_collectCache;
  std::vector<TNode> d_collectTodo;

  std::vector<std::unique_ptr<PrePattern>> d_prePatterns;
  std::vector<Node> d_args;
  /** the cache of apply() */
  std::unordered_map<Node, Node> d_cache;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__PATTERN_INFERENCE_H */

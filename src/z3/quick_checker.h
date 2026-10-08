/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An incomplete model checker for quantifiers.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), files
 * src/smt/smt_quick_checker.{h,cpp}, and recast in cvc5 style.
 *
 * This finds instances of a quantifier that the current partial model
 * falsifies, by enumerating a small set of candidate bindings collected from
 * the terms already in the context. Z3 enables it for the quantified logics
 * (qi_quick_checker = MC_UNSAT, see setup.cpp), where it catches the
 * instances E-matching misses because no pattern matches them.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__QUICK_CHECKER_H
#define CVC5__Z3__QUICK_CHECKER_H

#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "z3/types.h"

namespace cvc5::internal {
namespace z3 {

class SmtContext;

/**
 * Finds quantifier instantiations that the current model falsifies.
 *
 * Note the way candidates are selected is deliberately naive, as in Z3.
 */
class QuickChecker
{
 public:
  QuickChecker(SmtContext& c);

  /**
   * Instantiate the instances the current model falsifies.
   *
   * @param conservative Whether the candidate bindings are restricted to the
   * terms that already occur at the same position under the same symbol, as
   * Z3 does. Dropping the restriction widens the search in the same way Z3's
   * model based instantiation does, while still only creating the instances
   * the current assignment falsifies.
   */
  bool instantiateUnsat(TNode q, bool conservative = true);

  /** Instantiate the instances the current model does not satisfy. */
  bool instantiateNotSat(TNode q, bool conservative = false);

  /**
   * Add at most one instance of q, from the candidate bindings the collector
   * proposes, preferring one the current assignment falsifies. This is not a
   * Z3 method; see z3/enum_inst.h for why it exists.
   */
  bool instantiateFirstNew(TNode q);

  /**
   * Whether an atom with no value under the current assignment counts as
   * false. The assignment is partial, so the plain check almost never finds a
   * falsified binding; completing it this way gives a crude but consistent
   * candidate model, which is the role Z3's model checker plays. Two
   * congruent atoms are given the same value, since the check works on the
   * congruence class of the canonical form.
   */
  void setTotal(bool total) { d_total = total; }

 private:
  using ENodeSet = std::unordered_set<ENode*>;

  /** Collects the candidate bindings of a quantifier. */
  class Collector
  {
   public:
    Collector(SmtContext& c);

    void operator()(TNode q,
                    bool conservative,
                    std::vector<ENodeVector>& candidates);

   private:
    /** One visited subterm, together with the position it occurs at. */
    struct Entry
    {
      Node d_expr;
      Node d_parent;
      size_t d_parentPos;

      bool operator==(const Entry& e) const
      {
        return d_expr == e.d_expr && d_parent == e.d_parent
               && d_parentPos == e.d_parentPos;
      }
    };

    struct EntryHash
    {
      size_t operator()(const Entry& e) const
      {
        size_t h = e.d_expr.getId();
        if (!e.d_parent.isNull())
        {
          h = h * 7919 + e.d_parent.getId() * 31 + e.d_parentPos;
        }
        return h;
      }
    };

    void init(TNode q);
    /**
     * True if there is a term (f ... n' ...) in the context whose i-th
     * argument n' is in the class of n. A null f means there is no parent to
     * check, in which case true is returned.
     */
    bool checkArg(ENode* n, TNode f, size_t i);
    void collectCore(TNode n, TNode p, size_t i);
    void collect(TNode n, TNode f, size_t idx);
    void saveResult(std::vector<ENodeVector>& candidates);

    SmtContext& d_context;
    bool d_conservative;
    size_t d_numVars;
    /** mapping: variable level -> whether a candidate set was found */
    std::vector<bool> d_alreadyFound;
    /** mapping: variable level -> the candidates */
    std::vector<ENodeSet> d_candidates;
    std::vector<ENodeSet> d_tmpCandidates;
    std::unordered_set<Entry, EntryHash> d_cache;
  };

  bool allArgs(TNode a, bool isTrue);
  bool anyArg(TNode a, bool isTrue);
  bool checkCore(TNode n, bool isTrue);
  bool check(TNode n, bool isTrue);
  bool checkQuantifier(TNode q, bool isTrue);
  Node canonize(TNode n);
  bool processCandidates(TNode q, bool unsat);
  bool processFirstNew(TNode q);

  /**
   * Fill the candidates of the variables the collector found none for with
   * the class representatives of the variable's sort. The collector only
   * proposes a term that already occurs at the same position under the same
   * symbol, which for most quantifiers leaves at least one variable with
   * nothing at all; cvc5's own enumerative instantiation falls back to the
   * sort in the same way.
   */
  void fillBySort(TNode q);

  /** How many terms of a sort may be used as candidates. */
  static constexpr size_t s_maxBySort = 32;

  /** How many binding tuples instantiateFirstNew may scan. */
  static constexpr size_t s_maxTuplesPerQuantifier = 2000;

  SmtContext& d_context;
  Collector d_collector;
  std::vector<ENodeVector> d_candidateVectors;
  struct NodeBoolHash
  {
    size_t operator()(const std::pair<Node, bool>& p) const
    {
      return p.first.getId() * 2 + (p.second ? 1 : 0);
    }
  };

  std::unordered_map<std::pair<Node, bool>, bool, NodeBoolHash> d_checkCache;
  std::unordered_map<Node, Node> d_canonizeCache;
  size_t d_numBindings;
  ENodeVector d_bindings;
  bool d_total;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUICK_CHECKER_H */

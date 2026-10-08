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

  /** Instantiate the instances the current model falsifies. */
  bool instantiateUnsat(TNode q);

  /** Instantiate the instances the current model does not satisfy. */
  bool instantiateNotSat(TNode q);

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
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUICK_CHECKER_H */

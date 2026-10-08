/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Dynamic Ackermannization.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/dyn_ack.h, and recast in cvc5 style.
 *
 * When a congruence f(a) = f(b) keeps showing up in conflicts, it is cheaper
 * to add the Ackermann clause (a /= b or f(a) = f(b)) once than to rederive
 * the congruence each time. This manager counts how often each congruence is
 * used and instantiates the rule for the frequent ones.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__DYN_ACK_H
#define CVC5__Z3__DYN_ACK_H

#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "z3/clause.h"
#include "z3/params.h"
#include "z3/util/literal.h"

namespace cvc5::internal {
namespace z3 {

class SmtContext;

class DynAckManager
{
  using AppPair = std::pair<Node, Node>;
  using ExprTriple = std::tuple<Node, Node, Node>;

  struct AppPairHash
  {
    size_t operator()(const AppPair& p) const
    {
      return std::hash<Node>()(p.first) * 31 + std::hash<Node>()(p.second);
    }
  };

  struct ExprTripleHash
  {
    size_t operator()(const ExprTriple& t) const
    {
      size_t h = std::hash<Node>()(std::get<0>(t));
      h = h * 31 + std::hash<Node>()(std::get<1>(t));
      h = h * 31 + std::hash<Node>()(std::get<2>(t));
      return h;
    }
  };

 public:
  DynAckManager(SmtContext& ctx, Params& p);
  ~DynAckManager();

  void setup() {}

  /** Invoked before the beginning of the search. */
  void initSearchEh();

  /** Invoked when the congruence rule was used during conflict resolution. */
  void usedCgEh(TNode n1, TNode n2)
  {
    if (d_params.d_dack == DACK_CR)
    {
      cgEh(n1, n2);
    }
  }

  /** Invoked when the congruence rule is the root of a conflict. */
  void cgConflictEh(TNode n1, TNode n2)
  {
    if (d_params.d_dack == DACK_ROOT)
    {
      cgEh(n1, n2);
    }
  }

  /** Invoked when equalities are used during conflict resolution. */
  void usedEqEh(TNode n1, TNode n2, TNode r)
  {
    if (d_params.d_dackEq)
    {
      eqEh(n1, n2, r);
    }
  }

  /** Invoked when it is safe to expand the new Ackermann rule entries. */
  void propagateEh();

  void reset();

  /** Invoked when a clause this manager created is deleted. */
  void delClauseEh(Clause* cls);

 private:
  void gc();
  void resetAppPairs();
  void instantiate(TNode n1, TNode n2);
  Literal mkEq(TNode n1, TNode n2);
  void cgEh(TNode n1, TNode n2);

  void eqEh(TNode n1, TNode n2, TNode r);
  void instantiate(TNode n1, TNode n2, TNode r);
  void resetExprTriples();
  void gcTriples();

  SmtContext& d_context;
  Params& d_params;
  std::unordered_map<AppPair, uint32_t, AppPairHash> d_appPair2NumOccs;
  std::vector<AppPair> d_appPairs;
  std::vector<AppPair> d_toInstantiate;
  size_t d_qhead;
  size_t d_numInstances;
  size_t d_numPropagationsSinceLastGc;
  std::unordered_set<AppPair, AppPairHash> d_instantiated;
  std::unordered_map<Clause*, AppPair> d_clause2AppPair;

  struct Triple
  {
    std::unordered_map<ExprTriple, uint32_t, ExprTripleHash> d_app2NumOccs;
    std::vector<ExprTriple> d_apps;
    std::vector<ExprTriple> d_toInstantiate;
    size_t d_qhead = 0;
    size_t d_numInstances = 0;
    size_t d_numPropagationsSinceLastGc = 0;
    std::unordered_set<ExprTriple, ExprTripleHash> d_instantiated;
    std::unordered_map<Clause*, ExprTriple> d_clause2Apps;
  };
  Triple d_triple;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__DYN_ACK_H */

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Converting the (dis)equalities the core propagates into arithmetic atoms.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), file
 * src/smt/arith_eq_adapter.{h,cpp}, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__ARITH_EQ_ADAPTER_H
#define CVC5__Z3__ARITH_EQ_ADAPTER_H

#include <map>
#include <utility>
#include <vector>

#include "expr/node.h"
#include "z3/enode.h"
#include "z3/types.h"

namespace cvc5::internal {
namespace z3 {

class SmtContext;
class Theory;

/**
 * For every pair of arithmetic terms the core equates or disequates, the
 * axioms
 *
 *   t1 = t2  =>  t1 - t2 <= 0
 *   t1 = t2  =>  t1 - t2 >= 0
 *   t1 - t2 <= 0 & t1 - t2 >= 0  =>  t1 = t2
 *
 * which is how a (dis)equality reaches the simplex: as bounds.
 */
class ArithEqAdapter
{
 public:
  struct Stats
  {
    uint64_t d_numEqAxioms = 0;
  };

  ArithEqAdapter(Theory& owner);

  void newEqEh(TheoryVar v1, TheoryVar v2);
  void newDiseqEh(TheoryVar v1, TheoryVar v2);
  void resetEh();
  void initSearchEh();
  void restartEh();

  /** Add the equality axioms for n1 and n2. */
  void mkAxioms(ENode* n1, ENode* n2);

  const Stats& getStats() const { return d_stats; }

  /** The data of a processed pair: the atoms t1 = t2, t1 <= t2, t1 >= t2. */
  struct Data
  {
    Node d_t1EqT2;
    Node d_le;
    Node d_ge;
  };
  using AlreadyProcessed = std::map<std::pair<ENode*, ENode*>, Data>;

 private:
  SmtContext& getContext() const;

  Theory& d_owner;
  Stats d_stats;
  AlreadyProcessed d_alreadyProcessed;
  std::vector<std::pair<ENode*, ENode*>> d_restartPairs;
  /**
   * Every atom created, kept alive for the relevancy handlers, which hold
   * plain TNodes; Z3 relies on its own reference counting for the same.
   */
  std::vector<Node> d_keepAlive;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__ARITH_EQ_ADAPTER_H */

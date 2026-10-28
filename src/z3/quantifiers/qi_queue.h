/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The queue of quantifier instantiations.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), files
 * src/smt/qi_queue.h and src/smt/qi_queue.cpp, recast in cvc5 style.
 *
 * E-matching hands every match it finds to this queue, which costs it and
 * then either instantiates it right away (cost at or below the eager
 * threshold), promotes it because it already produces a conflict, or drops
 * it. This triage, not the matching itself, is what keeps the number of
 * instances bounded.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__QUANTIFIERS__QI_QUEUE_H
#define CVC5__Z3__QUANTIFIERS__QI_QUEUE_H

#include <ostream>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "z3/quantifiers/checker.h"
#include "z3/quantifiers/fingerprints.h"

namespace cvc5::internal {
namespace z3 {

class QuantifierManager;
class ENode;
class SmtContext;

class QiQueue : protected EnvObj
{
 public:
  QiQueue(Env& env, QuantifierManager& qm, SmtContext& ctx);

  void setup();

  /**
   * Enqueue a new instance. The fingerprint holds the quantifier and the
   * bindings.
   */
  void insert(Fingerprint* f, uint32_t generation);

  void instantiate();

  bool hasWork() const { return !d_newEntries.empty(); }

  void initSearch();

  /** Discard the new entries, before the scopes are popped. */
  void notifyPop() { d_newEntries.clear(); }

 private:
  struct Entry
  {
    Fingerprint* d_qb;
    float d_cost;
    uint32_t d_generation;
    Entry(Fingerprint* f, float c, uint32_t g)
        : d_qb(f), d_cost(c), d_generation(g)
    {
    }
  };

  /**
   * The cost of an instance whose bindings have the maximum generation
   * generation, by Z3's default cost function (+ weight generation). The
   * enodes the instance creates get the cost as their generation, Z3's
   * default (qi.new_gen = cost).
   *
   * cvc5's parser does not retain ":weight", so every quantifier has Z3's
   * default weight, which is 1 and not 0: with weight 0 the cost of an
   * instance is its generation, the generation of the enodes an instance
   * creates is its cost, and so every instance has cost 0 and matching loops
   * are never broken. See the long comment on the "weight 0" performance bug
   * in Z3's qi_params.h.
   */
  static float getCost(uint32_t generation);
  void instantiate(const Entry& ent);
  /**
   * Whether the checker finds the instance of q with these bindings already
   * satisfied (--z3-qi-checker), in which case it is counted, as in Z3, but
   * not made.
   */
  bool skipSatisfied(TNode q, size_t numBindings, ENode* const* bindings);

  QuantifierManager& d_qm;
  SmtContext& d_context;
  /** The instance checker. */
  Checker d_checker;

  /** The instances made, for --z3-qi-max-instances. */
  uint64_t d_numInstances;
  double d_eagerCostThreshold;

  std::vector<Entry> d_newEntries;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIERS__QI_QUEUE_H */

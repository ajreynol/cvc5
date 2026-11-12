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
 * Ported from Z3: src/smt/qi_queue.h, src/smt/qi_queue.cpp.
 * Z3 is Copyright (c) Microsoft Corporation and licensed under the MIT
 * License, see licenses/z3-LICENSE.
 *
 * E-matching hands every match it finds to this queue, which costs it and
 * then either instantiates it right away (cost at or below the eager
 * threshold), promotes it because it already produces a conflict, or drops
 * it. This triage, not the matching itself, is what keeps the number of
 * instances bounded.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__QI_QUEUE_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__QI_QUEUE_H

#include <ostream>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/eager/checker.h"
#include "theory/quantifiers/eager/fingerprints.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

class ENode;
class SmtContext;

/** The queue of the matches found by E-matching, triaged into instances. */
class QiQueue : protected EnvObj
{
 public:
  /** Make the queue of ctx, which makes the instances. */
  QiQueue(Env& env, SmtContext& ctx);

  /** Read the eager cost threshold from the options. */
  void setup();

  /**
   * Enqueue a new instance. The fingerprint holds the quantifier and the
   * bindings.
   */
  void insert(Fingerprint* f, uint32_t generation);

  /**
   * Make the instances of the new entries whose cost is within the eager
   * threshold or that are already in conflict, drop the others, and clear
   * the new entries. Stops early when cancelled or out of resources.
   */
  void instantiate();

  /** True if there are new entries to process. */
  bool hasWork() const { return !d_newEntries.empty(); }

  /** Discard the new entries, when a search starts. */
  void initSearch();

  /** Discard the new entries, before the scopes are popped. */
  void notifyPop() { d_newEntries.clear(); }

 private:
  /** A match waiting to be instantiated. */
  struct Entry
  {
    /** The quantifier and the bindings. */
    Fingerprint* d_qb;
    /** The cost, see getCost. */
    float d_cost;
    /** The maximum generation of the bindings. */
    uint32_t d_generation;
    /** An entry for the match f with cost c and generation g. */
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
  /**
   * Make the instance of ent, unless the core is inconsistent, the checker
   * finds it satisfied, or its body simplifies to true.
   */
  void instantiate(const Entry& ent);
  /**
   * Whether the checker finds the instance of q with these bindings already
   * satisfied, in which case it is counted, as in Z3, but not made.
   */
  bool skipSatisfied(TNode q, size_t numBindings, ENode* const* bindings);

  /** The core, which internalizes the instances. */
  SmtContext& d_context;
  /** The instance checker. */
  Checker d_checker;

  /** The cost at or below which an entry is instantiated right away. */
  double d_eagerCostThreshold;

  /** The entries inserted since the last instantiate. */
  std::vector<Entry> d_newEntries;
};

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER__QI_QUEUE_H */

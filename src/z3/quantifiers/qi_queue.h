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
 * threshold), promotes it because it already produces a conflict, or delays
 * it. Delayed instances are reconsidered at final check and dropped entirely
 * if their cost exceeds the lazy threshold. This triage, not the matching
 * itself, is what keeps the number of instances bounded.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__QUANTIFIERS__QI_QUEUE_H
#define CVC5__Z3__QUANTIFIERS__QI_QUEUE_H

#include <cstring>
#include <ostream>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "z3/quantifiers/checker.h"
#include "z3/quantifiers/fingerprints.h"
#include "z3/quantifiers/quantifier_stat.h"
#include "z3/util/types.h"

namespace cvc5::internal {
namespace z3 {

class QuantifierManager;
class SmtContext;

struct QiQueueStats
{
  uint64_t d_numInstances;
  uint64_t d_numLazyInstances;
  void reset() { std::memset(this, 0, sizeof(QiQueueStats)); }
  QiQueueStats() { reset(); }
};

class QiQueue
{
 public:
  QiQueue(QuantifierManager& qm, SmtContext& ctx);

  void setup();

  /**
   * Enqueue a new instance. The fingerprint holds the quantifier and the
   * bindings.
   */
  void insert(Fingerprint* f, uint32_t generation);

  void instantiate();

  bool hasWork() const { return !d_newEntries.empty(); }

  void initSearch();

  /**
   * Instantiate the delayed entries whose cost is within the lazy threshold.
   * Returns true if nothing was instantiated, i.e. the final check succeeds.
   */
  bool finalCheck();

  void pushScope();
  void popScope(size_t numScopes);

  const QiQueueStats& getStats() const { return d_stats; }

 private:
  struct Entry
  {
    Fingerprint* d_qb;
    float d_cost;
    uint32_t d_generation : 31;
    uint32_t d_instantiated : 1;
    Entry(Fingerprint* f, float c, uint32_t g)
        : d_qb(f), d_cost(c), d_generation(g), d_instantiated(false)
    {
    }
  };

  struct Scope
  {
    size_t d_delayedEntriesLim;
    size_t d_instancesLim;
    size_t d_instantiatedTrailLim;
  };

  /**
   * The cost of an instance of q whose bindings have the maximum generation
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
  float getCost(TNode q, uint32_t generation);
  void instantiate(Entry& ent);
  /** The quantifier of the fingerprint f. */
  TNode getQuantifier(Fingerprint* f) const;
  /**
   * Whether the checker finds the instance of q with these bindings already
   * satisfied (--z3-qi-checker), in which case it is counted, as in Z3, but
   * not made.
   */
  bool skipSatisfied(TNode q,
                     QuantifierStat* stat,
                     size_t numBindings,
                     ENode* const* bindings);
  /**
   * The lemma (or (not q) instance) for the instance of q with these
   * bindings, counted as made; or null if the instance rewrites to true.
   */
  Node mkLemma(TNode q,
               QuantifierStat* stat,
               size_t numBindings,
               ENode* const* bindings);

  QuantifierManager& d_qm;
  SmtContext& d_context;
  /** The instance checker. */
  Checker d_checker;

  QiQueueStats d_stats;
  double d_eagerCostThreshold;

  std::vector<Entry> d_newEntries;
  std::vector<Entry> d_delayedEntries;
  std::vector<Node> d_instances;
  /**
   * The lemmas of the instances made so far, by (SEXPR q t1 ... tn), null for
   * an instance that rewrites to true. The core makes an instance again after
   * backtracking, and its lemma is the same.
   */
  std::unordered_map<Node, Node> d_lemmas;
  std::vector<size_t> d_instantiatedTrail;
  std::vector<Scope> d_scopes;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIERS__QI_QUEUE_H */

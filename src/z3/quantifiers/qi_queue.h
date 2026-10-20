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
#include "z3/quantifiers/cost_function.h"
#include "z3/quantifiers/fingerprints.h"
#include "z3/util/params.h"
#include "z3/quantifiers/quantifier_stat.h"
#include "z3/util/types.h"

namespace cvc5::internal {
namespace z3 {

class QuantifierManager;
class QuantifierServices;

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
  QiQueue(QuantifierManager& qm, QuantifierServices& ctx, Params& params);

  void setup();

  /**
   * Enqueue a new instance. The fingerprint holds the quantifier and the
   * bindings.
   */
  void insert(Fingerprint* f,
              TNode pat,
              uint32_t generation,
              uint32_t minTopGeneration,
              uint32_t maxTopGeneration);

  void instantiate();

  bool hasWork() const { return !d_newEntries.empty(); }

  void initSearchEh();

  /**
   * Instantiate the delayed entries whose cost is within the lazy threshold.
   * Returns true if nothing was instantiated, i.e. the final check succeeds.
   */
  bool finalCheckEh();

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

  QuantifierStat* setValues(TNode q,
                            TNode pat,
                            uint32_t generation,
                            uint32_t minTopGeneration,
                            uint32_t maxTopGeneration,
                            float cost);
  float getCost(TNode q,
                TNode pat,
                uint32_t generation,
                uint32_t minTopGeneration,
                uint32_t maxTopGeneration);
  uint32_t getNewGen(TNode q, uint32_t generation, float cost);
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
  /** Assert the lemma of an instance, with the generation of its terms. */
  void assertLemma(TNode lemma, uint32_t generation);

  QuantifierManager& d_qm;
  QuantifierServices& d_context;
  Params& d_params;
  /** The instance checker. */
  Checker d_checker;

  QiQueueStats d_stats;
  CostFunction d_costFunction;
  CostFunction d_newGenFunction;
  std::vector<float> d_vals;
  double d_eagerCostThreshold;

  std::vector<Entry> d_newEntries;
  std::vector<Entry> d_delayedEntries;
  std::vector<Node> d_instances;
  std::vector<size_t> d_instantiatedTrail;
  std::vector<Scope> d_scopes;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIERS__QI_QUEUE_H */

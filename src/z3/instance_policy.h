/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * When the instances of the matches found are made.
 *
 * Not ported from Z3, whose qi_queue is the only policy: this separates the
 * policy from matching and from making an instance (Phase C, step 4 of
 * THEORY_BRANCH.md), so that Z3's queue (QiQueue) and a cvc5-like policy
 * are two implementations of it.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__INSTANCE_POLICY_H
#define CVC5__Z3__INSTANCE_POLICY_H

#include <iosfwd>
#include <unordered_map>
#include <utility>
#include <vector>

#include "expr/node.h"
#include "z3/checker.h"
#include "z3/types.h"

namespace cvc5::internal {
namespace z3 {

class Fingerprint;
class QuantifierManager;
class QuantifierServices;
class QuantifierStat;
struct Params;

/**
 * The policy behind QuantifierManager::addInstance. Matching (the MAM, the
 * quick checker) reports a match to the quantifier manager, which drops the
 * ones already made in scope (by their fingerprint) and inserts the others
 * here, with the generation of their terms. The policy decides when each is
 * made; this base class makes it.
 */
class InstancePolicy
{
 public:
  InstancePolicy(QuantifierManager& qm, QuantifierServices& ctx, Params& p);
  virtual ~InstancePolicy() = default;

  virtual void setup() {}

  /**
   * A new match: the quantifier and bindings are those of f, generation is
   * the largest generation of its terms and the quantifier's, and the top
   * generations are those of the enodes the pattern matched (0 if unknown).
   */
  virtual void insert(Fingerprint* f,
                      TNode pat,
                      uint32_t generation,
                      uint32_t minTopGeneration,
                      uint32_t maxTopGeneration) = 0;

  /** Make the instances due during propagation. */
  virtual void instantiate() = 0;

  /** Whether instantiate has something to do. */
  virtual bool hasWork() const = 0;

  /**
   * Make the instances due at a final check. Returns true if there is none,
   * i.e. the final check succeeds.
   */
  virtual bool finalCheckEh() = 0;

  virtual void initSearchEh() = 0;
  virtual void pushScope() = 0;
  virtual void popScope(size_t numScopes) = 0;
  virtual void reset() = 0;

 protected:
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
   * bindings, counted as made; or null if it is not to be made: the
   * instance rewrites to true, or, with --z3-qi-permanent, it is still
   * asserted (and is then made a root again with --z3-qi-permanent-local).
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

 private:
  /**
   * With --z3-qi-permanent, the instances asserted as lemmas that survive
   * backtracking, which are not asserted again when matching finds them
   * again, each with the formula asserted for it.
   */
  std::unordered_map<Node, Node> d_permanentInstances;
};

/**
 * Every match is made, with no cost and no threshold; an instance's terms
 * get the generation of the match plus one, as cvc5's instantiation levels
 * count, and the instance checker still applies, as cvc5's
 * --inst-no-entail does. What remains is when:
 * - eagerly (--z3-qi-policy=eager), at the next propagation, which is Z3's
 *   timing without its triage;
 * - in rounds (--z3-qi-policy=cvc5), at final checks, every match found
 *   since, which is cvc5's timing. Matching itself stays incremental.
 */
class Cvc5InstancePolicy : public InstancePolicy
{
 public:
  Cvc5InstancePolicy(QuantifierManager& qm,
                     QuantifierServices& ctx,
                     Params& p,
                     bool eager);

  void insert(Fingerprint* f,
              TNode pat,
              uint32_t generation,
              uint32_t minTopGeneration,
              uint32_t maxTopGeneration) override;
  void instantiate() override;
  bool hasWork() const override { return !d_new.empty(); }
  bool finalCheckEh() override;
  void initSearchEh() override { d_new.clear(); }
  void pushScope() override;
  void popScope(size_t numScopes) override;
  void reset() override;

 private:
  struct Entry
  {
    Fingerprint* d_qb;
    uint32_t d_generation;
    bool d_instantiated;
    Entry(Fingerprint* f, uint32_t g)
        : d_qb(f), d_generation(g), d_instantiated(false)
    {
    }
  };
  struct Scope
  {
    size_t d_roundEntriesLim;
    size_t d_instantiatedTrailLim;
  };
  /**
   * Make the instance of the entry. Returns false if the search must stop
   * making instances (cancellation, resource limits, the instance limit).
   */
  bool make(Entry& e);

  /** Whether matches are made at the next propagation, else in rounds. */
  bool d_eager;
  /** The matches to make at the next propagation (eager). */
  std::vector<Entry> d_new;
  /**
   * The matches to make at final checks (in rounds), in the scope where
   * they were found; one made in a scope that is popped is made again.
   */
  std::vector<Entry> d_roundEntries;
  std::vector<size_t> d_instantiatedTrail;
  std::vector<Scope> d_scopes;
  /** How many instances were made. */
  uint64_t d_numInstances;
  /** Instances made since the resource limits were last checked. */
  size_t d_sinceLastCheck;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__INSTANCE_POLICY_H */

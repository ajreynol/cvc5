/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The queue of pending instances of eager E-matching.
 *
 * A port of z3's smt/qi_queue.{h,cpp} together with the duplicate filter of
 * smt/fingerprints.{h,cpp}. The queue decides, for each match the matching
 * abstract machine reports, whether the instance is created now or delayed
 * until final check, based on its cost. See
 * theory/quantifiers/eager/README.md sections 2.4 and 5.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__INST_QUEUE_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__INST_QUEUE_H

#include <map>
#include <set>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/eager/mam.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

/**
 * Where instances go. Implemented by the inner SMT solver, and (for bring-up)
 * by a sink that forwards to cvc5's lemma channel.
 */
class InstanceSink
{
 public:
  virtual ~InstanceSink() {}
  /**
   * Add the instance of q obtained by substituting terms for its bound
   * variables. lemma is (or (not q) body), already rewritten. generation is
   * the generation to assign to the terms the instance introduces.
   */
  virtual void addInstance(TNode q,
                           const std::vector<Node>& terms,
                           TNode lemma,
                           uint32_t generation) = 0;
};

/**
 * Decides whether an instance is worth creating now, given the current
 * assignment. z3's analogue is smt::quick_checker, used through
 * qi.quick_checker and qi.promote_unsat: an instance whose body is already
 * false under the assignment is a conflict and is worth creating whatever its
 * cost, while one whose body is not yet determined only adds work.
 */
class InstanceEvaluator
{
 public:
  virtual ~InstanceEvaluator() {}
  /** Is the instance whose (substituted, rewritten) body is body worth it? */
  virtual bool isUseful(TNode body) = 0;
};

/**
 * The duplicate filter: the set of (quantified formula, bindings up to
 * equality) pairs that have already been turned into an instance. This is the
 * only duplicate filter of eager E-matching; it is deliberately not shared
 * with cvc5's lazy instantiation.
 *
 * z3: class fingerprint_set, used through context::add_fingerprint.
 */
class Fingerprints
{
 public:
  Fingerprints(Trail& trail);
  /**
   * Record that q was instantiated with the given bindings, using the
   * representative of each binding. Returns false if it already was.
   */
  bool add(TNode q, const std::vector<ENode*>& bindings);
  /** The number of fingerprints */
  size_t size() const { return d_fps.size(); }

 private:
  Trail& d_trail;
  std::set<std::pair<Node, std::vector<Node>>> d_fps;
};

/**
 * The instance queue.
 */
class InstQueue : protected EnvObj, public MamListener
{
 public:
  InstQueue(Env& env, Trail& trail);
  ~InstQueue();

  /** Set the sink, which must outlive this object */
  void setSink(InstanceSink* s) { d_sink = s; }
  /**
   * Set the evaluator that decides which instances are worth creating, or
   * nullptr to create all of them. It must outlive this object.
   */
  void setEvaluator(InstanceEvaluator* e) { d_eval = e; }

  //--------------------------------------------------- MamListener
  /** z3: quantifier_manager::imp::add_instance */
  void onMatch(TNode q,
               TNode pat,
               const std::vector<ENode*>& bindings,
               uint32_t maxGeneration,
               uint32_t minTopGeneration,
               uint32_t maxTopGeneration) override;
  //----------------------------------------------- end MamListener

  /** Is there an entry waiting to be processed? z3: qi_queue::has_work */
  bool hasWork() const { return !d_newEntries.empty(); }
  /**
   * Process the new entries, creating the cheap instances and delaying the
   * expensive ones. z3: qi_queue::instantiate().
   */
  void instantiate();
  /**
   * Create the delayed instances whose cost is below the lazy threshold.
   * Returns true if nothing was done. z3: qi_queue::final_check_eh.
   */
  bool finalCheck();
  /** Drop the pending entries, called when a scope is popped */
  void clearWork();

  /** Statistics, for -t eager-inst */
  struct Stats
  {
    /** matches reported by the machine */
    uint64_t d_numMatches = 0;
    /** matches that were duplicates */
    uint64_t d_numDuplicates = 0;
    /** instances created eagerly */
    uint64_t d_numInstances = 0;
    /** instances created at final check */
    uint64_t d_numLazyInstances = 0;
    /** instances that simplified to true */
    uint64_t d_numTrivial = 0;
    /** instances the evaluator rejected */
    uint64_t d_numNotUseful = 0;
  };
  const Stats& getStats() const { return d_stats; }

 private:
  /** One pending instance. z3: struct qi_queue::entry */
  struct Entry
  {
    Node d_quant;
    Node d_pattern;
    /** the bindings, one per bound variable */
    std::vector<Node> d_terms;
    double d_cost;
    uint32_t d_generation;
    bool d_instantiated;
  };
  /**
   * The cost of an instance. z3 evaluates a user-specified arithmetic
   * expression over the variables listed in qi_queue::init_parser_vars; we
   * implement its default, (+ weight generation).
   */
  double getCost(TNode q, uint32_t generation) const;
  /**
   * The generation to assign to the terms the instance introduces. z3
   * evaluates qi.new_gen; its default behaviour is generation + 1.
   */
  uint32_t getNewGeneration(TNode q, uint32_t generation, double cost) const;
  /** The weight of q. z3: quantifier::get_weight */
  uint32_t getWeight(TNode q) const;
  /** Create the instance of ent. z3: qi_queue::instantiate(entry&) */
  void instantiate(Entry& ent);

  /** The trail */
  Trail& d_trail;
  /** The sink */
  InstanceSink* d_sink;
  /** The evaluator, or nullptr if every instance is created */
  InstanceEvaluator* d_eval;
  /** The duplicate filter */
  Fingerprints d_fps;
  /** Entries that have not been processed yet. z3: m_new_entries */
  std::vector<Entry> d_newEntries;
  /** Entries that were too expensive. z3: m_delayed_entries */
  std::vector<Entry> d_delayed;
  /** The cost above which an instance is delayed. z3: qi.eager_threshold */
  double d_eagerThreshold;
  /** The cost above which a delayed instance is never created */
  double d_lazyThreshold;
  /** Statistics */
  Stats d_stats;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif

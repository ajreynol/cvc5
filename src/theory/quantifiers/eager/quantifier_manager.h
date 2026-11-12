/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Quantifier reasoning for the eager E-matching core.
 *
 * Ported from Z3: src/smt/smt_quantifier.h, src/smt/smt_quantifier.cpp.
 * Z3 is Copyright (c) Microsoft Corporation and licensed under the MIT
 * License, see licenses/z3-LICENSE.
 *
 * The manager owns the E-matching engines (Mam), the queue of delayed
 * instantiations (QiQueue) and the generations of the quantifiers. Of Z3's
 * plugins, only E-matching is ported. The core calls
 * into it when a quantifier is asserted, when equivalence classes merge, when
 * a term becomes relevant, and at final check.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__QUANTIFIER_MANAGER_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__QUANTIFIER_MANAGER_H

#include <memory>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/eager/fingerprints.h"
#include "theory/quantifiers/eager/qi_queue.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

class Mam;
class ENode;
class SmtContext;

/**
 * The quantifiers of the core, Z3's quantifier_manager: their generations,
 * and the E-matching engine and instantiation queue that make their
 * instances.
 */
class QuantifierManager : protected EnvObj
{
 public:
  /** The quantifier manager of the core ctx. */
  QuantifierManager(Env& env, SmtContext& ctx);
  ~QuantifierManager();

  /** Register the quantifier q, internalized with the given generation. */
  void add(TNode q, uint32_t generation);
  /**
   * Unregister q, the last quantifier added, whose Boolean variable is
   * deleted on backtracking.
   */
  void del(TNode q);
  /** Whether no quantifier is registered. */
  bool empty() const { return d_quantifiers.empty(); }

  /** The generation of q, or 0 if q is not registered. */
  uint32_t getGeneration(TNode q) const;

  /**
   * Record and enqueue an instantiation of q found by matching, with the
   * bindings, the maximum generation of whose enodes is maxGeneration.
   * Returns true if the instance is new.
   */
  bool addInstance(TNode q,
                   size_t numBindings,
                   ENode* const* bindings,
                   uint32_t maxGeneration);

  /** Discard the queue's pending instances, at the start of a search. */
  void initSearch();
  /** Invoked whenever q is assigned to true. */
  void notifyAssigned(TNode q);
  /** Invoked whenever n1 and n2 are merged into the same class. */
  void notifyMerge(ENode* n1, ENode* n2);
  /** Invoked whenever n is marked as relevant. */
  void notifyRelevant(ENode* n);
  /** Whether the queue or the matchers have pending work. */
  bool canPropagate() const;
  /**
   * Run the matchers, if a quantifier was asserted, then process the queued
   * instances: make the cheap or conflicting ones, and drop the others.
   */
  void propagate();

  /**
   * Discard the pending work of the matchers and the queue, before the
   * scopes are popped. Their scoped state is in the trail stack of the
   * context, and is popped with it.
   */
  void notifyPop();

 private:
  /** The core. */
  SmtContext& d_context;
  /** When the instances of the matches found are made. */
  QiQueue d_queue;
  /** The fingerprints of the instances made in the current scopes. */
  FingerprintSet d_fingerprints;
  /** The generation of each quantifier, as Z3's quantifier_stat keeps it. */
  std::unordered_map<Node, uint32_t> d_generations;
  /** The registered quantifiers, in the order they were added. */
  std::vector<Node> d_quantifiers;
  /** The E-matching engine. */
  std::unique_ptr<Mam> d_mam;
  /** Whether a quantifier was asserted. */
  bool d_active;
};

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER__QUANTIFIER_MANAGER_H */

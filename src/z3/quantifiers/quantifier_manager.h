/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Quantifier reasoning for the ported Z3 core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * files src/smt/smt_quantifier.h and src/smt/smt_quantifier.cpp, recast in
 * cvc5 style.
 *
 * The manager owns the E-matching engines (Mam), the queue of delayed
 * instantiations (QiQueue) and the generations of the quantifiers. Of Z3's
 * plugins, only E-matching is ported. The core calls
 * into it when a quantifier is asserted, when equivalence classes merge, when
 * a term becomes relevant, and at final check.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__QUANTIFIERS__QUANTIFIER_MANAGER_H
#define CVC5__Z3__QUANTIFIERS__QUANTIFIER_MANAGER_H

#include <memory>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "z3/quantifiers/fingerprints.h"
#include "z3/quantifiers/qi_queue.h"

namespace cvc5::internal {
namespace z3 {

class Mam;
class ENode;
class SmtContext;

class QuantifierManager : protected EnvObj
{
 public:
  QuantifierManager(Env& env, SmtContext& ctx);
  ~QuantifierManager();

  void add(TNode q, uint32_t generation);
  void del(TNode q);
  bool empty() const { return d_quantifiers.empty(); }

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

  void initSearch();
  /** Invoked whenever q is assigned to true. */
  void notifyAssigned(TNode q);
  /** Invoked whenever n1 and n2 are merged into the same class. */
  void notifyMerge(ENode* n1, ENode* n2);
  /** Invoked whenever n is marked as relevant. */
  void notifyRelevant(ENode* n);
  /** Match the lazy multi-patterns. Returns true if this made no progress. */
  bool finalCheck();

  bool canPropagate() const;
  void propagate();

  /**
   * Discard the pending work of the matchers and the queue, before the
   * scopes are popped. Their scoped state is in the trail stack of the
   * context, and is popped with it.
   */
  void notifyPop();

 private:
  SmtContext& d_context;
  /** When the instances of the matches found are made. */
  QiQueue d_queue;
  /** The fingerprints of the instances made in the current scopes. */
  FingerprintSet d_fingerprints;
  /** The generation of each quantifier, as Z3's quantifier_stat keeps it. */
  std::unordered_map<Node, uint32_t> d_generations;
  std::vector<Node> d_quantifiers;
  /** The E-matching engine for the patterns matched eagerly. */
  std::unique_ptr<Mam> d_mam;
  /** The E-matching engine for the multi-patterns matched at final check. */
  std::unique_ptr<Mam> d_lazyMam;
  /** How many times the lazy patterns were matched in this search. */
  size_t d_lazyMatchingIdx;
  /** Whether a quantifier was asserted. */
  bool d_active;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIERS__QUANTIFIER_MANAGER_H */

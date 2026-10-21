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
 * instantiations (QiQueue) and the per-quantifier statistics. Of Z3's
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
#include "z3/quantifiers/fingerprints.h"
#include "z3/quantifiers/qi_queue.h"
#include "z3/quantifiers/quantifier_stat.h"
#include "z3/util/types.h"

namespace cvc5::internal {
namespace z3 {

class Mam;
class SmtContext;

class QuantifierManager
{
 public:
  QuantifierManager(SmtContext& ctx);
  ~QuantifierManager();

  void add(TNode q, uint32_t generation);
  void del(TNode q);
  bool empty() const { return d_quantifiers.empty(); }

  QuantifierStat* getStat(TNode q) const;

  /**
   * The quantifier whose node id is the given one. Fingerprints key on the
   * id rather than on a pointer, so this maps back.
   */
  TNode getQuantifierById(uint64_t id) const;
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

  void initSearchEh();
  /** Invoked whenever q is assigned to true. */
  void assignEh(TNode q);
  /** Invoked whenever n1 and n2 are merged into the same class. */
  void addEqEh(ENode* n1, ENode* n2);
  /** Invoked whenever n is marked as relevant. */
  void relevantEh(ENode* n);
  FinalCheckStatus finalCheckEh(bool full);

  bool canPropagate() const;
  void propagate();

  void push();
  void pop(size_t numScopes);

 private:
  /** Push the scopes of the matchers and the queue. */
  void pushCore();

  SmtContext& d_context;
  /** When the instances of the matches found are made. */
  QiQueue d_queue;
  /** The fingerprints of the instances made in the current scopes. */
  FingerprintSet d_fingerprints;
  std::unordered_map<Node, QuantifierStat*> d_quantifierStat;
  std::unordered_map<uint64_t, Node> d_id2Quant;
  QuantifierStatGen d_qstatGen;
  std::vector<Node> d_quantifiers;
  /** The E-matching engine for the patterns matched eagerly. */
  std::unique_ptr<Mam> d_mam;
  /** The E-matching engine for the multi-patterns matched at final check. */
  std::unique_ptr<Mam> d_lazyMam;
  /** How many times the lazy patterns were matched in this search. */
  size_t d_lazyMatchingIdx;
  /** Whether a quantifier was asserted. */
  bool d_active;
  /**
   * The scopes pushed before the first quantifier was added, which the
   * matchers and the queue only get then, so that a problem without
   * quantifiers pays nothing.
   */
  size_t d_lazyScopes;
  bool d_lazy;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIERS__QUANTIFIER_MANAGER_H */

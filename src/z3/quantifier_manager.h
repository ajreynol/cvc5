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
 * The manager owns the E-matching engine (Mam), the queue of delayed
 * instantiations (QiQueue) and the per-quantifier statistics. The core calls
 * into it when a quantifier is asserted, when equivalence classes merge, when
 * a term becomes relevant, and at final check.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__QUANTIFIER_MANAGER_H
#define CVC5__Z3__QUANTIFIER_MANAGER_H

#include <memory>
#include <ostream>
#include <vector>

#include "expr/node.h"
#include "z3/params.h"
#include "z3/quantifier_stat.h"
#include "z3/types.h"

namespace cvc5::internal {
namespace z3 {

class QuantifierManagerPlugin;
class SmtContext;

class QuantifierManager
{
 public:
  QuantifierManager(SmtContext& ctx, Params& fp);
  ~QuantifierManager();

  SmtContext& getContext() const;

  void add(TNode q, uint32_t generation);
  void del(TNode q);
  bool empty() const;

  bool isShared(ENode* n) const;

  QuantifierStat* getStat(TNode q) const;

  /**
   * The quantifier whose node id is the given one. Fingerprints key on the
   * id rather than on a pointer, so this maps back.
   */
  TNode getQuantifierById(uint64_t id) const;
  uint32_t getGeneration(TNode q) const;

  /**
   * Record and enqueue an instantiation of q found by matching pat against
   * the bindings. Returns true if the instance is new.
   */
  bool addInstance(TNode q,
                   TNode pat,
                   size_t numBindings,
                   ENode* const* bindings,
                   uint32_t maxGeneration,
                   uint32_t minTopGeneration,
                   uint32_t maxTopGeneration,
                   std::vector<std::pair<ENode*, ENode*>>& usedENodes);

  bool addInstance(TNode q,
                   size_t numBindings,
                   ENode* const* bindings,
                   uint32_t generation = 0);

  void initSearchEh();
  void assignEh(TNode q);
  void addEqEh(ENode* n1, ENode* n2);
  void relevantEh(ENode* n);
  FinalCheckStatus finalCheckEh(bool full);
  void restartEh();

  bool canPropagate() const;
  void propagate();

  enum CheckModelResult
  {
    SAT,
    UNKNOWN,
    RESTART
  };

  bool modelBased() const;
  bool hasQuantifiers() const;
  /** True if model based instantiation may instantiate q. */
  bool mbqiEnabled(TNode q) const;
  CheckModelResult checkModel();

  void push();
  void pop(size_t numScopes);
  void reset();

  void print(std::ostream& out) const;

  /** Print the per-quantifier instantiation counts, as Z3's profile does. */
  void printStats(std::ostream& out) const;

  const std::vector<Node>& quantifiers() const;
  size_t numQuantifiers() const;

 private:
  struct Imp;
  std::unique_ptr<Imp> d_imp;
  size_t d_lazyScopes;
  bool d_lazy;
  void flush();
};

/**
 * The strategy half of quantifier reasoning: Z3 separates the bookkeeping
 * (QuantifierManager) from the instantiation strategy, which is what lets
 * E-matching and model based instantiation be swapped.
 */
class QuantifierManagerPlugin
{
 public:
  virtual ~QuantifierManagerPlugin() = default;

  virtual void setManager(QuantifierManager& qm) = 0;

  virtual void add(TNode q) = 0;
  virtual void del(TNode q) = 0;

  virtual bool isShared(ENode* n) const = 0;

  /** Invoked whenever q is assigned to true. */
  virtual void assignEh(TNode q) = 0;
  /** Invoked whenever n1 and n2 are merged into the same class. */
  virtual void addEqEh(ENode* n1, ENode* n2) = 0;
  /** Invoked whenever n is marked as relevant. */
  virtual void relevantEh(ENode* n) = 0;
  /** Invoked when a new search starts. */
  virtual void initSearchEh() = 0;
  /** The final check event handler. */
  virtual FinalCheckStatus finalCheckEh(bool full) = 0;
  /** Invoked whenever the solver restarts. */
  virtual void restartEh() = 0;

  /** True if the plugin can propagate information back into the core. */
  virtual bool canPropagate() const = 0;
  virtual void propagate() = 0;

  /** True if the plugin is model based. */
  virtual bool modelBased() const = 0;

  /** True if model based instantiation may instantiate q. */
  virtual bool mbqiEnabled(TNode /*q*/) const { return true; }

  /**
   * The core invokes this to check whether the candidate model satisfies the
   * quantifiers.
   */
  virtual QuantifierManager::CheckModelResult checkModel() = 0;

  virtual void push() = 0;
  virtual void pop(size_t numScopes) = 0;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIER_MANAGER_H */

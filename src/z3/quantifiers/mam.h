/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The Matching Abstract Machine: Z3's E-matching engine.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/mam.h, and recast in cvc5 style.
 *
 * Patterns are compiled into code trees whose instructions bind, compare and
 * filter enodes, and common prefixes of different patterns are shared. The
 * machine is driven incrementally: as terms become relevant and as classes
 * merge, only the affected code trees are re-executed.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__QUANTIFIERS__MAM_H
#define CVC5__Z3__QUANTIFIERS__MAM_H

#include <memory>
#include <ostream>
#include <utility>
#include <vector>

#include "expr/node.h"

namespace cvc5::internal {
namespace z3 {

class QuantifierManager;
class ENode;
class SmtContext;

class MamImpl;

/**
 * The matching abstract machine: the code trees of the patterns and their
 * interpreter, which are hidden in mam.cpp.
 */
class Mam
{
 public:
  Mam(SmtContext& ctx, QuantifierManager& qm);
  ~Mam();

  /** Compile the multi-pattern mp of quantifier q into the code trees. */
  void addPattern(TNode q, TNode mp);

  /**
   * Discard the pending matching work, before the scopes are popped. The
   * code trees are in the trail stack of the context, and are popped with
   * it.
   */
  void notifyPop();

  /** Execute the pending matching work. */
  void match();

  /** Re-execute every code tree from scratch. */
  void rematch();

  bool hasWork() const;

  /** Notification that n became relevant. */
  void notifyRelevant(ENode* n, bool lazy);

  /** Notification that the classes of r1 and r2 merged. */
  void notifyMerge(ENode* r1, ENode* r2);

 private:
  std::unique_ptr<MamImpl> d_impl;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIERS__MAM_H */

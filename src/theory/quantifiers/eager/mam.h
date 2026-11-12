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
 * Ported from Z3: src/smt/mam.h.
 * Z3 is Copyright (c) Microsoft Corporation and licensed under the MIT
 * License, see licenses/z3-LICENSE.
 *
 * Patterns are compiled into code trees whose instructions bind, compare and
 * filter enodes, and common prefixes of different patterns are shared. The
 * machine is driven incrementally: as terms become relevant and as classes
 * merge, only the affected code trees are re-executed.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__MAM_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__MAM_H

#include <memory>
#include <ostream>
#include <utility>
#include <vector>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

class QuantifierManager;
class ENode;
class SmtContext;

/** The implementation of Mam, in mam.cpp. */
class MamImpl;

/**
 * The matching abstract machine: the code trees of the patterns and their
 * interpreter, which are hidden in mam.cpp.
 */
class Mam
{
 public:
  /** Make the machine of ctx, which reports its matches to qm. */
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

  /** True if a code tree has candidates or a new pattern is not matched yet. */
  bool hasWork() const;

  /** Notification that n became relevant. */
  void notifyRelevant(ENode* n);

  /** Notification that the classes of r1 and r2 merged. */
  void notifyMerge(ENode* r1, ENode* r2);

 private:
  /** The implementation. */
  std::unique_ptr<MamImpl> d_impl;
};

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER__MAM_H */

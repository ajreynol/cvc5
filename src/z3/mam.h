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

#ifndef CVC5__Z3__MAM_H
#define CVC5__Z3__MAM_H

#include <ostream>
#include <utility>
#include <vector>

#include "expr/node.h"
#include "z3/types.h"

namespace cvc5::internal {
namespace z3 {

class SmtContext;

class Mam
{
 public:
  Mam(SmtContext& ctx) : d_context(ctx) {}

  virtual ~Mam() = default;

  /** Compile the multi-pattern mp of quantifier q into the code trees. */
  virtual void addPattern(TNode q, TNode mp) = 0;

  virtual void pushScope() = 0;

  virtual void popScope(size_t numScopes) = 0;

  /** Execute the pending matching work. */
  virtual void match() = 0;

  /** Re-execute every code tree from scratch. */
  virtual void rematch(bool useIrrelevant = false) = 0;

  virtual bool hasWork() const = 0;

  /** Notification that n became relevant. */
  virtual void relevantEh(ENode* n, bool lazy) = 0;

  /** Notification that the classes of r1 and r2 merged. */
  virtual void addEqEh(ENode* r1, ENode* r2) = 0;

  virtual void reset() = 0;

  virtual void print(std::ostream& out) = 0;

  /** Report a match to the quantifier manager. */
  virtual void onMatch(TNode q,
                       TNode pat,
                       size_t numBindings,
                       ENode* const* bindings,
                       uint32_t maxGeneration,
                       std::vector<std::pair<ENode*, ENode*>>& usedENodes) = 0;

  virtual bool isShared(ENode* n) const = 0;

 protected:
  SmtContext& d_context;
};

Mam* mkMam(SmtContext& ctx);

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__MAM_H */

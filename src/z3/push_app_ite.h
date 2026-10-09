/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Lifting if-then-else out of non-ground applications.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/ast/rewriter/push_app_ite.{h,cpp}, and recast in cvc5 style.
 *
 * This is Z3's ng_push_app_ite_rw, which asserted_formulas::reduce() runs as
 * its ng_lift_ite step:
 *
 *   (f s (ite c t1 t2)) ==> (ite c (f s t1) (f s t2))
 *
 * for an application with at least one non-ground argument. setup_AUFLIA,
 * which these logics reach through setup_unknown, sets m_ng_lift_ite to
 * LI_CONSERVATIVE; unlike the eager instantiation threshold, this override is
 * live, because setup_context runs before internalize_assertions calls
 * reduce(). The effect is on quantifier bodies, where it changes which terms
 * exist for a trigger to match.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__PUSH_APP_ITE_H
#define CVC5__Z3__PUSH_APP_ITE_H

#include <unordered_map>

#include "expr/node.h"

namespace cvc5::internal {

class NodeManager;

namespace z3 {

class NgPushAppIte
{
 public:
  /**
   * In conservative mode an application is a target only if exactly one of
   * its arguments is a non-Boolean if-then-else; otherwise if at least one is.
   */
  NgPushAppIte(NodeManager* nm, bool conservative)
      : d_nm(nm), d_conservative(conservative)
  {
  }

  /** The assertion n with if-then-else lifted out of non-ground terms. */
  Node apply(TNode n);

 private:
  /** The rewriter's traversal: arguments first, then reduceApp. */
  Node applyRec(TNode n);
  /** push_app_ite_cfg::reduce_app on n, whose arguments are already done. */
  Node reduceApp(TNode n);
  /** ng_push_app_ite_cfg::is_target. */
  bool isTarget(TNode n) const;

  NodeManager* d_nm;
  bool d_conservative;
  std::unordered_map<Node, Node> d_cache;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__PUSH_APP_ITE_H */

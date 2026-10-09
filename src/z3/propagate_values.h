/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Propagating the values of unit assertions into the other assertions.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/solver/assertions/asserted_formulas.cpp (propagate_values,
 * update_substitution, is_gt), and recast in cvc5 style.
 *
 * This is the first step of asserted_formulas::reduce(). Every assertion is
 * rewritten under the substitution the assertions before it induce -- a
 * ground equality oriented towards its smaller side, a negated atom to false,
 * any other assertion to true -- once forwards and once backwards. On Verus
 * queries it is what turns each fuel-guarded axiom, (or (not (fuel_bool f))
 * Q) with (fuel_bool f) asserted, into the top-level quantifier Q. cvc5's
 * preprocessor does not do the same: it leaves the guard in place, and the
 * core then reaches the quantifier only through propagation and relevancy,
 * which changes the order everything after it happens in.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__PROPAGATE_VALUES_H
#define CVC5__Z3__PROPAGATE_VALUES_H

#include <unordered_map>
#include <vector>

#include "expr/node.h"

namespace cvc5::internal {
namespace z3 {

class AssertionRewriter;

class PropagateValues
{
 public:
  PropagateValues(AssertionRewriter& rw) : d_rw(rw) {}

  /** Apply propagate_values to fmls in place; the number changed. */
  size_t apply(std::vector<Node>& fmls);

 private:
  /** propagate_values(i): rewrite fmls[i], then extend the substitution. */
  bool propagate(std::vector<Node>& fmls, size_t i);
  /** n under the current substitution; patterns are left alone. */
  Node substitute(TNode n, std::unordered_map<TNode, Node>& cache);
  /** update_substitution. */
  void updateSubstitution(TNode n);
  /** is_gt: a Knuth-Bendix style ordering, with values smallest. */
  static bool isGt(TNode lhs, TNode rhs);

  AssertionRewriter& d_rw;
  /** the substitution of the current pass */
  std::unordered_map<Node, Node> d_subst;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__PROPAGATE_VALUES_H */

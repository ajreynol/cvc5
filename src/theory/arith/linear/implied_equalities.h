/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The equalities implied by the rows of the tableau whose variables are fixed
 * but one or two.
 */

#include "cvc5_private.h"

#pragma once

#include <vector>

#include "context/cdhashmap.h"
#include "smt/env_obj.h"
#include "theory/arith/linear/arithvar.h"
#include "theory/arith/linear/matrix.h"
#include "util/hash.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

class ArithCongruenceManager;
class ArithVariables;
class Tableau;

/**
 * Finds the equalities implied by the rows of the tableau once their other
 * variables are fixed, i.e. have equal lower and upper bounds, as Z3's cheap
 * equalities (theory_arith_eq.h) do. A row whose variables are fixed but
 * - x, fixes x to a value c: x = c;
 * - x and y, of opposite coefficients, relates them by an offset: x = y + k.
 *   With k = 0, x = y; two variables with the same offset from y are equal.
 *
 * The congruence manager asserts the equalities between terms to the
 * equality engine, explained by the bounds of the fixed variables. They are
 * then known to the other theories without a split of theory combination,
 * and to E-matching.
 *
 * The search is incremental: it visits the rows of the variables whose
 * bounds were asserted since the last call to check.
 */
class ImpliedEqualities : protected EnvObj
{
 public:
  ImpliedEqualities(Env& env,
                    const ArithVariables& vars,
                    const Tableau& tableau,
                    ArithCongruenceManager& cm);

  /** A bound of x was asserted. */
  void notifyBound(ArithVar x) { d_bounded.push_back(x); }
  /**
   * Find the equalities implied by the rows of the variables fixed since the
   * last call, and assert them to the equality engine. The tableau must be
   * consistent with the bounds, i.e. the simplex found no conflict.
   */
  void check();

 private:
  /** A linear combination sum_j c_j * v_j of fixed variables v_j. */
  using FixedSum = std::vector<std::pair<ArithVar, Rational>>;
  /** x = y + k, where x - y = s for a fixed sum s, of value k. */
  struct Offset
  {
    ArithVar d_var = ARITHVAR_SENTINEL;
    FixedSum d_sum;
  };
  using OffsetKey = std::pair<ArithVar, Rational>;
  using OffsetKeyHash = PairHashFunction<ArithVar,
                                         Rational,
                                         std::hash<ArithVar>,
                                         RationalHashFunction>;

  /**
   * Is x a term? An auxiliary variable of the tableau, which stands for a sum
   * of terms, is one only if the sum is a term of the equality engine.
   */
  bool isTerm(ArithVar x) const;
  /** Is x fixed? */
  bool isFixed(ArithVar x) const;
  /** The value of the fixed variable x. */
  const Rational& fixedValue(ArithVar x) const;
  /** Find the equalities implied by the row rid. */
  void checkRow(RowIndex rid);
  /** x = y + k by sum, and record it. */
  void addOffset(ArithVar x,
                 ArithVar y,
                 const Rational& k,
                 const FixedSum& sum);
  /**
   * Assert x = y, where x - y = sum, if x and y are terms. If y is
   * ARITHVAR_SENTINEL, assert x = k, where x = sum, of value k.
   */
  void assertEquality(ArithVar x,
                      ArithVar y,
                      const Rational& k,
                      const FixedSum& sum);

  /** The variables. */
  const ArithVariables& d_vars;
  /** The tableau. */
  const Tableau& d_tableau;
  /** The congruence manager, which asserts the equalities. */
  ArithCongruenceManager& d_cm;
  /** The variables whose bounds were asserted since the last check. */
  std::vector<ArithVar> d_bounded;
  /** Maps (y, k) to x, where x = y + k. */
  context::CDHashMap<OffsetKey, Offset, OffsetKeyHash> d_offsets;
};

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal

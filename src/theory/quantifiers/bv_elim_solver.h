/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Solving bit-vector literals using elimination sets.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__BV_ELIM_SOLVER_H
#define CVC5__THEORY__QUANTIFIERS__BV_ELIM_SOLVER_H

#include <vector>

#include "expr/node.h"
#include "theory/quantifiers/bv_inverter.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * Solves bit-vector literals for a variable using elimination sets, as an
 * alternative to the invertibility conditions used by BvInverter.
 *
 * For a literal L(x, s, t) of the form (x <op> s) = t or (s <op> x) = t, the
 * approach of Niemetz et al, CAV 2018 (implemented in BvInverter) returns a
 * witness term (witness x. IC(s,t) => L(x, s, t)), where IC is the
 * invertibility condition for L, i.e. IC(s,t) <=> exists x. L(x, s, t).
 *
 * Instead, this class uses a finite set of terms E(s,t) = { u_1, ..., u_k },
 * not containing x, such that:
 *
 *   exists x. L(x, s, t)  <=>  L(u_1, s, t) or ... or L(u_k, s, t)
 *
 * This is an elimination set in the sense of Loos and Weispfenning. Using a
 * term from E(s,t) as an instantiation requires no witness terms and no
 * invertibility condition lemmas: instantiating with any term is sound, and
 * the property above is only required for completeness. Moreover, since the
 * current model M satisfies exists x. L(x, s, t) whenever M satisfies L, some
 * u_i in E(s,t) satisfies L in M, and hence we may choose one of the terms in a
 * model-guided way.
 *
 * The elimination sets we use for positive equalities, where n is the
 * bit-width of x, are the following:
 *
 *   Literal          Elimination set
 *   ~x = t           { ~t }
 *   -x = t           { -t }
 *   x + s = t        { t - s }
 *   x ^ s = t        { t ^ s }
 *   x * s = t        { (t udiv low(s)) * inv(s udiv low(s)) }
 *   x udiv s = t     { s * t }
 *   s udiv x = t     { s udiv t }
 *   x urem s = t     { t }
 *   s urem x = t     { s - t }
 *   x & s = t        { t }
 *   x | s = t        { t }
 *   x << s = t       { t >> s }
 *   x >> s = t       { t << s }
 *   x >>a s = t      { t << s, t }
 *   s << x = t       { lg(low(t)) - lg(low(s)), n }
 *   s >> x = t       { lg(hb(s)) - lg(hb(t)), n }
 *   s >>a x = t      { lg(hb(s ^ m)) - lg(hb(t ^ m)), n }
 *                      where m = s >>a (n-1)
 *   concat(.., x, ..) = t      { t[hi:lo] }, the corresponding extract of t
 *   sign_extend(x) = t         { t[n-1:0] }
 *
 * where:
 * - low(a) = a & -a is the lowest set bit of a (or 0 if a = 0).
 * - inv(a) is the multiplicative inverse of a modulo 2^n for odd a, computed
 *   by Newton iteration y_0 = a, y_{i+1} = y_i * (2 - a * y_i). Since
 *   a * a = 1 mod 8 for odd a, y_0 is correct on 3 bits, and each iteration
 *   doubles the number of correct bits, hence ceil(log2(n/3)) iterations
 *   suffice (4 for n = 64).
 *   Correctness: for s = 2^k * s' with s' odd, x * s = t has a solution iff
 *   2^k divides t, in which case (t / 2^k) * inv(s') is a solution. If s = 0,
 *   then low(s) = 0, and the term is 1, which is a solution iff t = 0.
 * - hb(a) is the highest set bit of a (or 0 if a = 0), computed by smearing
 *   a := a | (a >> 2^i) for 2^i < n, followed by a ^ (a >> 1).
 * - lg(p) is the base-2 logarithm of a power of two p (and 0 if p = 0),
 *   computed bit-parallel as zero-extend(concat_{j} redor(p & M_j)) where M_j
 *   is the mask of the bit positions whose index has its j^th bit set.
 * Intuitively, for the shift cases where x is the shift amount, the first term
 * is the difference between the positions of the lowest (resp. highest) set
 * bits of s and t, and the term n handles the cases where the result is fully
 * shifted out (e.g. t = 0). For the arithmetic shift right, xor-ing with the
 * sign mask m reduces to the logical case. Notice that the first term may be
 * "negative" when no solution exists, which is benign since only the
 * equivalence of the disjunction is required. Similarly for x >>a s = t, the
 * term t is required when s >= n and t = ~0.
 *
 * These were verified to be elimination sets exhaustively for bit-widths
 * 1 to 8. Furthermore, the quantifier-free queries
 *   L(x, s, t) and not L(u_1, s, t) and ... and not L(u_k, s, t)
 * were checked to be unsatisfiable for bit-widths 16, 32 and 64, where the
 * queries for multiplication and udiv at width 32 and 64, and x urem s at
 * width 64, are beyond the reach of bit-blasting but have easy direct proofs:
 * - x udiv s = t: a solution x has the form s * t + r without overflow, hence
 *   s * t is also a solution; if s = 0, then t = ~0 and any x is a solution.
 * - s udiv x = t: s udiv t is the largest solution x when one exists (for
 *   t = 0 the only solution is x > s, for t = ~0 the solution x = 0 coincides
 *   when s udiv ~0 = 0, or else s = ~0 and x = 1 = s udiv t).
 * - x urem s = t: if s = 0 then x = t, otherwise t < s and t urem s = t.
 *
 * For nested literals, e.g. f(g(x), s) = t, we solve for the term g(x) and
 * then for x. As with witness terms, choosing a term u from the elimination
 * set of f does not guarantee that g(x) = u is solvable. To mitigate this, we
 * use the model: we prefer the term u whose value in M is the value of g(x)
 * in M, which ensures that g(x) = u is solvable in M (by the value of x in M).
 *
 * Literals not of the above forms (disequalities, inequalities, unhandled
 * operators) are currently not handled by this class. Note that by default,
 * the BV instantiator projects inequalities and disequalities to equalities
 * (see option --cegqi-bv-ineq). Small elimination sets also exist for
 * disequalities, e.g. x * s != t has { 0, 1 }, x & s != t has { ~t },
 * x urem s != t has { t + 1 } (verified exhaustively for bit-widths 4 to 6),
 * which are left as future work.
 */
class BvElimSolver
{
 public:
  BvElimSolver() {}
  ~BvElimSolver() {}
  /**
   * Solve for sv in lit, where lit.path = sv. If this function returns a
   * non-null node t, then t does not contain sv and is a term that can be used
   * to instantiate sv. This is analogous to BvInverter::solveBvLit.
   *
   * @param sv The solve variable.
   * @param lit The literal, which is expected to be a positive equality.
   * @param path The path to sv in lit, outermost term index last. This vector
   * is modified by this call.
   * @param svVal The value of the variable we are solving for in the current
   * model, or null if no such value is available.
   * @param m Used for querying the current model, may be null.
   * @return The chosen term, or null if lit is not handled.
   */
  Node solveBvLit(Node sv,
                  Node lit,
                  std::vector<uint32_t>& path,
                  Node svVal,
                  BvInverterQuery* m);
  /**
   * Get the elimination set for the equality svt = t with respect to the
   * index^th child of svt, as described above.
   *
   * @param svt The term containing the variable to solve for.
   * @param index The index of the child of svt we are solving for.
   * @param t The right hand side of the equality.
   * @param terms The terms of the elimination set are added to this vector.
   * @return true if we computed an elimination set for svt = t.
   */
  static bool getEqualityElimSet(Node svt,
                                 uint32_t index,
                                 Node t,
                                 std::vector<Node>& terms);

 private:
  /** Make the term a & -a */
  static Node mkLowBit(Node a);
  /** Make the term for the highest set bit of a */
  static Node mkHighBit(Node a);
  /** Make the multiplicative inverse of a, assuming a is odd */
  static Node mkOddInverse(Node a);
  /** Make the base-2 logarithm of p, assuming p is a power of two or zero */
  static Node mkLog2(Node p);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__BV_ELIM_SOLVER_H */

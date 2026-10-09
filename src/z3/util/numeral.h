/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The operations of Z3's rational class that cvc5's Rational does not have
 * under the same name.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), file
 * src/util/rational.h, and recast in cvc5 style. The arithmetic theory is
 * written against Z3's rational; these keep its bodies close to the original
 * while the numbers are cvc5's.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__NUMERAL_H
#define CVC5__Z3__UTIL__NUMERAL_H

#include "util/integer.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace z3 {

/** rational::is_int */
inline bool isInt(const Rational& r) { return r.isIntegral(); }

/** rational::is_neg, is_pos, is_nonneg, is_nonpos */
inline bool isNeg(const Rational& r) { return r.sgn() < 0; }
inline bool isPos(const Rational& r) { return r.sgn() > 0; }
inline bool isNonneg(const Rational& r) { return r.sgn() >= 0; }
inline bool isNonpos(const Rational& r) { return r.sgn() <= 0; }

/** rational::is_minus_one */
inline bool isMinusOne(const Rational& r) { return r.isNegativeOne(); }

/** floor(rational) and ceil(rational), as rationals. */
inline Rational floor(const Rational& r) { return Rational(r.floor()); }
inline Rational ceil(const Rational& r) { return Rational(r.ceiling()); }

/** numerator(rational) and denominator(rational), as rationals. */
inline Rational numerator(const Rational& r)
{
  return Rational(r.getNumerator());
}
inline Rational denominator(const Rational& r)
{
  return Rational(r.getDenominator());
}

/** gcd and lcm of two integral rationals. */
inline Rational gcd(const Rational& a, const Rational& b)
{
  return Rational(a.getNumerator().gcd(b.getNumerator()));
}
inline Rational lcm(const Rational& a, const Rational& b)
{
  return Rational(a.getNumerator().lcm(b.getNumerator()));
}

/** abs(rational) */
inline Rational abs(const Rational& r) { return r.abs(); }

/**
 * rational::is_big: true if the numerator or the denominator does not fit in
 * Z3's small integer representation, which is a machine int.
 */
inline bool isBig(const Rational& r)
{
  return !r.getNumerator().fitsSignedInt()
         || !r.getDenominator().fitsSignedInt();
}

/**
 * div(a, b) and mod(a, b) on integral rationals. Z3's mpz div adjusts a
 * truncating division so that the remainder is non-negative, i.e. it is
 * Euclidean division, as mod is.
 */
inline Rational intDiv(const Rational& a, const Rational& b)
{
  return Rational(a.getNumerator().euclidianDivideQuotient(b.getNumerator()));
}
inline Rational intMod(const Rational& a, const Rational& b)
{
  return Rational(a.getNumerator().euclidianDivideRemainder(b.getNumerator()));
}

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__NUMERAL_H */

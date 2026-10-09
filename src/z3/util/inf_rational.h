/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rational numbers extended with an infinitesimal: r + i*epsilon.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), file
 * src/util/inf_rational.h, and recast in cvc5 style. This is the inf_numeral
 * of theory_arith<mi_ext>, the arithmetic solver Z3 uses for these logics: a
 * strict bound x < k is the non-strict bound x <= k - epsilon.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__INF_RATIONAL_H
#define CVC5__Z3__UTIL__INF_RATIONAL_H

#include <ostream>
#include <string>

#include "z3/util/numeral.h"

namespace cvc5::internal {
namespace z3 {

class InfRational
{
 public:
  InfRational() = default;
  explicit InfRational(int n) : d_first(n), d_second(0) {}
  explicit InfRational(int n, int d) : d_first(n, d), d_second(0) {}
  /** r + epsilon if posInf, r - epsilon otherwise. */
  explicit InfRational(const Rational& r, bool posInf)
      : d_first(r), d_second(posInf ? 1 : -1)
  {
  }
  InfRational(const Rational& r) : d_first(r), d_second(0) {}
  InfRational(const Rational& r, const Rational& i) : d_first(r), d_second(i) {}

  size_t hash() const { return d_first.hash() ^ (d_second.hash() + 1); }

  std::string toString() const
  {
    if (d_second.isZero())
    {
      return d_first.toString();
    }
    std::string s = "(";
    s += d_first.toString();
    s += z3::isNeg(d_second) ? " -e*" : " +e*";
    s += d_second.abs().toString();
    s += ")";
    return s;
  }

  void reset()
  {
    d_first = Rational(0);
    d_second = Rational(0);
  }

  bool isInt() const { return d_first.isIntegral() && d_second.isZero(); }

  bool isRational() const { return d_second.isZero(); }

  const Rational& getRational() const { return d_first; }

  const Rational& getInfinitesimal() const { return d_second; }

  const Rational& getFirst() const { return d_first; }

  InfRational& operator=(const Rational& r)
  {
    d_first = r;
    d_second = Rational(0);
    return *this;
  }

  InfRational& operator+=(const InfRational& r)
  {
    d_first += r.d_first;
    d_second += r.d_second;
    return *this;
  }

  InfRational& operator-=(const InfRational& r)
  {
    d_first -= r.d_first;
    d_second -= r.d_second;
    return *this;
  }

  InfRational& operator+=(const Rational& r)
  {
    d_first += r;
    return *this;
  }

  InfRational& operator-=(const Rational& r)
  {
    d_first -= r;
    return *this;
  }

  InfRational& operator*=(const Rational& r)
  {
    d_first *= r;
    d_second *= r;
    return *this;
  }

  InfRational& operator/=(const Rational& r)
  {
    d_first /= r;
    d_second /= r;
    return *this;
  }

  InfRational& operator++()
  {
    d_first += Rational(1);
    return *this;
  }

  InfRational& operator--()
  {
    d_first -= Rational(1);
    return *this;
  }

  void neg()
  {
    d_first = -d_first;
    d_second = -d_second;
  }

  bool isZero() const { return d_first.isZero() && d_second.isZero(); }
  bool isOne() const { return d_first.isOne() && d_second.isZero(); }
  bool isMinusOne() const
  {
    return d_first.isNegativeOne() && d_second.isZero();
  }
  bool isNeg() const
  {
    return z3::isNeg(d_first) || (d_first.isZero() && z3::isNeg(d_second));
  }
  bool isPos() const
  {
    return z3::isPos(d_first) || (d_first.isZero() && z3::isPos(d_second));
  }
  bool isNonneg() const
  {
    return z3::isPos(d_first) || (d_first.isZero() && z3::isNonneg(d_second));
  }
  bool isNonpos() const
  {
    return z3::isNeg(d_first) || (d_first.isZero() && z3::isNonpos(d_second));
  }

  /** this += c * k */
  void addmul(const Rational& c, const InfRational& k)
  {
    d_first += c * k.d_first;
    d_second += c * k.d_second;
  }

  /** this -= c * k */
  void submul(const Rational& c, const InfRational& k)
  {
    d_first -= c * k.d_first;
    d_second -= c * k.d_second;
  }

  friend bool operator==(const InfRational& r1, const InfRational& r2)
  {
    return r1.d_first == r2.d_first && r1.d_second == r2.d_second;
  }
  friend bool operator==(const Rational& r1, const InfRational& r2)
  {
    return r1 == r2.d_first && r2.d_second.isZero();
  }
  friend bool operator==(const InfRational& r1, const Rational& r2)
  {
    return r1.d_first == r2 && r1.d_second.isZero();
  }
  friend bool operator<(const InfRational& r1, const InfRational& r2)
  {
    return r1.d_first < r2.d_first
           || (r1.d_first == r2.d_first && r1.d_second < r2.d_second);
  }
  friend bool operator<(const Rational& r1, const InfRational& r2)
  {
    return r1 < r2.d_first || (r1 == r2.d_first && z3::isPos(r2.d_second));
  }
  friend bool operator<(const InfRational& r1, const Rational& r2)
  {
    return r1.d_first < r2 || (r1.d_first == r2 && z3::isNeg(r1.d_second));
  }

  /** floor(inf_rational) */
  friend Rational floor(const InfRational& r)
  {
    if (r.d_first.isIntegral())
    {
      if (z3::isNonneg(r.d_second))
      {
        return r.d_first;
      }
      return r.d_first - Rational(1);
    }
    return z3::floor(r.d_first);
  }

  /** ceil(inf_rational) */
  friend Rational ceil(const InfRational& r)
  {
    if (r.d_first.isIntegral())
    {
      if (z3::isNonpos(r.d_second))
      {
        return r.d_first;
      }
      return r.d_first + Rational(1);
    }
    return z3::ceil(r.d_first);
  }

  friend InfRational operator*(const Rational& r1, const InfRational& r2)
  {
    InfRational result(r2);
    result.d_first *= r1;
    result.d_second *= r1;
    return result;
  }

 private:
  Rational d_first;
  Rational d_second;
};

inline bool operator!=(const InfRational& r1, const InfRational& r2)
{
  return !(r1 == r2);
}
inline bool operator!=(const Rational& r1, const InfRational& r2)
{
  return !(r1 == r2);
}
inline bool operator!=(const InfRational& r1, const Rational& r2)
{
  return !(r1 == r2);
}
inline bool operator>(const InfRational& r1, const InfRational& r2)
{
  return r2 < r1;
}
inline bool operator>(const InfRational& r1, const Rational& r2)
{
  return r2 < r1;
}
inline bool operator>(const Rational& r1, const InfRational& r2)
{
  return r2 < r1;
}
inline bool operator<=(const InfRational& r1, const InfRational& r2)
{
  return !(r2 < r1);
}
inline bool operator<=(const Rational& r1, const InfRational& r2)
{
  return !(r2 < r1);
}
inline bool operator<=(const InfRational& r1, const Rational& r2)
{
  return !(r2 < r1);
}
inline bool operator>=(const InfRational& r1, const InfRational& r2)
{
  return !(r1 < r2);
}
inline bool operator>=(const Rational& r1, const InfRational& r2)
{
  return !(r1 < r2);
}
inline bool operator>=(const InfRational& r1, const Rational& r2)
{
  return !(r1 < r2);
}
inline InfRational operator+(const InfRational& r1, const InfRational& r2)
{
  return InfRational(r1) += r2;
}
inline InfRational operator-(const InfRational& r1, const InfRational& r2)
{
  return InfRational(r1) -= r2;
}
inline InfRational operator-(const InfRational& r)
{
  InfRational result(r);
  result.neg();
  return result;
}
inline InfRational operator*(const InfRational& r1, const Rational& r2)
{
  return r2 * r1;
}
inline InfRational operator/(const InfRational& r1, const Rational& r2)
{
  InfRational result(r1);
  result /= r2;
  return result;
}
inline std::ostream& operator<<(std::ostream& out, const InfRational& r)
{
  return out << r.toString();
}
inline InfRational abs(const InfRational& r)
{
  InfRational result(r);
  if (result.isNeg())
  {
    result.neg();
  }
  return result;
}

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__INF_RATIONAL_H */

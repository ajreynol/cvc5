/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Boolean variables and literals of the ported Z3 SMT core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * files src/util/sat_literal.h and src/smt/smt_literal.h, recast in cvc5
 * style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__LITERAL_H
#define CVC5__Z3__UTIL__LITERAL_H

#include <climits>
#include <cstdint>
#include <ostream>
#include <vector>

#include "base/check.h"
#include "z3/util/approx_set.h"

namespace cvc5::internal {
namespace z3 {

/** A Boolean variable is just an index. */
using BoolVar = uint32_t;

using BoolVarVector = std::vector<BoolVar>;

/** The absence of a Boolean variable. */
inline constexpr BoolVar s_nullBoolVar = UINT32_MAX >> 1;

/** The variable reserved for the constant true. */
inline constexpr BoolVar s_trueBoolVar = 0;

/** The first variable available for input formulas. */
inline constexpr BoolVar s_firstBoolVar = 1;

/**
 * A literal. The positive literal of variable b is represented by 2*b and the
 * negative one by 2*b+1, so that negation is a single xor and the index can be
 * used directly to key watch lists.
 */
class Literal
{
  uint32_t d_val;

 public:
  constexpr Literal() : d_val(s_nullBoolVar << 1) {}

  explicit Literal(BoolVar v, bool sign = false)
      : d_val((v << 1) + static_cast<uint32_t>(sign))
  {
    Assert(var() == v);
    Assert(this->sign() == sign);
  }

  constexpr BoolVar var() const { return d_val >> 1; }

  constexpr bool sign() const { return (d_val & 1u) != 0; }

  /** The positive literal of the same variable. */
  Literal unsign() const
  {
    Literal l;
    l.d_val = d_val & ~1u;
    return l;
  }

  /** The dense index of this literal, in [0, 2*numVars). */
  uint32_t index() const { return d_val; }

  void neg() { d_val = d_val ^ 1; }

  friend Literal operator~(Literal l)
  {
    l.d_val = l.d_val ^ 1;
    return l;
  }

  uint32_t toUint() const { return d_val; }

  uint32_t hash() const { return toUint(); }

  friend Literal toLiteral(uint32_t x);
  friend bool operator<(const Literal& l1, const Literal& l2);
  friend bool operator==(const Literal& l1, const Literal& l2);
  friend bool operator!=(const Literal& l1, const Literal& l2);
};

inline constexpr Literal s_nullLiteral;
static_assert(s_nullLiteral.var() == s_nullBoolVar);
static_assert(!s_nullLiteral.sign());

/** The literal that is always true. */
inline const Literal s_trueLiteral(s_trueBoolVar, false);

/** The literal that is always false. */
inline const Literal s_falseLiteral(s_trueBoolVar, true);

inline Literal toLiteral(uint32_t x)
{
  Literal l;
  l.d_val = x;
  return l;
}

inline bool operator<(const Literal& l1, const Literal& l2)
{
  return l1.d_val < l2.d_val;
}

inline bool operator==(const Literal& l1, const Literal& l2)
{
  return l1.d_val == l2.d_val;
}

inline bool operator!=(const Literal& l1, const Literal& l2)
{
  return l1.d_val != l2.d_val;
}

std::ostream& operator<<(std::ostream& out, Literal l);

using LiteralVector = std::vector<Literal>;

/** Maps a literal to its dense index, for approximated literal sets. */
struct LiteralToUnsigned
{
  uint32_t operator()(Literal l) const { return l.toUint(); }
};

using LiteralApproxSet = ApproxSetTpl<Literal, LiteralToUnsigned, uint32_t>;

using VarApproxSet = ApproxSetTpl<BoolVar, UnsignedToUnsigned, uint32_t>;

/** Negate every literal of lits into result. */
template <typename T>
void negLiterals(size_t numLits, const Literal* lits, T& result)
{
  for (size_t i = 0; i < numLits; ++i)
  {
    result.push_back(~lits[i]);
  }
}

/** Hash functor for Literal, for use with std:: containers. */
struct LiteralHashFunction
{
  size_t operator()(Literal l) const { return l.hash(); }
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__LITERAL_H */

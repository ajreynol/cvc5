/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Approximated sets: fixed-width bit masks that over-approximate a set of
 * elements, used as a cheap filter before an exact test.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/util/approx_set.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__APPROX_SET_H
#define CVC5__Z3__UTIL__APPROX_SET_H

#include <cstdint>
#include <ostream>

namespace cvc5::internal {
namespace z3 {

template <typename R>
class ApproxSetTraits;

template <>
class ApproxSetTraits<uint64_t>
{
 public:
  static constexpr uint32_t s_capacity = 64;
  static constexpr uint64_t s_zero = UINT64_C(0);
  static constexpr uint64_t s_one = UINT64_C(1);
};

template <>
class ApproxSetTraits<uint32_t>
{
 public:
  static constexpr uint32_t s_capacity = 32;
  static constexpr uint32_t s_zero = 0;
  static constexpr uint32_t s_one = 1;
};

/**
 * A set of elements of type T, approximated by an R-bit mask. Each element is
 * mapped to an unsigned by ToUnsigned and then to the bit at that index modulo
 * the width of R.
 *
 * Membership is one-sided: mayContain() can return a false positive, but
 * mustNotContain() is exact. The same holds for the subset and equality tests,
 * which is where the cheap filtering comes from.
 */
template <typename T, typename ToUnsigned, typename R = uint64_t>
class ApproxSetTpl : private ToUnsigned
{
 protected:
  R d_set = ApproxSetTraits<R>::s_zero;

  uint32_t elemToUnsigned(const T& e) const
  {
    return ToUnsigned::operator()(e);
  }

  R unsignedToSet(uint32_t u) const
  {
    return ApproxSetTraits<R>::s_one
           << (u & (ApproxSetTraits<R>::s_capacity - 1));
  }

  R elemToSet(const T& e) const { return unsignedToSet(elemToUnsigned(e)); }

  static ApproxSetTpl rawToSet(const R& s)
  {
    ApproxSetTpl r;
    r.d_set = s;
    return r;
  }

 public:
  ApproxSetTpl() = default;

  explicit ApproxSetTpl(const T& e) : d_set(elemToSet(e)) {}

  ApproxSetTpl(size_t sz, const T* es)
  {
    for (size_t i = 0; i < sz; ++i)
    {
      insert(es[i]);
    }
  }

  void set(R s) { d_set = s; }

  R get() const { return d_set; }

  void insert(const T& e) { d_set |= elemToSet(e); }

  bool mayContain(const T& e) const
  {
    return (d_set & elemToSet(e)) != ApproxSetTraits<R>::s_zero;
  }

  bool mustNotContain(const T& e) const { return !mayContain(e); }

  friend ApproxSetTpl mkUnion(const ApproxSetTpl& s1, const ApproxSetTpl& s2)
  {
    return rawToSet(s1.d_set | s2.d_set);
  }

  friend ApproxSetTpl mkIntersection(const ApproxSetTpl& s1,
                                     const ApproxSetTpl& s2)
  {
    return rawToSet(s1.d_set & s2.d_set);
  }

  void operator|=(const ApproxSetTpl& other) { d_set |= other.d_set; }

  void operator&=(const ApproxSetTpl& other) { d_set &= other.d_set; }

  void operator-=(const ApproxSetTpl& other) { d_set &= ~(other.d_set); }

  bool empty() const { return d_set == ApproxSetTraits<R>::s_zero; }

  /** Return true if this is definitely not a subset of s2. */
  bool mustNotSubset(const ApproxSetTpl& s2) const
  {
    return (d_set & ~(s2.d_set)) != ApproxSetTraits<R>::s_zero;
  }

  /** Return true if this definitely does not subsume s2. */
  bool mustNotSubsume(const ApproxSetTpl& s2) const
  {
    return mustNotSubset(s2);
  }

  /** Return true if the two approximations are definitely different. */
  friend bool mustNotEq(const ApproxSetTpl& s1, const ApproxSetTpl& s2)
  {
    return s1.d_set != s2.d_set;
  }

  /** Return true if the two approximations may denote equal sets. */
  friend bool mayEq(const ApproxSetTpl& s1, const ApproxSetTpl& s2)
  {
    return s1.d_set == s2.d_set;
  }

  /** Return true if s1 and s2 are the same approximated set. */
  bool equiv(const ApproxSetTpl& s2) const { return d_set == s2.d_set; }

  /** Return true if the approximation of s1 is a subset of that of s2. */
  friend bool approxSubset(const ApproxSetTpl& s1, const ApproxSetTpl& s2)
  {
    return s2.equiv(mkUnion(s1, s2));
  }

  void reset() { d_set = ApproxSetTraits<R>::s_zero; }

  bool emptyIntersection(const ApproxSetTpl& other) const
  {
    return mkIntersection(*this, other).empty();
  }
};

/** Identity map from unsigned to unsigned, for approximated sets of indices. */
struct UnsignedToUnsigned
{
  uint32_t operator()(uint32_t u) const { return u; }
};

using UApproxSet = ApproxSetTpl<uint32_t, UnsignedToUnsigned>;

/** The number of distinct bits available in an ApproxSet. */
constexpr uint32_t approxSetCapacity()
{
  return ApproxSetTraits<uint64_t>::s_capacity;
}

/**
 * The 64-bit approximated set of unsigned indices, extended with an iterator
 * over the bits that are set. This is the variant used for enode label sets.
 */
class ApproxSet : public UApproxSet
{
 public:
  ApproxSet() = default;
  ApproxSet(uint32_t e) : UApproxSet(e) {}

  class iterator
  {
    uint64_t d_set;
    uint32_t d_val;

    void moveToNext()
    {
      if (d_set > 0)
      {
        // after the shift the least significant bit is set
        uint32_t tz = static_cast<uint32_t>(__builtin_ctzll(d_set));
        d_val += tz;
        d_set >>= tz;
      }
    }

   public:
    iterator(uint64_t s) : d_set(s), d_val(0) { moveToNext(); }

    uint32_t operator*() const { return d_val; }

    iterator& operator++()
    {
      d_val++;
      d_set >>= 1;
      moveToNext();
      return *this;
    }

    iterator operator++(int)
    {
      iterator tmp = *this;
      ++*this;
      return tmp;
    }

    bool operator!=(const iterator& it) const { return d_set != it.d_set; }
  };

  iterator begin() const { return iterator(d_set); }

  static iterator end() { return iterator(0); }

  /** The number of bits set. */
  uint32_t size() const { return static_cast<uint32_t>(__builtin_popcountll(d_set)); }

  void print(std::ostream& out) const;

  friend bool operator==(const ApproxSet& s1, const ApproxSet& s2)
  {
    return mayEq(s1, s2);
  }
};

std::ostream& operator<<(std::ostream& out, const ApproxSet& s);

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__APPROX_SET_H */

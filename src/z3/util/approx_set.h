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

namespace cvc5::internal {
namespace z3 {

/** The number of distinct bits available in an ApproxSet. */
constexpr uint32_t approxSetCapacity() { return 64; }

/**
 * A set of unsigned indices, approximated by a 64-bit mask: each index is
 * mapped to the bit at that index modulo 64.
 *
 * Membership is one-sided: mayContain() can return a false positive, but
 * a negative answer is exact. The same holds for the intersection test, which
 * is where the cheap filtering comes from. This is the variant used for enode
 * label sets, with an iterator over the bits that are set.
 */
class ApproxSet
{
 public:
  ApproxSet() = default;
  ApproxSet(uint32_t e) : d_set(toSet(e)) {}

  void insert(uint32_t e) { d_set |= toSet(e); }

  bool mayContain(uint32_t e) const { return (d_set & toSet(e)) != 0; }

  void operator|=(const ApproxSet& other) { d_set |= other.d_set; }

  bool empty() const { return d_set == 0; }

  bool emptyIntersection(const ApproxSet& other) const
  {
    return (d_set & other.d_set) == 0;
  }

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

    bool operator!=(const iterator& it) const { return d_set != it.d_set; }
  };

  iterator begin() const { return iterator(d_set); }

  static iterator end() { return iterator(0); }

  /** The number of bits set. */
  uint32_t size() const
  {
    return static_cast<uint32_t>(__builtin_popcountll(d_set));
  }

 private:
  static uint64_t toSet(uint32_t u)
  {
    return UINT64_C(1) << (u & (approxSetCapacity() - 1));
  }

  uint64_t d_set = 0;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__APPROX_SET_H */

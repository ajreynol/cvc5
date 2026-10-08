/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A set of unsigned integers, represented as a growable bit vector.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/util/uint_set.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__UINT_SET_H
#define CVC5__Z3__UTIL__UINT_SET_H

#include <algorithm>
#include <cstdint>
#include <vector>

namespace cvc5::internal {
namespace z3 {

/**
 * A set of small unsigned integers backed by a bit vector. Membership tests
 * are a shift and a mask, which is what makes the relevancy and label
 * bookkeeping cheap enough to sit in the search's inner loops.
 */
class UIntSet
{
  static constexpr size_t s_bitsPerWord = 64;

 public:
  void insert(size_t v)
  {
    size_t w = v / s_bitsPerWord;
    if (w >= d_words.size())
    {
      d_words.resize(w + 1, 0);
    }
    d_words[w] |= (UINT64_C(1) << (v % s_bitsPerWord));
  }

  void remove(size_t v)
  {
    size_t w = v / s_bitsPerWord;
    if (w < d_words.size())
    {
      d_words[w] &= ~(UINT64_C(1) << (v % s_bitsPerWord));
    }
  }

  bool contains(size_t v) const
  {
    size_t w = v / s_bitsPerWord;
    return w < d_words.size()
           && (d_words[w] & (UINT64_C(1) << (v % s_bitsPerWord))) != 0;
  }

  void reset() { std::fill(d_words.begin(), d_words.end(), UINT64_C(0)); }

  void resetAndReleaseMemory()
  {
    d_words.clear();
    d_words.shrink_to_fit();
  }

  bool empty() const
  {
    for (uint64_t w : d_words)
    {
      if (w != 0)
      {
        return false;
      }
    }
    return true;
  }

  size_t size() const
  {
    size_t r = 0;
    for (uint64_t w : d_words)
    {
      r += static_cast<size_t>(__builtin_popcountll(w));
    }
    return r;
  }

  UIntSet& operator|=(const UIntSet& other)
  {
    if (d_words.size() < other.d_words.size())
    {
      d_words.resize(other.d_words.size(), 0);
    }
    for (size_t i = 0, n = other.d_words.size(); i < n; ++i)
    {
      d_words[i] |= other.d_words[i];
    }
    return *this;
  }

  /** Note the trailing all-zero words are not significant. */
  bool operator==(const UIntSet& other) const
  {
    size_t n = std::max(d_words.size(), other.d_words.size());
    for (size_t i = 0; i < n; ++i)
    {
      if (word(i) != other.word(i))
      {
        return false;
      }
    }
    return true;
  }

  bool operator!=(const UIntSet& other) const { return !(*this == other); }

  bool subsetOf(const UIntSet& other) const
  {
    for (size_t i = 0, n = d_words.size(); i < n; ++i)
    {
      if ((d_words[i] & ~other.word(i)) != 0)
      {
        return false;
      }
    }
    return true;
  }

 private:
  uint64_t word(size_t i) const { return i < d_words.size() ? d_words[i] : 0; }

  std::vector<uint64_t> d_words;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__UINT_SET_H */

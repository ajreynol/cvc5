/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Small helpers that stand in for the sparse-vector operations the Z3 core is
 * written against.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__UTIL_H
#define CVC5__Z3__UTIL__UTIL_H

#include <cstddef>
#include <vector>

namespace cvc5::internal {
namespace z3 {

/**
 * Store val at index i, growing v with def as needed. This is Z3's
 * vector::setx.
 */
template <typename T>
void setx(std::vector<T>& v, size_t i, const T& val, const T& def)
{
  if (i >= v.size())
  {
    v.resize(i + 1, def);
  }
  v[i] = val;
}

/** Read index i, or def if i is out of range. This is Z3's vector::get. */
template <typename T>
const T& getx(const std::vector<T>& v, size_t i, const T& def)
{
  return i < v.size() ? v[i] : def;
}

/** Grow v to at least size sz, filling with def. */
template <typename T>
void reservex(std::vector<T>& v, size_t sz, const T& def)
{
  if (v.size() < sz)
  {
    v.resize(sz, def);
  }
}

/**
 * Advance the iterator it over the product of n ranges, where sz[i] is the
 * size of the i-th range. Returns false once the product is exhausted.
 */
inline bool productIteratorNext(size_t n, const size_t* sz, size_t* it)
{
  for (size_t i = 0; i < n; ++i)
  {
    it[i]++;
    if (it[i] < sz[i])
    {
      return true;
    }
    it[i] = 0;
  }
  return false;
}

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__UTIL_H */

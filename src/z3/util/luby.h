/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The Luby sequence, used by one of the restart strategies.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/util/luby.cpp, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__LUBY_H
#define CVC5__Z3__UTIL__LUBY_H

#include <cmath>
#include <cstdint>

namespace cvc5::internal {
namespace z3 {

inline uint32_t getLuby(uint32_t i)
{
  if (i == 1)
  {
    return 1;
  }
  double k = std::log(static_cast<double>(i + 1)) / std::log(2.0);

  if (k == std::floor(k + 0.5))
  {
    return static_cast<uint32_t>(std::pow(2, k - 1));
  }
  k = static_cast<uint32_t>(std::floor(k));
  return getLuby(i - static_cast<uint32_t>(std::pow(2, k)) + 1);
}

/**
 * The element x, counting from 0, of the Luby sequence with base y. With
 * y = 2 this is getLuby(x + 1).
 *
 * Not ported from Z3: this is luby(y, x) of MiniSat (MIT License), as in
 * src/prop/minisat/core/Solver.cc.
 */
inline double getLuby(double y, uint32_t x)
{
  // find the finite subsequence that contains index x, and its size
  uint32_t size = 1;
  uint32_t seq = 0;
  while (size < x + 1)
  {
    seq++;
    size = 2 * size + 1;
  }
  while (size - 1 != x)
  {
    size = (size - 1) >> 1;
    seq--;
    x = x % size;
  }
  return std::pow(y, seq);
}

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__LUBY_H */

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The random number generator of the ported Z3 core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/util/util.h, and recast in cvc5 style.
 *
 * This is kept bit-for-bit identical to Z3's, since random decisions and
 * random restarts are part of the search behavior being replicated.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__RANDOM_GEN_H
#define CVC5__Z3__UTIL__RANDOM_GEN_H

#include <cstdint>

#include "base/check.h"

namespace cvc5::internal {
namespace z3 {

class RandomGen
{
 public:
  RandomGen(uint32_t seed = 0) : d_data(seed) {}

  void setSeed(uint32_t s) { d_data = s; }

  uint32_t getSeed() const { return d_data; }

  int operator()()
  {
    return ((d_data = d_data * 214013L + 2531011L) >> 16) & 0x7fff;
  }

  uint32_t operator()(uint32_t u)
  {
    if (u == 0)
    {
      return 0;
    }
    uint32_t r = static_cast<uint32_t>((*this)());
    return r % u;
  }

  static int maxValue() { return 0x7fff; }

 private:
  uint32_t d_data;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__RANDOM_GEN_H */

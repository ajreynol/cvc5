/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The integer hash functions of the ported Z3 core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/util/hash.h, and recast in cvc5 style.
 *
 * These are kept bit-for-bit identical to Z3's, because they decide the
 * bucket layout of the congruence table and the label hashes that filter
 * E-matching, and so are part of what is being replicated.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__HASH_H
#define CVC5__Z3__UTIL__HASH_H

#include <cstdint>

namespace cvc5::internal {
namespace z3 {

/** Bob Jenkins' 96-bit mixing step. */
inline void hashMix(uint32_t& a, uint32_t& b, uint32_t& c)
{
  a -= b;
  a -= c;
  a ^= (c >> 13);
  b -= c;
  b -= a;
  b ^= (a << 8);
  c -= a;
  c -= b;
  c ^= (b >> 13);
  a -= b;
  a -= c;
  a ^= (c >> 12);
  b -= c;
  b -= a;
  b ^= (a << 16);
  c -= a;
  c -= b;
  c ^= (b >> 5);
  a -= b;
  a -= c;
  a ^= (c >> 3);
  b -= c;
  b -= a;
  b ^= (a << 10);
  c -= a;
  c -= b;
  c ^= (b >> 15);
}

/** Thomas Wang's 32-bit integer hash. */
inline uint32_t hashU(uint32_t a)
{
  a = (a + 0x7ed55d16) + (a << 12);
  a = (a ^ 0xc761c23c) ^ (a >> 19);
  a = (a + 0x165667b1) + (a << 5);
  a = (a + 0xd3a2646c) ^ (a << 9);
  a = (a + 0xfd7046c5) + (a << 3);
  a = (a ^ 0xb55a4f09) ^ (a >> 16);
  return a;
}

inline uint32_t combineHash(uint32_t h1, uint32_t h2)
{
  h1 ^= h2 + 0x9e3779b9 + (h1 << 6) + (h1 >> 2);
  return hashU(h1);
}

inline uint32_t hashUU(uint32_t a, uint32_t b)
{
  return combineHash(hashU(a), hashU(b));
}

/**
 * Bob Jenkins' hash over a composite object with n children, where khasher
 * hashes the "kind" of the object and chasher hashes its i-th child. Kept
 * identical to Z3's get_composite_hash, since it decides fingerprint
 * bucketing.
 */
template <typename Composite,
          typename GetKindHashProc,
          typename GetChildHashProc>
uint32_t getCompositeHash(Composite app,
                          size_t n,
                          const GetKindHashProc& khasher,
                          const GetChildHashProc& chasher)
{
  uint32_t a, b, c;
  uint32_t kindHash = khasher(app);

  a = b = 0x9e3779b9;
  c = 11;

  switch (n)
  {
    case 0: return c;
    case 1:
      a += kindHash;
      b = chasher(app, 0);
      hashMix(a, b, c);
      return c;
    case 2:
      a += kindHash;
      b += chasher(app, 0);
      c += chasher(app, 1);
      hashMix(a, b, c);
      return c;
    case 3:
      a += chasher(app, 0);
      b += chasher(app, 1);
      c += chasher(app, 2);
      hashMix(a, b, c);
      a += kindHash;
      hashMix(a, b, c);
      return c;
    default:
      while (n >= 3)
      {
        n--;
        a += chasher(app, n);
        n--;
        b += chasher(app, n);
        n--;
        c += chasher(app, n);
        hashMix(a, b, c);
      }

      a += kindHash;
      switch (n)
      {
        case 2: b += chasher(app, 1); CVC5_FALLTHROUGH;
        case 1: c += chasher(app, 0);
      }
      hashMix(a, b, c);
      return c;
  }
}

inline uint32_t hashUll(uint64_t a)
{
  a = (~a) + (a << 18);
  a ^= (a >> 31);
  a = a * 21;
  a ^= (a >> 11);
  a = a + (a << 6);
  a ^= (a >> 22);
  return static_cast<uint32_t>(a);
}

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__HASH_H */

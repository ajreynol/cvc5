/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A set of natural numbers with a constant-time reset.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/util/nat_set.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__NAT_SET_H
#define CVC5__Z3__UTIL__NAT_SET_H

#include <climits>
#include <cstdint>
#include <vector>

namespace cvc5::internal {
namespace z3 {

/**
 * A subset of [0, domain). Membership is recorded by stamping the current
 * timestamp, so reset() is a single increment rather than a sweep.
 */
class NatSet
{
 public:
  NatSet(size_t s = 0) : d_currTimestamp(0)
  {
    if (s > 0)
    {
      d_timestamps.resize(s, 0);
    }
  }

  /** Set the domain to [0, s). */
  void setDomain(size_t s) { d_timestamps.resize(s, 0); }

  size_t getDomain() const { return d_timestamps.size(); }

  /** Grow the domain so that v is in it. */
  void assureDomain(size_t v)
  {
    if (v >= getDomain())
    {
      setDomain(v + 1);
    }
  }

  bool contains(size_t v) const { return d_timestamps[v] > d_currTimestamp; }

  void insert(size_t v) { d_timestamps[v] = d_currTimestamp + 1; }

  void remove(size_t v) { d_timestamps[v] = d_currTimestamp; }

  void reset()
  {
    d_currTimestamp++;
    if (d_currTimestamp == UINT32_MAX)
    {
      std::fill(d_timestamps.begin(), d_timestamps.end(), 0);
      d_currTimestamp = 0;
    }
  }

  bool empty() const
  {
    for (uint32_t t : d_timestamps)
    {
      if (t > d_currTimestamp)
      {
        return false;
      }
    }
    return true;
  }

 private:
  uint32_t d_currTimestamp;
  std::vector<uint32_t> d_timestamps;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__NAT_SET_H */

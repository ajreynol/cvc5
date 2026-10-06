/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Approximate sets of label hashes, used to filter E-matching candidates.
 */

#include "theory/quantifiers/eager/approx_set.h"

#include <ostream>

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

size_t ApproxSet::size() const
{
  size_t n = 0;
  for (uint64_t s = d_set; s != 0; s >>= 1)
  {
    n += (s & 1);
  }
  return n;
}

void ApproxSet::const_iterator::moveToNext()
{
  while (d_set != 0 && (d_set & 1) == 0)
  {
    d_val++;
    d_set >>= 1;
  }
}

std::ostream& operator<<(std::ostream& out, const ApproxSet& s)
{
  out << "{";
  bool first = true;
  for (size_t e : s)
  {
    out << (first ? "" : ",") << e;
    first = false;
  }
  return out << "}";
}

size_t LabelHasher::operator()(TNode op)
{
  Node opn = op;
  std::unordered_map<Node, size_t>::iterator it = d_hash.find(opn);
  if (it != d_hash.end())
  {
    return it->second;
  }
  // z3 mixes the small id of the declaration (mam.cpp, label_hasher::
  // mk_lbl_hash) and then takes it modulo the capacity of the approximate
  // set. We do the same with the node id of the operator.
  uint32_t a = 17;
  uint32_t b = 3;
  uint32_t c = static_cast<uint32_t>(opn.getId());
  // the mix function of z3's util/hash.h
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
  size_t h = c & (ApproxSet::capacity - 1);
  d_hash[opn] = h;
  return h;
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

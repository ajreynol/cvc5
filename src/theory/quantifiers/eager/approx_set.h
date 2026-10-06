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
 *
 * This is a port of z3's util/approx_set.h (class approx_set) and of the
 * label_hasher in z3's smt/mam.cpp. See
 * theory/quantifiers/eager/README.md section 2.3.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__APPROX_SET_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__APPROX_SET_H

#include <cstdint>
#include <iosfwd>
#include <unordered_map>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

/**
 * A set of label hashes, approximated by a 64 bit word. Elements are taken
 * modulo the capacity, so membership is may-membership: mayContain(e) false
 * means e is definitely not in the set.
 *
 * Mirrors z3's approx_set, including the fact that z3's capacity
 * (APPROX_SET_CAPACITY) is 64.
 */
class ApproxSet
{
 public:
  /** The number of distinct elements this set can distinguish */
  static constexpr size_t capacity = 64;

  ApproxSet() : d_set(0) {}
  explicit ApproxSet(size_t e) : d_set(toBit(e)) {}

  /** Is the set (definitely) empty? */
  bool empty() const { return d_set == 0; }
  /** May the set contain e? */
  bool mayContain(size_t e) const { return (d_set & toBit(e)) != 0; }
  /** Add e */
  void insert(size_t e) { d_set |= toBit(e); }
  /** Union */
  ApproxSet& operator|=(const ApproxSet& s)
  {
    d_set |= s.d_set;
    return *this;
  }
  bool operator==(const ApproxSet& s) const { return d_set == s.d_set; }
  bool operator!=(const ApproxSet& s) const { return d_set != s.d_set; }
  /** Is the intersection with s (definitely) empty? */
  bool emptyIntersection(const ApproxSet& s) const
  {
    return (d_set & s.d_set) == 0;
  }
  /** May this be a subset of s? (z3: approx_subset) */
  bool maySubset(const ApproxSet& s) const { return (d_set & ~s.d_set) == 0; }
  /** The number of elements, i.e. the number of bits set */
  size_t size() const;
  /** The raw bits */
  uint64_t bits() const { return d_set; }
  /** The set whose raw bits are b */
  static ApproxSet fromBits(uint64_t b)
  {
    ApproxSet s;
    s.d_set = b;
    return s;
  }

  /** Iteration over the elements of the set, in increasing order */
  class const_iterator
  {
   public:
    const_iterator(uint64_t s) : d_set(s), d_val(0) { moveToNext(); }
    size_t operator*() const { return d_val; }
    const_iterator& operator++()
    {
      d_val++;
      d_set >>= 1;
      moveToNext();
      return *this;
    }
    bool operator==(const const_iterator& it) const
    {
      return d_set == it.d_set && (d_set == 0 || d_val == it.d_val);
    }
    bool operator!=(const const_iterator& it) const { return !(*this == it); }

   private:
    void moveToNext();
    uint64_t d_set;
    size_t d_val;
  };
  const_iterator begin() const { return const_iterator(d_set); }
  const_iterator end() const { return const_iterator(0); }

 private:
  static uint64_t toBit(size_t e)
  {
    return UINT64_C(1) << (e & (capacity - 1));
  }
  uint64_t d_set;
};

std::ostream& operator<<(std::ostream& out, const ApproxSet& s);

/**
 * Maps an operator to its label hash, i.e. to an element of an ApproxSet.
 *
 * Mirrors z3's label_hasher (smt/mam.cpp). z3 hashes the small id of a
 * func_decl with its mix function; we hash the operator Node with the same
 * mixing applied to the node id, so that two distinct operators get the same
 * hash only as often as in z3.
 */
class LabelHasher
{
 public:
  /** Get the label hash of operator op */
  size_t operator()(TNode op);

 private:
  /** Cache from operator to hash */
  std::unordered_map<Node, size_t> d_hash;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif

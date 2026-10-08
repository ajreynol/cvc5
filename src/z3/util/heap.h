/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An indexed binary heap over small non-negative integers.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/util/heap.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__HEAP_H
#define CVC5__Z3__UTIL__HEAP_H

#include <cstring>
#include <ostream>
#include <vector>

#include "base/check.h"

namespace cvc5::internal {
namespace z3 {

/**
 * A binary min-heap of integer values in [0, bound), which additionally keeps
 * the index of each value so that a value can be removed, or notified that its
 * key changed, in logarithmic time. This is what makes the activity-based
 * case-split queues able to react to activity updates.
 *
 * Slot zero of the value array holds a sentinel, so that index arithmetic can
 * use the usual one-based formulas and index zero can mean "absent".
 */
template <typename LT>
class Heap : private LT
{
 public:
  Heap(int s, const LT& lt = LT()) : LT(lt)
  {
    d_values.push_back(-1);
    setBounds(s);
  }

  bool lessThan(int v1, int v2) const { return LT::operator()(v1, v2); }

  bool empty() const { return d_values.size() == 1; }

  bool contains(int val) const
  {
    return val < static_cast<int>(d_value2Indices.size())
           && d_value2Indices[val] != 0;
  }

  void reset()
  {
    if (empty())
    {
      return;
    }
    std::memset(
        d_value2Indices.data(), 0, sizeof(int) * d_value2Indices.size());
    d_values.clear();
    d_values.push_back(-1);
  }

  void clear() { reset(); }

  void setBounds(int s) { d_value2Indices.resize(s, 0); }

  size_t getBounds() const { return d_value2Indices.size(); }

  size_t size() const { return d_values.size() - 1; }

  void reserve(int s)
  {
    if (s > static_cast<int>(d_value2Indices.size()))
    {
      setBounds(s);
    }
  }

  int minValue() const
  {
    Assert(!empty());
    return d_values[1];
  }

  int eraseMin()
  {
    Assert(!empty());
    Assert(d_values.size() >= 2);
    int result = d_values[1];
    if (d_values.size() == 2)
    {
      d_value2Indices[result] = 0;
      d_values.pop_back();
      Assert(empty());
    }
    else
    {
      int lastVal = d_values.back();
      d_values[1] = lastVal;
      d_value2Indices[lastVal] = 1;
      d_value2Indices[result] = 0;
      d_values.pop_back();
      moveDown(1);
    }
    return result;
  }

  void erase(int val)
  {
    Assert(contains(val));
    int idx = d_value2Indices[val];
    if (idx == static_cast<int>(d_values.size()) - 1)
    {
      d_value2Indices[val] = 0;
      d_values.pop_back();
    }
    else
    {
      int lastVal = d_values.back();
      d_values[idx] = lastVal;
      d_value2Indices[lastVal] = idx;
      d_value2Indices[val] = 0;
      d_values.pop_back();
      int parentIdx = parent(idx);
      if (parentIdx != 0 && lessThan(lastVal, d_values[parentIdx]))
      {
        moveUp(idx);
      }
      else
      {
        moveDown(idx);
      }
    }
  }

  /** Notify the heap that the key of val decreased. */
  void decreased(int val)
  {
    Assert(contains(val));
    moveUp(d_value2Indices[val]);
  }

  /** Notify the heap that the key of val increased. */
  void increased(int val)
  {
    Assert(contains(val));
    moveDown(d_value2Indices[val]);
  }

  void insert(int val)
  {
    Assert(!contains(val));
    Assert(val >= 0 && val < static_cast<int>(d_value2Indices.size()));
    int idx = static_cast<int>(d_values.size());
    d_value2Indices[val] = idx;
    d_values.push_back(val);
    moveUp(idx);
  }

  using iterator = int*;
  using const_iterator = const int*;

  iterator begin() { return d_values.data() + 1; }

  iterator end() { return d_values.data() + d_values.size(); }

  const_iterator begin() const { return d_values.data() + 1; }

  const_iterator end() const { return d_values.data() + d_values.size(); }

  void swap(Heap& other) noexcept
  {
    if (this != &other)
    {
      d_values.swap(other.d_values);
      d_value2Indices.swap(other.d_value2Indices);
    }
  }

  bool checkInvariant() const { return checkInvariantCore(1); }

 private:
  static int left(int i) { return i << 1; }

  static int right(int i) { return (i << 1) + 1; }

  static int parent(int i) { return i >> 1; }

  bool checkInvariantCore(int idx) const
  {
    if (d_values.empty() || d_values[0] != -1)
    {
      return false;
    }
    if (idx < static_cast<int>(d_values.size()))
    {
      Assert(d_value2Indices[d_values[idx]] == idx);
      Assert(parent(idx) == 0
             || !lessThan(d_values[idx], d_values[parent(idx)]));
      Assert(checkInvariantCore(left(idx)));
      Assert(checkInvariantCore(right(idx)));
    }
    return true;
  }

  void moveUp(int idx)
  {
    int val = d_values[idx];
    while (true)
    {
      int parentIdx = parent(idx);
      if (parentIdx == 0 || !lessThan(val, d_values[parentIdx]))
      {
        break;
      }
      d_values[idx] = d_values[parentIdx];
      d_value2Indices[d_values[idx]] = idx;
      idx = parentIdx;
    }
    d_values[idx] = val;
    d_value2Indices[val] = idx;
  }

  void moveDown(int idx)
  {
    int val = d_values[idx];
    int sz = static_cast<int>(d_values.size());
    while (true)
    {
      int leftIdx = left(idx);
      if (leftIdx >= sz)
      {
        break;
      }
      int rightIdx = right(idx);
      int minIdx = rightIdx < sz
                           && lessThan(d_values[rightIdx], d_values[leftIdx])
                       ? rightIdx
                       : leftIdx;
      int minValue = d_values[minIdx];
      if (!lessThan(minValue, val))
      {
        break;
      }
      d_values[idx] = minValue;
      d_value2Indices[minValue] = idx;
      idx = minIdx;
    }
    d_values[idx] = val;
    d_value2Indices[val] = idx;
  }

  std::vector<int> d_values;
  std::vector<int> d_value2Indices;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__HEAP_H */

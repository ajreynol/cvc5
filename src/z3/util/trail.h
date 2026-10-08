/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Backtracking trail objects and the trail stack of the ported Z3 SMT core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/util/trail.h, and recast in cvc5 style.
 *
 * Note this is deliberately *not* cvc5's context::Context. The Z3 core
 * manages its own scopes (one per decision level, plus base-level scopes for
 * user push/pop) and the ported code is written against this interface.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__TRAIL_H
#define CVC5__Z3__UTIL__TRAIL_H

#include <cstdint>
#include <vector>

#include "base/check.h"
#include "z3/util/region.h"

namespace cvc5::internal {
namespace z3 {

/** An action to be undone when the enclosing scope is popped. */
class Trail
{
 public:
  virtual ~Trail() = default;
  virtual void undo() = 0;
};

/** Restore a variable to the value it had when the trail object was created. */
template <typename T>
class ValueTrail : public Trail
{
 public:
  ValueTrail(T& value) : d_value(value), d_oldValue(value) {}

  ValueTrail(T& value, const T& newValue) : d_value(value), d_oldValue(value)
  {
    d_value = newValue;
  }

  void undo() override { d_value = d_oldValue; }

 private:
  T& d_value;
  T d_oldValue;
};

/** Restore a variable from a separate history stack. */
template <typename T, typename Ts>
class ScopedValueTrail : public Trail
{
 public:
  ScopedValueTrail(T& value, Ts& values) : d_value(value), d_values(values) {}

  void undo() override
  {
    d_value = d_values.back();
    d_values.pop_back();
  }

 private:
  T& d_value;
  Ts& d_values;
};

/** Set a flag back to false. */
class ResetFlagTrail : public Trail
{
 public:
  ResetFlagTrail(bool& value) : d_value(value) {}

  void undo() override { d_value = false; }

 private:
  bool& d_value;
};

/** Set a pointer back to null. */
template <typename T>
class SetPtrTrail : public Trail
{
 public:
  SetPtrTrail(T*& ptr) : d_ptr(ptr) { Assert(d_ptr == nullptr); }

  void undo() override { d_ptr = nullptr; }

 private:
  T*& d_ptr;
};

/** Shrink a vector back to the size it had when the object was created. */
template <typename V>
class RestoreVector : public Trail
{
 public:
  RestoreVector(V& v) : d_vector(v), d_oldSize(v.size()) {}

  RestoreVector(V& v, size_t sz) : d_vector(v), d_oldSize(sz) {}

  void undo() override { d_vector.resize(d_oldSize); }

 private:
  V& d_vector;
  size_t d_oldSize;
};

/** Restore one element of a vector. */
template <typename V>
class VectorValueTrail : public Trail
{
 public:
  VectorValueTrail(V& v, size_t idx)
      : d_vector(v), d_idx(idx), d_oldValue(v[idx])
  {
  }

  void undo() override { d_vector[d_idx] = d_oldValue; }

 private:
  V& d_vector;
  size_t d_idx;
  typename V::value_type d_oldValue;
};

/** Restore one element of a vector of vectors. */
template <typename V, typename T>
class Vector2ValueTrail : public Trail
{
 public:
  Vector2ValueTrail(V& v, size_t i, size_t j)
      : d_vector(v), d_i(i), d_j(j), d_oldValue(v[i][j])
  {
  }

  void undo() override { d_vector[d_i][d_j] = d_oldValue; }

 private:
  V& d_vector;
  size_t d_i;
  size_t d_j;
  T d_oldValue;
};

/** Undo a push_back. */
template <typename V>
class PushBackVector : public Trail
{
 public:
  PushBackVector(V& v) : d_vector(v) {}

  void undo() override { d_vector.pop_back(); }

 private:
  V& d_vector;
};

/** Undo a push_back; Z3 spells the same thing two ways. */
template <typename V>
using PushBackTrail = PushBackVector<V>;

/** Undo a push_back into one row of a vector of vectors. */
template <typename V>
class PushBack2Trail : public Trail
{
 public:
  PushBack2Trail(V& v, size_t index) : d_vector(v), d_index(index) {}

  void undo() override { d_vector[d_index].pop_back(); }

 private:
  V& d_vector;
  size_t d_index;
};

/** Undo a pop_back by restoring the element that was removed. */
template <typename V>
class PopBackTrail : public Trail
{
 public:
  PopBackTrail(V& v) : d_vector(v), d_value(v.back()) {}

  void undo() override { d_vector.push_back(d_value); }

 private:
  V& d_vector;
  typename V::value_type d_value;
};

/** Set a vector entry back to null. */
template <typename V>
class SetVectorIdxTrail : public Trail
{
 public:
  SetVectorIdxTrail(V& v, size_t idx) : d_vector(v), d_idx(idx) {}

  void undo() override { d_vector[d_idx] = nullptr; }

 private:
  V& d_vector;
  size_t d_idx;
};

/** Set a bit of a Boolean vector, and clear it again on undo. */
template <typename V>
class SetBitvectorTrail : public Trail
{
 public:
  SetBitvectorTrail(V& v, size_t idx) : d_vector(v), d_idx(idx)
  {
    Assert(!d_vector[d_idx]);
    d_vector[d_idx] = true;
  }

  void undo() override { d_vector[d_idx] = false; }

 private:
  V& d_vector;
  size_t d_idx;
};

/** Remove a key that was inserted into a map. */
template <typename M, typename D>
class InsertMap : public Trail
{
 public:
  InsertMap(M& t, const D& o) : d_map(t), d_obj(o) {}

  void undo() override { d_map.erase(d_obj); }

 private:
  M& d_map;
  D d_obj;
};

/** Reinsert a key/value pair that was removed from a map. */
template <typename M, typename D, typename R>
class RemoveMap : public Trail
{
 public:
  RemoveMap(M& t, const D& o, const R& v) : d_map(t), d_obj(o), d_value(v) {}

  void undo() override { d_map[d_obj] = d_value; }

 private:
  M& d_map;
  D d_obj;
  R d_value;
};

/** Remove an element that was inserted into a set. */
template <typename S, typename T>
class InsertObjTrail : public Trail
{
 public:
  InsertObjTrail(S& t, const T& o) : d_table(t), d_obj(o) {}

  void undo() override { d_table.erase(d_obj); }

 private:
  S& d_table;
  T d_obj;
};

/** Reinsert an element that was removed from a set. */
template <typename S, typename T>
class RemoveObjTrail : public Trail
{
 public:
  RemoveObjTrail(S& t, const T& o) : d_table(t), d_obj(o) {}

  void undo() override { d_table.insert(d_obj); }

 private:
  S& d_table;
  T d_obj;
};

/** Delete a heap-allocated object. */
template <typename T>
class NewObjTrail : public Trail
{
 public:
  NewObjTrail(T* obj) : d_obj(obj) {}

  void undo() override { delete d_obj; }

 private:
  T* d_obj;
};

/**
 * Undo trail objects down to oldSize, destroying them as it goes. The objects
 * themselves live in a region, so only their destructors run here; the memory
 * is reclaimed when the region scope is popped.
 */
inline void undoTrailStack(std::vector<Trail*>& s, size_t oldSize)
{
  Assert(oldSize <= s.size());
  size_t i = s.size();
  while (i != oldSize)
  {
    --i;
    s[i]->undo();
    s[i]->~Trail();
  }
  s.resize(oldSize);
}

/**
 * A stack of scopes, each holding the trail objects to undo when it is popped.
 *
 * Trail objects are allocated in a region whose scopes are kept in lockstep
 * with this stack, so pushing a trail object costs a pointer bump.
 */
class TrailStack
{
 public:
  ~TrailStack() { reset(); }

  Region& getRegion() { return d_region; }

  void reset()
  {
    popScope(d_scopes.size());
    // Undo the trail objects at level 0 as well, so that e.g. NewObjTrail
    // does not leak.
    undoTrailStack(d_trailStack, 0);
  }

  /** Push an already-allocated trail object. */
  void pushPtr(Trail* t) { d_trailStack.push_back(t); }

  /** Copy obj into the region and push it. */
  template <typename TrailObject>
  void push(const TrailObject& obj)
  {
    d_trailStack.push_back(new (d_region) TrailObject(obj));
  }

  size_t getNumScopes() const { return d_scopes.size(); }

  void pushScope()
  {
    d_region.pushScope();
    d_scopes.push_back(d_trailStack.size());
  }

  void popScope(size_t numScopes)
  {
    if (numScopes == 0)
    {
      return;
    }
    size_t lvl = d_scopes.size();
    Assert(numScopes <= lvl);
    size_t newLvl = lvl - numScopes;
    size_t oldSize = d_scopes[newLvl];
    undoTrailStack(d_trailStack, oldSize);
    d_scopes.resize(newLvl);
    d_region.popScope(numScopes);
  }

  size_t size() const { return d_trailStack.size(); }

  void shrink(size_t newSize)
  {
    Assert(newSize <= d_trailStack.size());
    d_trailStack.resize(newSize);
  }

 private:
  std::vector<Trail*> d_trailStack;
  std::vector<size_t> d_scopes;
  Region d_region;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__TRAIL_H */

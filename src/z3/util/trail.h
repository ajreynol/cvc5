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

  void undo() override { d_value = d_oldValue; }

 private:
  T& d_value;
  T d_oldValue;
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

/** Undo a trail object owned elsewhere; see TrailStack::pushPtr. */
class PtrTrail : public Trail
{
 public:
  PtrTrail(Trail* t) : d_trail(t) {}

  void undo() override { d_trail->undo(); }

 private:
  Trail* d_trail;
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
 * Trail objects are allocated in a region, owned by the owner of the stack,
 * whose scopes are kept in lockstep with this stack, so pushing a trail object
 * costs a pointer bump.
 */
class TrailStack
{
 public:
  TrailStack(Region& region) : d_region(region) {}
  ~TrailStack() { reset(); }

  Region& getRegion() { return d_region; }

  void reset()
  {
    popScope(d_scopes.size());
    // Undo the trail objects at level 0 as well, so that e.g. NewObjTrail
    // does not leak.
    undoTrailStack(d_trailStack, 0);
  }

  /**
   * Push a trail object that is not owned by the stack, such as a member of
   * its owner, which is undone but not destroyed: it is pushed through a
   * forwarder in the region, which undoTrailStack destroys instead.
   */
  void pushPtr(Trail* t) { push(PtrTrail(t)); }

  /** Copy obj into the region and push it. */
  template <typename TrailObject>
  void push(const TrailObject& obj)
  {
    d_trailStack.push_back(new (d_region) TrailObject(obj));
  }

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

 private:
  std::vector<Trail*> d_trailStack;
  std::vector<size_t> d_scopes;
  Region& d_region;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__TRAIL_H */

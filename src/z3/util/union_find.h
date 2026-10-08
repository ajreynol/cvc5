/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A backtrackable union-find over theory variables.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), file
 * src/util/union_find.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__UNION_FIND_H
#define CVC5__Z3__UTIL__UNION_FIND_H

#include <algorithm>
#include <ostream>
#include <vector>

#include "base/check.h"
#include "z3/util/trail.h"

namespace cvc5::internal {
namespace z3 {

/**
 * A union-find whose merges are undone when the owning trail stack pops.
 *
 * The context type Ctx has to provide getTrailStack(), mergeEh(r2, r1, v2,
 * v1), afterMergeEh(r2, r1, v2, v1) and unmergeEh(r2, r1), which is how the
 * theory using it learns about the class merges.
 */
template <typename Ctx>
class UnionFind
{
 public:
  UnionFind(Ctx& ctx)
      : d_ctx(ctx), d_trailStack(ctx.getTrailStack()), d_mkVarTrail(*this)
  {
  }

  uint32_t mkVar()
  {
    uint32_t r = static_cast<uint32_t>(d_find.size());
    d_find.push_back(r);
    d_size.push_back(1);
    d_next.push_back(r);
    d_trailStack.pushPtr(&d_mkVarTrail);
    return r;
  }

  void reserve(uint32_t v)
  {
    while (getNumVars() <= v)
    {
      mkVar();
    }
  }

  uint32_t getNumVars() const { return static_cast<uint32_t>(d_find.size()); }

  uint32_t find(uint32_t v) const
  {
    for (;;)
    {
      Assert(v < d_find.size());
      uint32_t newV = d_find[v];
      if (newV == v)
      {
        return v;
      }
      v = newV;
    }
  }

  uint32_t next(uint32_t v) const { return d_next[v]; }

  uint32_t size(uint32_t v) const { return d_size[find(v)]; }

  bool isRoot(uint32_t v) const { return d_find[v] == v; }

  void merge(uint32_t v1, uint32_t v2)
  {
    uint32_t r1 = find(v1);
    uint32_t r2 = find(v2);
    if (r1 == r2)
    {
      return;
    }
    if (d_size[r1] > d_size[r2])
    {
      std::swap(r1, r2);
      std::swap(v1, v2);
    }
    d_ctx.mergeEh(r2, r1, v2, v1);
    d_find[r1] = r2;
    d_size[r2] += d_size[r1];
    std::swap(d_next[r1], d_next[r2]);
    d_trailStack.push(MergeTrail(*this, r1));
    d_ctx.afterMergeEh(r2, r1, v2, v1);
  }

  void print(std::ostream& out) const
  {
    uint32_t num = getNumVars();
    for (uint32_t v = 0; v < num; ++v)
    {
      out << "v" << v << " --> v" << d_find[v] << " (" << size(v) << ")\n";
    }
  }

 private:
  /** Drop the variable created last when its scope is popped. */
  class MkVarTrail : public Trail
  {
   public:
    MkVarTrail(UnionFind& o) : d_owner(o) {}

    void undo() override
    {
      d_owner.d_find.pop_back();
      d_owner.d_size.pop_back();
      d_owner.d_next.pop_back();
    }

   private:
    UnionFind& d_owner;
  };

  /** Undo the merge that made r1 a non-root. */
  class MergeTrail : public Trail
  {
   public:
    MergeTrail(UnionFind& o, uint32_t r1) : d_owner(o), d_r1(r1) {}

    void undo() override { d_owner.unmerge(d_r1); }

   private:
    UnionFind& d_owner;
    uint32_t d_r1;
  };

  void unmerge(uint32_t r1)
  {
    uint32_t r2 = d_find[r1];
    Assert(find(r2) == r2);
    d_size[r2] -= d_size[r1];
    d_find[r1] = r1;
    std::swap(d_next[r1], d_next[r2]);
    d_ctx.unmergeEh(r2, r1);
  }

  Ctx& d_ctx;
  TrailStack& d_trailStack;
  std::vector<uint32_t> d_find;
  std::vector<uint32_t> d_size;
  std::vector<uint32_t> d_next;
  MkVarTrail d_mkVarTrail;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__UNION_FIND_H */

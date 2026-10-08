/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The watch list of a literal.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/watch_list.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__WATCH_LIST_H
#define CVC5__Z3__WATCH_LIST_H

#include <algorithm>

#include "z3/clause.h"
#include "z3/util/literal.h"

namespace cvc5::internal {
namespace z3 {

/**
 * The list of clauses and literals watching a given literal.
 *
 * One allocation holds both, growing towards each other from opposite ends,
 * with a three-word header stored just before the data pointer:
 *
 *  ------------------------------------------------------------------------
 *  | endCls | beginLits | end |  clauses  | ->        <- |  literals      |
 *  ------------------------------------------------------------------------
 *  ^                      ^                ^              ^
 *  d_data               endCls          beginLits       endLits
 *
 * When used for unit propagation, a literal l1 in the watch list of l2
 * represents the binary clause (or l1 (not l2)).
 */
class WatchList
{
 public:
  WatchList() : d_data(nullptr) {}

  WatchList(WatchList&& other) noexcept : d_data(nullptr)
  {
    std::swap(d_data, other.d_data);
  }

  WatchList(const WatchList&) = delete;
  WatchList& operator=(const WatchList&) = delete;

  ~WatchList() { destroy(); }

  size_t size() const
  {
    if (d_data != nullptr)
    {
      return reinterpret_cast<uint32_t*>(d_data)[-3]
             + reinterpret_cast<uint32_t*>(d_data)[-1]
             - reinterpret_cast<uint32_t*>(d_data)[-2];
    }
    return 0;
  }

  using ClauseIterator = Clause**;

  void reset()
  {
    if (d_data != nullptr)
    {
      endClsCore() = 0;
      beginLitsCore() = endLitsCore();
    }
  }

  void resetAndReleaseMemory()
  {
    destroy();
    d_data = nullptr;
  }

  ClauseIterator beginClause() { return reinterpret_cast<Clause**>(d_data); }

  ClauseIterator endClause()
  {
    return reinterpret_cast<Clause**>(d_data + endCls());
  }

  ClauseIterator findClause(const Clause* c)
  {
    return std::find(beginClause(), endClause(), c);
  }

  Literal* beginLiterals()
  {
    return reinterpret_cast<Literal*>(d_data + beginLits());
  }

  Literal* endLiterals()
  {
    return reinterpret_cast<Literal*>(d_data + endLits());
  }

  const Literal* beginLiterals() const
  {
    return reinterpret_cast<const Literal*>(d_data + beginLits());
  }

  const Literal* endLiterals() const
  {
    return reinterpret_cast<const Literal*>(d_data + endLits());
  }

  Literal* findLiteral(const Literal& l)
  {
    return std::find(beginLiterals(), endLiterals(), l);
  }

  const Literal* findLiteral(const Literal& l) const
  {
    return std::find(beginLiterals(), endLiterals(), l);
  }

  void insertClause(Clause* c)
  {
    if (d_data == nullptr
        || endClsCore() + sizeof(Clause*) >= beginLitsCore())
    {
      expand();
    }
    *(reinterpret_cast<Clause**>(d_data + endClsCore())) = c;
    endClsCore() += sizeof(Clause*);
  }

  void insertLiteral(const Literal& l)
  {
    if (d_data == nullptr
        || beginLitsCore() <= endClsCore() + sizeof(Literal))
    {
      expand();
    }
    Assert(beginLitsCore() >= sizeof(Literal));
    beginLitsCore() -= sizeof(Literal);
    *(reinterpret_cast<Literal*>(d_data + beginLitsCore())) = l;
  }

  void removeClause(Clause* c);

  void removeDeleted();

  void removeLiteral(Literal l);

  void setEndClause(ClauseIterator newEnd)
  {
    Assert(newEnd <= endClause());
    if (d_data != nullptr)
    {
      endClsCore() =
          static_cast<uint32_t>(reinterpret_cast<char*>(newEnd) - d_data);
    }
  }

 private:
  void expand();
  void destroy();

  uint32_t& endClsCore()
  {
    Assert(d_data != nullptr);
    return reinterpret_cast<uint32_t*>(d_data)[-3];
  }

  uint32_t endCls() { return d_data != nullptr ? endClsCore() : 0; }

  uint32_t& beginLitsCore()
  {
    Assert(d_data != nullptr);
    return reinterpret_cast<uint32_t*>(d_data)[-2];
  }

  uint32_t beginLitsCore() const
  {
    Assert(d_data != nullptr);
    return reinterpret_cast<uint32_t*>(d_data)[-2];
  }

  uint32_t beginLits() const { return d_data != nullptr ? beginLitsCore() : 0; }

  uint32_t& endLitsCore()
  {
    Assert(d_data != nullptr);
    return reinterpret_cast<uint32_t*>(d_data)[-1];
  }

  uint32_t endLitsCore() const
  {
    Assert(d_data != nullptr);
    return reinterpret_cast<uint32_t*>(d_data)[-1];
  }

  uint32_t endLits() const { return d_data != nullptr ? endLitsCore() : 0; }

  char* d_data;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__WATCH_LIST_H */

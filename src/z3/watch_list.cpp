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
 * file src/smt/watch_list.cpp, and recast in cvc5 style.
 */

#include "z3/watch_list.h"

#include <cstdlib>
#include <cstring>
#include <new>

namespace cvc5::internal {
namespace z3 {

namespace {
/** The initial capacity of the data area, in bytes. */
constexpr uint32_t s_defaultWatchListSize = sizeof(Clause*) * 4;
/**
 * The header is three unsigneds, padded to keep the data area pointer-aligned
 * on 64 bit machines.
 */
constexpr uint32_t s_headerSize =
    sizeof(void*) == 8 ? 4 * sizeof(uint32_t) : 3 * sizeof(uint32_t);
}  // namespace

void WatchList::destroy()
{
  if (d_data != nullptr)
  {
    std::free(d_data - s_headerSize);
  }
}

void WatchList::expand()
{
  if (d_data == nullptr)
  {
    uint32_t size = s_defaultWatchListSize + s_headerSize;
    char* raw = static_cast<char*>(std::malloc(size));
    if (raw == nullptr)
    {
      throw std::bad_alloc();
    }
    uint32_t* mem = reinterpret_cast<uint32_t*>(raw);
    if (sizeof(void*) == 8)
    {
      // keep the data area pointer-aligned
      ++mem;
    }
    *mem = 0;
    ++mem;
    *mem = s_defaultWatchListSize;
    ++mem;
    *mem = s_defaultWatchListSize;
    ++mem;
    d_data = reinterpret_cast<char*>(mem);
    Assert(beginLitsCore() % sizeof(Literal) == 0);
  }
  else
  {
    uint32_t currBeginBin = beginLitsCore();
    uint32_t currCapacity = endLitsCore();
    uint32_t binBytes = currCapacity - currBeginBin;
    // Literals must stay four-byte aligned, hence the rounding.
    uint32_t newCapacity =
        (((currCapacity * 3 + sizeof(Clause*)) >> 1) + 3) & ~3u;
    char* raw = static_cast<char*>(std::malloc(newCapacity + s_headerSize));
    if (raw == nullptr)
    {
      throw std::bad_alloc();
    }
    uint32_t* mem = reinterpret_cast<uint32_t*>(raw);
    uint32_t currEndCls = endClsCore();
    if (sizeof(void*) == 8)
    {
      ++mem;
    }
    *mem = currEndCls;
    ++mem;
    Assert(binBytes <= newCapacity);
    uint32_t newBeginBin = newCapacity - binBytes;
    *mem = newBeginBin;
    ++mem;
    *mem = newCapacity;
    ++mem;
    std::memcpy(mem, d_data, currEndCls);
    std::memcpy(reinterpret_cast<char*>(mem) + newBeginBin,
                d_data + currBeginBin,
                binBytes);
    destroy();
    d_data = reinterpret_cast<char*>(mem);
    Assert(beginLitsCore() % sizeof(Literal) == 0);
  }
}

void WatchList::removeClause(Clause* c)
{
  ClauseIterator begin = beginClause();
  ClauseIterator end = endClause();
  ClauseIterator it = std::find(begin, end, c);
  if (it == end)
  {
    return;
  }
  ClauseIterator prev = it;
  ++it;
  for (; it != end; ++it, ++prev)
  {
    *prev = *it;
  }
  endClsCore() -= sizeof(Clause*);
}

void WatchList::removeDeleted()
{
  ClauseIterator end = endClause();
  ClauseIterator it = beginClause();
  ClauseIterator prev = it;
  uint32_t numDeleted = 0;
  for (; it != end; ++it)
  {
    if ((*it)->deleted())
    {
      ++numDeleted;
    }
    else
    {
      *prev++ = *it;
    }
  }
  if (numDeleted > 0)
  {
    endClsCore() -= numDeleted * sizeof(Clause*);
  }
}

void WatchList::removeLiteral(Literal l)
{
  Literal* begin = beginLiterals();
  Literal* end = endLiterals();
  Literal* it = std::find(begin, end, l);
  if (it == end)
  {
    return;
  }
  Literal* prev = it;
  while (it != begin)
  {
    Assert(it == prev);
    --it;
    *prev = *it;
    --prev;
  }
  Assert(prev == begin);
  beginLitsCore() += sizeof(Literal);
}

}  // namespace z3
}  // namespace cvc5::internal

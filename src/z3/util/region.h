/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Region/arena memory manager.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/util/region.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__REGION_H
#define CVC5__Z3__UTIL__REGION_H

#include <cstddef>
#include <ostream>

namespace cvc5::internal {
namespace z3 {

/**
 * An explicit region (arena) memory manager.
 *
 * Objects are allocated by bumping a pointer within a page. Deallocation is
 * only possible in bulk, by popping a scope: everything allocated since the
 * matching pushScope() is released at once. Destructors are *not* run, so
 * only objects whose destruction is a no-op (or whose destruction is arranged
 * for separately, as the trail stack does) may be allocated here.
 */
class Region
{
  /** The payload size of a regular page. */
  static constexpr size_t s_defaultPageSize = 8192 - sizeof(size_t);

  /**
   * A page of memory. The header is stored immediately before the payload,
   * so that payload pointers are what gets handed out.
   */
  struct Page
  {
    /** The previously allocated page, forming a singly linked stack. */
    Page* d_prev;
    /** The usable size of this page, in bytes. */
    size_t d_size;
  };

  /** A saved allocation position, used to implement scopes. */
  struct Mark
  {
    Page* d_page;
    char* d_ptr;
    Mark* d_prev;
  };

 public:
  Region();
  ~Region();

  Region(const Region&) = delete;
  Region& operator=(const Region&) = delete;

  /** Allocate size bytes. The result is suitably aligned for any object. */
  void* allocate(size_t size);

  /** Release all memory and return to a single empty page. */
  void reset();

  /** Remember the current allocation position. */
  void pushScope();

  /** Release everything allocated since the matching pushScope(). */
  void popScope();

  /** Pop numScopes scopes. */
  void popScope(size_t numScopes);

  /** Print the number of pages currently held, for debugging. */
  void printMemStats(std::ostream& out) const;

 private:
  /** Alignment applied to every allocation. */
  static constexpr size_t s_align = alignof(std::max_align_t);

  /** Round size up to the next multiple of s_align. */
  static constexpr size_t align(size_t size)
  {
    return (size + s_align - 1) & ~(s_align - 1);
  }

  /** Payload pointer of a page. */
  static char* payload(Page* p)
  {
    return reinterpret_cast<char*>(p) + align(sizeof(Page));
  }

  /** Make a fresh page with the given payload size the current page. */
  void allocatePage(size_t size);

  /** Move the current page onto the free list (or free it, if oversized). */
  void recycleCurrentPage();

  /** The page we are currently allocating from. */
  Page* d_currPage;
  /** Next free byte in the current page. */
  char* d_currPtr;
  /** One past the last usable byte of the current page. */
  char* d_currEndPtr;
  /** Recycled regular-sized pages, available for reuse. */
  Page* d_freePages;
  /** The innermost scope mark, itself allocated in this region. */
  Mark* d_mark;
};

}  // namespace z3
}  // namespace cvc5::internal

/** Placement new that allocates from a region. */
inline void* operator new(size_t s, cvc5::internal::z3::Region& r)
{
  return r.allocate(s);
}

/** Placement new[] that allocates from a region. */
inline void* operator new[](size_t s, cvc5::internal::z3::Region& r)
{
  return r.allocate(s);
}

/** Matching delete for region placement new; regions free in bulk. */
inline void operator delete(void*, cvc5::internal::z3::Region&) {}

/** Matching delete[] for region placement new[]; regions free in bulk. */
inline void operator delete[](void*, cvc5::internal::z3::Region&) {}

#endif /* CVC5__Z3__UTIL__REGION_H */

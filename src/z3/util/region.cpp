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
 * file src/util/region.cpp, and recast in cvc5 style.
 */

#include "z3/util/region.h"

#include <cstdlib>
#include <new>

#include "base/check.h"

namespace cvc5::internal {
namespace z3 {

Region::Region()
    : d_currPage(nullptr),
      d_currPtr(nullptr),
      d_currEndPtr(nullptr),
      d_freePages(nullptr),
      d_mark(nullptr)
{
  allocatePage(s_defaultPageSize);
}

Region::~Region()
{
  while (d_currPage != nullptr)
  {
    Page* prev = d_currPage->d_prev;
    std::free(d_currPage);
    d_currPage = prev;
  }
  while (d_freePages != nullptr)
  {
    Page* prev = d_freePages->d_prev;
    std::free(d_freePages);
    d_freePages = prev;
  }
}

void Region::allocatePage(size_t size)
{
  Page* page = nullptr;
  if (size == s_defaultPageSize && d_freePages != nullptr)
  {
    // reuse a recycled page
    page = d_freePages;
    d_freePages = page->d_prev;
  }
  else
  {
    void* mem = std::malloc(align(sizeof(Page)) + size);
    if (mem == nullptr)
    {
      throw std::bad_alloc();
    }
    page = static_cast<Page*>(mem);
    page->d_size = size;
  }
  page->d_prev = d_currPage;
  d_currPage = page;
  d_currPtr = payload(page);
  d_currEndPtr = d_currPtr + page->d_size;
}

void Region::recycleCurrentPage()
{
  Assert(d_currPage != nullptr);
  Page* prev = d_currPage->d_prev;
  if (d_currPage->d_size == s_defaultPageSize)
  {
    d_currPage->d_prev = d_freePages;
    d_freePages = d_currPage;
  }
  else
  {
    std::free(d_currPage);
  }
  d_currPage = prev;
}

void* Region::allocate(size_t size)
{
  size = align(size);
  // fast path: the current page has room
  if (d_currPtr + size <= d_currEndPtr)
  {
    char* result = d_currPtr;
    d_currPtr += size;
    return result;
  }
  if (size <= s_defaultPageSize)
  {
    allocatePage(s_defaultPageSize);
    char* result = d_currPtr;
    d_currPtr += size;
    return result;
  }
  // The request does not fit in a regular page. Give it a page of its own,
  // then install a fresh regular page so that subsequent small allocations
  // do not waste the remainder of the oversized one. Note the oversized page
  // is below the fresh one in the page stack, so it is released by the same
  // scope.
  allocatePage(size);
  char* result = d_currPtr;
  allocatePage(s_defaultPageSize);
  return result;
}

void Region::reset()
{
  while (d_currPage != nullptr)
  {
    recycleCurrentPage();
  }
  d_currPtr = nullptr;
  d_currEndPtr = nullptr;
  d_mark = nullptr;
  allocatePage(s_defaultPageSize);
}

void Region::pushScope()
{
  Page* currPage = d_currPage;
  char* currPtr = d_currPtr;
  Mark* mark = static_cast<Mark*>(allocate(sizeof(Mark)));
  mark->d_page = currPage;
  mark->d_ptr = currPtr;
  mark->d_prev = d_mark;
  d_mark = mark;
}

void Region::popScope()
{
  Assert(d_mark != nullptr);
  Page* oldCurrPage = d_mark->d_page;
  char* oldCurrPtr = d_mark->d_ptr;
  d_mark = d_mark->d_prev;
  while (d_currPage != oldCurrPage)
  {
    recycleCurrentPage();
  }
  Assert(d_currPage != nullptr);
  d_currPtr = oldCurrPtr;
  d_currEndPtr = payload(d_currPage) + d_currPage->d_size;
}

void Region::popScope(size_t numScopes)
{
  for (size_t i = 0; i < numScopes; ++i)
  {
    popScope();
  }
}

void Region::printMemStats(std::ostream& out) const
{
  size_t n = 0;
  for (Page* p = d_currPage; p != nullptr; p = p->d_prev)
  {
    n++;
  }
  out << "num. pages:      " << n << "\n";
}

}  // namespace z3
}  // namespace cvc5::internal

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A scoped undo trail, private to eager E-matching.
 */

#include "theory/quantifiers/eager/trail.h"

#include "base/check.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

void Trail::pushScope()
{
  d_scopes.push_back({d_entries.size(), d_callbacks.size()});
}

void Trail::popScope(size_t n)
{
  Assert(n <= d_scopes.size());
  const Scope& s = d_scopes[d_scopes.size() - n];
  size_t target = s.d_entriesSize;
  size_t cbTarget = s.d_callbacksSize;
  while (d_entries.size() > target)
  {
    undo(d_entries.back());
    d_entries.pop_back();
  }
  // the callbacks of the popped scopes have all been run
  d_callbacks.resize(cbTarget);
  d_scopes.resize(d_scopes.size() - n);
}

void Trail::reset()
{
  while (!d_entries.empty())
  {
    undo(d_entries.back());
    d_entries.pop_back();
  }
  d_scopes.clear();
  d_callbacks.clear();
}

void Trail::undo(const Entry& e)
{
  switch (e.d_kind)
  {
    case Kind::RESTORE_APPROX_SET:
    {
      *static_cast<ApproxSet*>(e.d_ptr) = ApproxSet::fromBits(e.d_data);
    }
    break;
    case Kind::RESTORE_UINT32:
      *static_cast<uint32_t*>(e.d_ptr) = static_cast<uint32_t>(e.d_data);
      break;
    case Kind::RESTORE_SIZE:
      static_cast<Shrinkable*>(e.d_ptr)->shrinkTo(e.d_data);
      break;
    case Kind::CALLBACK:
      Assert(e.d_data < d_callbacks.size());
      d_callbacks[e.d_data]();
      break;
  }
}

void Trail::restore(ApproxSet* s)
{
  d_entries.push_back({Kind::RESTORE_APPROX_SET, s, s->bits()});
}

void Trail::restore(uint32_t* u)
{
  d_entries.push_back({Kind::RESTORE_UINT32, u, *u});
}

void Trail::restoreSize(Shrinkable* v, size_t size)
{
  d_entries.push_back({Kind::RESTORE_SIZE, v, size});
}

void Trail::onPop(std::function<void()> f)
{
  d_callbacks.push_back(f);
  d_entries.push_back({Kind::CALLBACK, nullptr, d_callbacks.size() - 1});
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

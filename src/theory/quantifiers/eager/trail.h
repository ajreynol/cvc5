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
 *
 * This is the analogue of z3's util/trail.h (trail_stack). It is intentionally
 * not cvc5's context::Context: the state of eager E-matching is separate from
 * the rest of the system, and (for the inner SMT solver) needs to support
 * retraction that does not correspond to a scope pop. See
 * theory/quantifiers/eager/README.md section 3.2.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__TRAIL_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__TRAIL_H

#include <cstdint>
#include <functional>
#include <vector>

#include "theory/quantifiers/eager/approx_set.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

/**
 * Base class for containers whose size the trail can restore. Used instead of
 * type erasing the element type of a vector.
 */
class Shrinkable
{
 public:
  virtual ~Shrinkable() {}
  /** Shrink to n elements */
  virtual void shrinkTo(size_t n) = 0;
};

/** A vector whose size can be restored by a Trail */
template <class T>
class TrailedVector : public Shrinkable, public std::vector<T>
{
 public:
  void shrinkTo(size_t n) override { this->resize(n); }
};

/**
 * A stack of scopes, each of which collects the undo actions that must be
 * performed when the scope is popped.
 */
class Trail
{
 public:
  Trail() {}
  ~Trail() {}

  /** Push a scope */
  void pushScope();
  /** Pop n scopes */
  void popScope(size_t n = 1);
  /** The number of scopes currently pushed */
  size_t getNumScopes() const { return d_scopes.size(); }
  /** Pop all scopes and undo everything */
  void reset();

  /** Restore the current value of s when the current scope is popped */
  void restore(ApproxSet* s);
  /** Restore the current value of u when the current scope is popped */
  void restore(uint32_t* u);
  /** Restore the current size of v when the current scope is popped */
  void restoreSize(Shrinkable* v, size_t size);
  /** Run f when the current scope is popped */
  void onPop(std::function<void()> f);

 private:
  enum class Kind
  {
    RESTORE_APPROX_SET,
    RESTORE_UINT32,
    RESTORE_SIZE,
    CALLBACK
  };
  struct Entry
  {
    Kind d_kind;
    void* d_ptr;
    uint64_t d_data;
  };
  /** Undo a single entry */
  void undo(const Entry& e);
  /** The entries, in the order they were added */
  std::vector<Entry> d_entries;
  /** For each scope, the sizes of d_entries and d_callbacks when pushed */
  struct Scope
  {
    size_t d_entriesSize;
    size_t d_callbacksSize;
  };
  std::vector<Scope> d_scopes;
  /** Callbacks, referenced by index from CALLBACK entries */
  std::vector<std::function<void()>> d_callbacks;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The congruence table, keyed on the declaration and the equivalence class
 * roots of the arguments.
 *
 * Ported from Z3: src/smt/smt_cg_table.h.
 * Z3 is Copyright (c) Microsoft Corporation and licensed under the MIT
 * License, see licenses/z3-LICENSE.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__CG_TABLE_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__CG_TABLE_H

#include <unordered_set>

#include "theory/quantifiers/eager/enode.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

/**
 * The congruence table: a set of enodes, one per congruence class, in which
 * two enodes are equal if they are congruent (see congruentApps).
 *
 * Z3 splits the table per declaration and specializes it by arity; this port
 * uses a single std::unordered_set.
 */
class CgTable
{
  /**
   * Hashes an enode by its declaration and the roots of its arguments,
   * ignoring the argument order for a commutative node.
   */
  struct Hash
  {
    /** The hash of n modulo the classes of its arguments. */
    size_t operator()(ENode* n) const;
  };

  /** Equality modulo congruence. */
  struct Eq
  {
    /** True if n1 and n2 are congruent; see congruentApps. */
    bool operator()(ENode* n1, ENode* n2) const
    {
      return congruentApps(n1, n2);
    }
  };

 public:
  /**
   * Try to insert n. If the table already contains an element congruent to
   * n, then nothing is inserted and that element is returned. Otherwise n is
   * inserted and returned.
   */
  ENode* insert(ENode* n)
  {
    Assert(n->getNumArgs() > 0);
    return *d_table.insert(n).first;
  }

  /** Remove the element congruent to n, which callers expect to be n. */
  void erase(ENode* n) { d_table.erase(n); }

  /** The element congruent to n, or null. */
  ENode* find(ENode* n) const
  {
    auto it = d_table.find(n);
    return it == d_table.end() ? nullptr : *it;
  }

  /** True if n itself is the element of the table congruent to n. */
  bool containsPtr(ENode* n) const { return find(n) == n; }

 private:
  /** The elements, hashed and compared modulo congruence. */
  std::unordered_set<ENode*, Hash, Eq> d_table;
};

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER__CG_TABLE_H */

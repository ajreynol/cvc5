/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Clauses of the ported Z3 SMT core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_clause.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__RELEVANCY__CLAUSE_H
#define CVC5__Z3__RELEVANCY__CLAUSE_H

#include <vector>

#include "z3/util/literal.h"

namespace cvc5::internal {
namespace z3 {

/**
 * An auxiliary clause of the ported Z3 core, which encodes the Boolean
 * structure of the input and is deleted on backtracking.
 *
 * As in Z3, the literals are stored inline immediately after the header, so
 * that a clause costs one allocation and its literals are contiguous.
 */
class Clause
{
 public:
  /** Create a new clause. */
  static Clause* mk(size_t numLits, Literal* lits);

  void deallocate();

  Literal& getLiteral(size_t idx)
  {
    Assert(idx < d_numLiterals);
    return litsPtr()[idx];
  }

  Literal* begin() { return litsPtr(); }

  Literal* end() { return litsPtr() + d_numLiterals; }

  void markAsDeleted()
  {
    Assert(!d_deleted);
    d_deleted = true;
  }

  bool deleted() const { return d_deleted; }

 private:
  uint32_t d_numLiterals;
  /**
   * true if the clause is marked for deletion but was not deleted yet,
   * because it is still referenced from somewhere
   */
  uint32_t d_deleted : 1;

  Literal* litsPtr()
  {
    return reinterpret_cast<Literal*>(reinterpret_cast<char*>(this)
                                      + sizeof(Clause));
  }

  const Literal* litsPtr() const
  {
    return reinterpret_cast<const Literal*>(reinterpret_cast<const char*>(this)
                                            + sizeof(Clause));
  }

  friend class PropCore;

  void setLiteral(size_t idx, Literal l) { litsPtr()[idx] = l; }
};

using ClauseVector = std::vector<Clause*>;

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__RELEVANCY__CLAUSE_H */

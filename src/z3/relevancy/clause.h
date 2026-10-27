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

#include "base/check.h"
#include "prop/sat_solver_types.h"

namespace cvc5::internal {
namespace z3 {

/** The Boolean variables and literals of the core are cvc5's SAT ones. */
using prop::SatLiteral;
using prop::SatVariable;

/** The variable reserved for the constant true. */
inline constexpr SatVariable s_trueBoolVar = 0;
/** The literal that is always true. */
inline constexpr SatLiteral s_trueLiteral(s_trueBoolVar, false);
/** The literal that is always false. */
inline constexpr SatLiteral s_falseLiteral(s_trueBoolVar, true);

/**
 * An auxiliary clause of the ported Z3 core, which encodes the Boolean
 * structure of the input and is deleted on backtracking. Its first two
 * literals are the watched ones.
 */
class Clause
{
 public:
  Clause(size_t numLits, const SatLiteral* lits)
      : d_lits(lits, lits + numLits), d_deleted(false)
  {
    Assert(numLits >= 2);
  }

  SatLiteral getLiteral(size_t idx) const
  {
    Assert(idx < d_lits.size());
    return d_lits[idx];
  }

  void setLiteral(size_t idx, SatLiteral l)
  {
    Assert(idx < d_lits.size());
    d_lits[idx] = l;
  }

  SatLiteral* begin() { return d_lits.data(); }

  SatLiteral* end() { return d_lits.data() + d_lits.size(); }

  void markAsDeleted()
  {
    Assert(!d_deleted);
    d_deleted = true;
  }

  /**
   * True if the clause is marked for deletion but was not deleted yet,
   * because it is still referenced from somewhere.
   */
  bool deleted() const { return d_deleted; }

 private:
  std::vector<SatLiteral> d_lits;
  bool d_deleted;
};

using ClauseVector = std::vector<Clause*>;

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__RELEVANCY__CLAUSE_H */

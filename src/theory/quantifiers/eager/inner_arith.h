/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The arithmetic solver of the inner SMT solver.
 *
 * The instances eager E-matching produces are frequently arithmetic, and
 * without arithmetic reasoning the inner solver cannot see most of the
 * conflicts it exists to find. z3 reuses smt::theory_arith for this, which it
 * can do because its instances live in the main solver; ours do not, so this
 * is a separate, retractable solver. See
 * theory/quantifiers/eager/README.md section 6.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__INNER_ARITH_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__INNER_ARITH_H

#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

/**
 * A linear arithmetic solver over the atoms of the instances the inner solver
 * holds, supporting retraction of atoms.
 */
class InnerArith : protected EnvObj
{
 public:
  InnerArith(Env& env);
  ~InnerArith();

  /** Is lit an atom this solver handles? */
  bool isArithAtom(TNode lit) const;
  /**
   * Assert the literal lit. Returns false if the asserted set became
   * infeasible, in which case getConflict describes why.
   */
  bool assertLit(TNode lit);
  /** The reasons of the current conflict */
  const std::vector<Node>& getConflict() const { return d_conflict; }

  /** A checkpoint of the state, used in last-in-first-out order */
  size_t checkpoint() const { return d_asserted.size(); }
  /** Undo everything done since the checkpoint c */
  void restoreTo(size_t c);

  /** The number of asserted atoms */
  size_t getNumAsserted() const { return d_asserted.size(); }

 private:
  /** The asserted literals, in assertion order */
  std::vector<Node> d_asserted;
  /** The reasons of the current conflict */
  std::vector<Node> d_conflict;
  // TODO: a simplex over the asserted atoms with retraction. The tableau can
  // be kept and only the bounds retracted, which is what makes retraction
  // cheap here. See README.md section 9, step 6.
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif

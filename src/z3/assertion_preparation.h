/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The preparation of preprocessed assertions for the ported Z3 core.
 *
 * Not ported from Z3: this is cvc5 integration code, which sequences the
 * ported normalizations in the order Z3's own preprocessing applies them.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__ASSERTION_PREPARATION_H
#define CVC5__Z3__ASSERTION_PREPARATION_H

#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace z3 {

class PropCore;
class SmtContext;

/**
 * The stage between cvc5's preprocessing and the ported core, which
 * establishes the invariants the core inherits from Z3's own preprocessing
 * (asserted_formulas::reduce()) and that cvc5's preprocessing does not. In
 * order, each assertion is converted to negation normal form,
 * naming the quantifiers below atoms, after which each definition introduced
 * by the naming and then the formula itself is rewritten, normalized,
 * rewritten again, put in the form cvc5's theories
 * take, and asserted to the core.
 *
 * This is part of the propositional engine's input conversion, as the CNF
 * conversion is in cvc5's own engine. The definitions it introduces are
 * therefore internal to the core: SmtSolver records the assertions given to
 * apply, not the prepared ones, in the same way that it does not record
 * clauses.
 *
 * The utilities used here belong to the SmtContext, since the core applies
 * them again when it internalizes instances. This class keeps no state, so it
 * never refers to an SmtContext that has been replaced.
 */
class AssertionPreparation : protected EnvObj
{
 public:
  AssertionPreparation(Env& env);
  /**
   * Prepare assertions, in order, with the utilities of ctx, and assert the
   * results to core. The results are also appended to prepared, in order.
   */
  void apply(SmtContext& ctx,
             PropCore& core,
             const std::vector<Node>& assertions,
             std::vector<Node>& prepared);
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__ASSERTION_PREPARATION_H */

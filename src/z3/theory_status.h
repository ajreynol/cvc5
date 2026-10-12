/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * What the theory side of the ported Z3 core knows about whether a
 * satisfying assignment is a model.
 *
 * Not ported from Z3: Z3 has no counterpart, because it either supports a
 * construct or rejects it. This port weakens "sat" to "unknown" instead.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__THEORY_STATUS_H
#define CVC5__Z3__THEORY_STATUS_H

#include <cstdint>
#include <set>
#include <string>

#include "theory/theory_id.h"

namespace cvc5::internal {
namespace z3 {

/**
 * Records the ways in which the theory side reasoned about less than the
 * input says, so that the search driver can tell whether an assignment that
 * satisfies the Boolean abstraction may be reported as a model.
 *
 * Both kinds of record only drop constraints: an "unsat" answer stays sound
 * with them, but a satisfying assignment does not confirm "sat". The records
 * are kept for the life of the SmtContext and are not scoped; see
 * PROP_THEORY_SPLIT.md, section 9.
 */
class TheoryStatus
{
 public:
  /** Record that the input uses a construct the core does not support. */
  void markUnsupported() { d_unsupported = true; }

  bool isUnsupported() const { return d_unsupported; }

  /**
   * Record that theory tid could not reason about some term, or could not
   * confirm that the assignment extends to a model of its fragment.
   */
  void markModelUnsound(theory::TheoryId tid)
  {
    d_modelUnsoundTheories.insert(static_cast<int32_t>(tid));
  }

  bool isModelUnsound() const { return !d_modelUnsoundTheories.empty(); }

  /**
   * Whether an assignment that satisfies the Boolean abstraction can be
   * reported as a model. If not, reason is set to say why.
   */
  bool canConfirmModel(std::string& reason) const;

 private:
  /** true if the input uses a construct that is not supported */
  bool d_unsupported = false;
  /** The theories that could not confirm the assignment extends to a model. */
  std::set<int32_t> d_modelUnsoundTheories;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__THEORY_STATUS_H */

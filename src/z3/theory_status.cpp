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
 * Not ported from Z3.
 */

#include "z3/theory_status.h"

#include <sstream>

namespace cvc5::internal {
namespace z3 {

bool TheoryStatus::canConfirmModel(std::string& reason) const
{
  if (d_unsupported)
  {
    reason = "the input uses a construct the ported core does not support";
    return false;
  }
  if (isModelUnsound())
  {
    // The assignment satisfies the Boolean abstraction, but some theory could
    // not confirm that it extends to a model of its own fragment. Naming the
    // theories is worth the few lines: it is the difference between "no model
    // builder for quantifiers", which is the known cost of leaving MBQI out,
    // and a theory that gave up for a reason worth looking at.
    std::stringstream ss;
    ss << "no model could be built for";
    for (int32_t tid : d_modelUnsoundTheories)
    {
      ss << " " << static_cast<theory::TheoryId>(tid);
    }
    reason = ss.str();
    return false;
  }
  return true;
}

}  // namespace z3
}  // namespace cvc5::internal

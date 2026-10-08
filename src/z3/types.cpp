/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Basic types for the ported Z3 SMT engine.
 */

#include "z3/types.h"

namespace cvc5::internal {
namespace z3 {

std::ostream& operator<<(std::ostream& out, LBool b)
{
  switch (b)
  {
    case L_FALSE: out << "false"; break;
    case L_UNDEF: out << "undef"; break;
    case L_TRUE: out << "true"; break;
  }
  return out;
}

std::ostream& operator<<(std::ostream& out, FinalCheckStatus st)
{
  switch (st)
  {
    case FC_DONE: out << "done"; break;
    case FC_CONTINUE: out << "continue"; break;
    case FC_GIVEUP: out << "giveup"; break;
  }
  return out;
}

}  // namespace z3
}  // namespace cvc5::internal

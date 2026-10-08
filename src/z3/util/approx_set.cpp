/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Approximated sets.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/util/approx_set.cpp, and recast in cvc5 style.
 */

#include "z3/util/approx_set.h"

namespace cvc5::internal {
namespace z3 {

void ApproxSet::print(std::ostream& out) const
{
  out << "{";
  bool first = true;
  for (uint32_t e : *this)
  {
    if (first)
    {
      first = false;
    }
    else
    {
      out << ", ";
    }
    out << e;
  }
  out << "}";
}

std::ostream& operator<<(std::ostream& out, const ApproxSet& s)
{
  s.print(out);
  return out;
}

}  // namespace z3
}  // namespace cvc5::internal

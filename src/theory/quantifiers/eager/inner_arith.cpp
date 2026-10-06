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
 */

#include "theory/quantifiers/eager/inner_arith.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

InnerArith::InnerArith(Env& env) : EnvObj(env) {}

InnerArith::~InnerArith() {}

bool InnerArith::isArithAtom(TNode lit) const
{
  TNode atom = lit.getKind() == Kind::NOT ? lit[0] : lit;
  switch (atom.getKind())
  {
    case Kind::LT:
    case Kind::LEQ:
    case Kind::GT:
    case Kind::GEQ: return true;
    case Kind::EQUAL: return atom[0].getType().isRealOrInt();
    default: return false;
  }
}

bool InnerArith::assertLit(TNode lit)
{
  d_asserted.push_back(lit);
  // TODO: feed the atom to the simplex and report infeasibility.
  return true;
}

void InnerArith::restoreTo(size_t c)
{
  Assert(c <= d_asserted.size());
  d_asserted.resize(c);
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof-like objects for tracking dependencies in the ported Z3 SMT core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_justification.cpp, and recast in cvc5 style.
 */

#include "z3/justification.h"

#include <cstring>
#include <memory>

#include "z3/enode.h"
#include "z3/explainer.h"
#include "z3/smt_context.h"

namespace cvc5::internal {
namespace z3 {

void ExternalEqJustification::getAntecedents(Explainer& e)
{
  e.getContext().noteUnexplainable();
}

UnitResolutionJustification::UnitResolutionJustification(SmtContext& ctx,
                                                         size_t numLits,
                                                         const Literal* lits)
    : d_numLiterals(numLits)
{
  Region& r = ctx.getRegion();
  d_literals = static_cast<Literal*>(r.allocate(sizeof(Literal) * numLits));
  std::memcpy(d_literals, lits, sizeof(Literal) * numLits);
  Assert(d_numLiterals > 0);
}

void UnitResolutionJustification::getAntecedents(Explainer& e)
{
  for (size_t i = 0; i < d_numLiterals; ++i)
  {
    e.markLiteral(d_literals[i]);
  }
}

void EqConflictJustification::getAntecedents(Explainer& e)
{
  Assert(d_node1->getRoot()->isInterpreted());
  Assert(d_node2->getRoot()->isInterpreted());
  e.markEq(d_node1, d_node1->getRoot());
  e.markEq(d_node2, d_node2->getRoot());
  e.markJustifiedEq(d_node1, d_node2, d_js);
}

void EqRootPropagationJustification::getAntecedents(Explainer& e)
{
  e.markEq(d_node, d_node->getRoot());
}

void EqPropagationJustification::getAntecedents(Explainer& e)
{
  if (d_node1 != d_node2)
  {
    e.markEq(d_node1, d_node2);
  }
}

void MpIffJustification::getAntecedents(Explainer& e)
{
  if (d_node1 == d_node2)
  {
    return;
  }
  e.markEq(d_node1, d_node2);
  SmtContext& ctx = e.getContext();
  BoolVar v = ctx.enode2BoolVar(d_node1);
  LBool val = ctx.getAssignment(v);
  Literal l(v, val == L_FALSE);
  e.markLiteral(l);
}

}  // namespace z3
}  // namespace cvc5::internal

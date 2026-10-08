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

#include "z3/conflict_resolution.h"
#include "z3/enode.h"
#include "z3/smt_context.h"

namespace cvc5::internal {
namespace z3 {

UnitResolutionJustification::UnitResolutionJustification(SmtContext& ctx,
                                                         Justification* js,
                                                         size_t numLits,
                                                         const Literal* lits)
    : d_antecedent(js), d_numLiterals(numLits)
{
  Assert(js == nullptr || js->inRegion());
  Region& r = ctx.getRegion();
  d_literals = static_cast<Literal*>(r.allocate(sizeof(Literal) * numLits));
  std::memcpy(d_literals, lits, sizeof(Literal) * numLits);
  Assert(d_numLiterals > 0);
}

UnitResolutionJustification::UnitResolutionJustification(Justification* js,
                                                         size_t numLits,
                                                         const Literal* lits)
    : Justification(false),  // the object is not allocated in a region
      d_antecedent(js),
      d_numLiterals(numLits)
{
  Assert(js == nullptr || !js->inRegion());
  d_literals = new Literal[numLits];
  std::memcpy(d_literals, lits, sizeof(Literal) * numLits);
  Assert(numLits != 0);
}

UnitResolutionJustification::~UnitResolutionJustification()
{
  if (!inRegion())
  {
    delete[] d_literals;
    delete d_antecedent;
  }
}

void UnitResolutionJustification::getAntecedents(ConflictResolution& cr)
{
  if (d_antecedent != nullptr)
  {
    cr.markJustification(d_antecedent);
  }
  for (size_t i = 0; i < d_numLiterals; ++i)
  {
    cr.markLiteral(d_literals[i]);
  }
}

void EqConflictJustification::getAntecedents(ConflictResolution& cr)
{
  Assert(d_node1->getRoot()->isInterpreted());
  Assert(d_node2->getRoot()->isInterpreted());
  cr.markEq(d_node1, d_node1->getRoot());
  cr.markEq(d_node2, d_node2->getRoot());
  cr.markJustifiedEq(d_node1, d_node2, d_js);
}

void EqRootPropagationJustification::getAntecedents(ConflictResolution& cr)
{
  cr.markEq(d_node, d_node->getRoot());
}

void EqPropagationJustification::getAntecedents(ConflictResolution& cr)
{
  if (d_node1 != d_node2)
  {
    cr.markEq(d_node1, d_node2);
  }
}

void MpIffJustification::getAntecedents(ConflictResolution& cr)
{
  if (d_node1 == d_node2)
  {
    return;
  }
  cr.markEq(d_node1, d_node2);
  SmtContext& ctx = cr.getContext();
  BoolVar v = ctx.enode2BoolVar(d_node1);
  LBool val = ctx.getAssignment(v);
  Literal l(v, val == L_FALSE);
  cr.markLiteral(l);
}

SimpleJustification::SimpleJustification(SmtContext& ctx,
                                         size_t numLits,
                                         const Literal* lits)
    : d_numLiterals(numLits), d_literals(nullptr)
{
  Region& r = ctx.getRegion();
  if (numLits != 0)
  {
    d_literals = static_cast<Literal*>(r.allocate(sizeof(Literal) * numLits));
    std::memcpy(d_literals, lits, sizeof(Literal) * numLits);
#ifdef CVC5_ASSERTIONS
    for (size_t i = 0; i < numLits; ++i)
    {
      Assert(lits[i] != s_nullLiteral);
    }
#endif
  }
}

void SimpleJustification::getAntecedents(ConflictResolution& cr)
{
  for (size_t i = 0; i < d_numLiterals; ++i)
  {
    cr.markLiteral(d_literals[i]);
  }
}

ExtSimpleJustification::ExtSimpleJustification(SmtContext& ctx,
                                               size_t numLits,
                                               const Literal* lits,
                                               size_t numEqs,
                                               const ENodePair* eqs)
    : SimpleJustification(ctx, numLits, lits), d_numEqs(numEqs), d_eqs(nullptr)
{
  Region& r = ctx.getRegion();
  if (numEqs != 0)
  {
    d_eqs = static_cast<ENodePair*>(r.allocate(sizeof(ENodePair) * numEqs));
    std::uninitialized_copy(eqs, eqs + numEqs, d_eqs);
#ifdef CVC5_ASSERTIONS
    for (size_t i = 0; i < numEqs; ++i)
    {
      Assert(eqs[i].first->getRoot() == eqs[i].second->getRoot());
    }
#endif
  }
}

void ExtSimpleJustification::getAntecedents(ConflictResolution& cr)
{
  SimpleJustification::getAntecedents(cr);
  for (size_t i = 0; i < d_numEqs; ++i)
  {
    cr.markEq(d_eqs[i].first, d_eqs[i].second);
  }
}

}  // namespace z3
}  // namespace cvc5::internal

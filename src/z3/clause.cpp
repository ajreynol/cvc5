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
 * file src/smt/smt_clause.cpp, and recast in cvc5 style.
 */

#include "z3/clause.h"

#include <cstring>

#include "z3/justification.h"

namespace cvc5::internal {
namespace z3 {

Clause* Clause::mk(size_t numLits,
                   Literal* lits,
                   ClauseKind k,
                   Justification* js,
                   ClauseDelEh* delEh,
                   bool saveAtoms,
                   const std::vector<Node>* boolVar2Expr)
{
  Assert(z3::isAxiom(k) || js == nullptr || !js->inRegion());
  Assert(numLits >= 2);
  size_t sz =
      getObjSize(numLits, k, saveAtoms, delEh != nullptr, js != nullptr);
  void* mem = ::operator new(sz);
  Clause* cls = new (mem) Clause();
  cls->d_numLiterals = static_cast<uint32_t>(numLits);
  cls->d_capacity = static_cast<uint32_t>(numLits);
  cls->d_kind = k;
  cls->d_reinit = saveAtoms;
  cls->d_reinternalizeAtoms = saveAtoms;
  cls->d_hasAtoms = saveAtoms;
  cls->d_hasDelEh = delEh != nullptr;
  cls->d_hasJustification = js != nullptr;
  cls->d_deleted = false;
  std::memcpy(cls->litsPtr(), lits, sizeof(Literal) * numLits);
  if (cls->isLemma())
  {
    cls->setActivity(1);
  }
  if (delEh != nullptr)
  {
    *(const_cast<ClauseDelEh**>(cls->getDelEhAddr())) = delEh;
  }
  if (js != nullptr)
  {
    *(const_cast<Justification**>(cls->getJustificationAddr())) = js;
  }
  if (saveAtoms)
  {
    Assert(boolVar2Expr != nullptr);
    AtomEntry* atoms = cls->getAtomsAddr();
    for (size_t i = 0; i < numLits; ++i)
    {
      // The Node is constructed in place; releaseAtoms and deallocate run the
      // matching destructor.
      new (&atoms[i]) AtomEntry{(*boolVar2Expr)[lits[i].var()],
                                lits[i].sign()};
    }
  }
  return cls;
}

void Clause::releaseAtoms()
{
  size_t numAtoms = getNumAtoms();
  AtomEntry* atoms = getAtomsAddr();
  for (size_t i = 0; i < numAtoms; ++i)
  {
    atoms[i].~AtomEntry();
    // leave the slot destroyed; d_reinternalizeAtoms is cleared by the caller
  }
}

void Clause::deallocate()
{
  ClauseDelEh* delEh = getDelEh();
  if (delEh != nullptr)
  {
    (*delEh)(this);
  }
  if (isLemma() && d_hasJustification)
  {
    Justification* js = getJustification();
    if (js != nullptr)
    {
      Assert(!js->inRegion());
      js->delEh();
      delete js;
    }
  }
  if (d_reinternalizeAtoms)
  {
    releaseAtoms();
  }
  this->~Clause();
  ::operator delete(static_cast<void*>(this));
}

std::ostream& Clause::print(std::ostream& out,
                            const std::vector<Node>& boolVar2Expr) const
{
  out << "(clause";
  for (size_t i = 0; i < d_numLiterals; ++i)
  {
    Literal l = litsPtr()[i];
    out << " ";
    if (l.sign())
    {
      out << "(not ";
    }
    if (l.var() < boolVar2Expr.size())
    {
      out << boolVar2Expr[l.var()];
    }
    else
    {
      out << "p" << l.var();
    }
    if (l.sign())
    {
      out << ")";
    }
  }
  return out << ")";
}

}  // namespace z3
}  // namespace cvc5::internal

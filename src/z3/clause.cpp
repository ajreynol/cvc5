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
#include <new>

namespace cvc5::internal {
namespace z3 {

Clause* Clause::mk(size_t numLits, Literal* lits, Justification* js)
{
  Assert(numLits >= 2);
  size_t sz = align(sizeof(Clause) + sizeof(Literal) * numLits);
  if (js != nullptr)
  {
    sz += sizeof(Justification*);
  }
  void* mem = ::operator new(sz);
  Clause* cls = new (mem) Clause();
  cls->d_numLiterals = static_cast<uint32_t>(numLits);
  cls->d_hasJustification = js != nullptr;
  cls->d_deleted = false;
  std::memcpy(cls->litsPtr(), lits, sizeof(Literal) * numLits);
  if (js != nullptr)
  {
    *(const_cast<Justification**>(cls->getJustificationAddr())) = js;
  }
  return cls;
}

void Clause::deallocate()
{
  this->~Clause();
  ::operator delete(static_cast<void*>(this));
}

}  // namespace z3
}  // namespace cvc5::internal

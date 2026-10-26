/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The congruence table.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_cg_table.cpp, and recast in cvc5 style.
 */

#include "z3/quantifiers/cg_table.h"

#include "util/hash.h"

namespace cvc5::internal {
namespace z3 {

size_t CgTable::Hash::operator()(ENode* n) const
{
  uint64_t h = fnv1a::fnv1a_64(std::hash<TNode>()(n->getDecl()));
  if (n->isCommutative())
  {
    // the argument order does not matter
    size_t h1 = n->getArg(0)->getRoot()->hash();
    size_t h2 = n->getArg(1)->getRoot()->hash();
    if (h1 > h2)
    {
      std::swap(h1, h2);
    }
    return fnv1a::fnv1a_64(h2, fnv1a::fnv1a_64(h1, h));
  }
  for (uint32_t i = 0, num = n->getNumArgs(); i < num; ++i)
  {
    h = fnv1a::fnv1a_64(n->getArg(i)->getRoot()->hash(), h);
  }
  return h;
}

}  // namespace z3
}  // namespace cvc5::internal

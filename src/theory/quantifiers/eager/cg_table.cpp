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
 * Ported from Z3: src/smt/smt_cg_table.cpp.
 * Z3 is Copyright (c) Microsoft Corporation and licensed under the MIT
 * License, see licenses/z3-LICENSE.
 */

#include "theory/quantifiers/eager/cg_table.h"

#include "util/hash.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

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

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Enumerative quantifier instantiation.
 */

#include "z3/enum_inst.h"

#include "base/output.h"
#include "z3/ast.h"
#include "z3/enode.h"
#include "z3/smt_context.h"
#include "z3/util/util.h"

namespace cvc5::internal {
namespace z3 {

EnumInst::EnumInst(SmtContext& ctx, size_t maxPerRound)
    : d_context(ctx), d_checker(ctx), d_maxPerRound(maxPerRound), d_qIdx(0)
{
  // The assignment is completed to a total model, so that a falsified
  // binding can actually be found; see QuickChecker::setTotal.
  d_checker.setTotal(true);
}

bool EnumInst::instantiate(const std::vector<Node>& quantifiers)
{
  if (quantifiers.empty())
  {
    return false;
  }
  // The quantifiers are visited round-robin and only a bounded number of
  // instances is added per final check: adding one for every quantifier at
  // once buries the search in instances that are never used.
  size_t added = 0;
  size_t n = quantifiers.size();
  if (d_qIdx >= n)
  {
    d_qIdx = 0;
  }
  for (size_t i = 0; i < n && added < d_maxPerRound; ++i)
  {
    if (d_context.getCancelFlag() || d_context.inconsistent())
    {
      break;
    }
    size_t idx = (d_qIdx + i) % n;
    TNode q = quantifiers[idx];
    if (!d_context.isRelevant(q) || d_context.getAssignment(q) != L_TRUE)
    {
      continue;
    }
    if (d_checker.instantiateFirstNew(q))
    {
      added++;
      d_qIdx = (idx + 1) % n;
    }
  }
  Trace("z3-enum") << "enum-inst: added " << added << " of "
                   << quantifiers.size() << " quantifiers" << std::endl;
  return added > 0;
}

}  // namespace z3
}  // namespace cvc5::internal

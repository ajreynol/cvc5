/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Per-quantifier statistics.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/ast/quantifier_stat.cpp, and recast in cvc5 style.
 */

#include "z3/quantifier_stat.h"

#include "z3/ast.h"

namespace cvc5::internal {
namespace z3 {

namespace {
/** Saturating multiply, standing in for Z3's approx_nat. */
constexpr uint64_t s_approxNatMax = UINT64_MAX;

void approxMul(uint64_t& v, uint64_t by)
{
  if (v == s_approxNatMax || by == 0)
  {
    return;
  }
  if (by != 0 && v > s_approxNatMax / by)
  {
    v = s_approxNatMax;
  }
  else
  {
    v *= by;
  }
}
}  // namespace

QuantifierStat::QuantifierStat(uint32_t generation)
    : d_size(0),
      d_depth(0),
      d_generation(generation),
      d_caseSplitFactor(1),
      d_numNestedQuantifiers(0),
      d_numInstances(0),
      d_numInstancesCheckerSat(0),
      d_numInstancesSimplifyTrue(0),
      d_numInstancesCurrSearch(0),
      d_numInstancesCurrBranch(0),
      d_maxGeneration(0),
      d_maxCost(0.0f)
{
}

QuantifierStatGen::QuantifierStatGen(Region& r)
    : d_region(r), d_caseSplitFactor(1)
{
}

void QuantifierStatGen::reset()
{
  d_alreadyFound.clear();
  d_todo.clear();
  d_caseSplitFactor = 1;
}

QuantifierStat* QuantifierStatGen::operator()(TNode q, uint32_t generation)
{
  reset();
  QuantifierStat* r = new (d_region) QuantifierStat(generation);
  d_todo.push_back(Entry(getQuantBody(q)));
  while (!d_todo.empty())
  {
    Entry e = d_todo.back();
    Node n = e.d_expr;
    uint32_t depth = e.d_depth;
    bool depthOnly = e.d_depthOnly != 0;
    d_todo.pop_back();
    auto it = d_alreadyFound.find(n);
    if (it != d_alreadyFound.end())
    {
      if (it->second >= depth)
      {
        continue;
      }
      depthOnly = true;
    }
    d_alreadyFound[n] = depth;
    if (depth >= r->d_depth)
    {
      r->d_depth = depth;
    }
    if (!depthOnly)
    {
      r->d_size++;
      if (isQuantifier(n))
      {
        r->d_numNestedQuantifiers++;
      }
      size_t numArgs = n.getNumChildren();
      // Remark from Z3: the case split factor is an approximation, and the
      // contribution of the theories is ignored.
      switch (n.getKind())
      {
        case Kind::OR:
          approxMul(d_caseSplitFactor, depth == 0 ? numArgs : numArgs + 1);
          break;
        case Kind::AND:
          if (depth > 0)
          {
            approxMul(d_caseSplitFactor, numArgs + 1);
          }
          break;
        case Kind::EQUAL:
          if (n[0].getType().isBoolean())
          {
            approxMul(d_caseSplitFactor, depth == 0 ? 4 : 9);
          }
          break;
        case Kind::ITE: approxMul(d_caseSplitFactor, depth == 0 ? 4 : 9); break;
        default: break;
      }
    }
    if (isApp(n))
    {
      size_t j = n.getNumChildren();
      while (j > 0)
      {
        --j;
        d_todo.push_back(Entry(n[j], depth + 1, depthOnly));
      }
    }
  }
  r->d_caseSplitFactor = d_caseSplitFactor > UINT32_MAX
                             ? UINT32_MAX
                             : static_cast<uint32_t>(d_caseSplitFactor);
  return r;
}

}  // namespace z3
}  // namespace cvc5::internal

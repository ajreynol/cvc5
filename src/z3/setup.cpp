/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Configuration of the ported Z3 core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), files
 * src/smt/smt_setup.cpp and src/params/smt_params.cpp, recast in cvc5 style.
 */

#include "z3/setup.h"

#include "expr/node_manager.h"
#include "theory/logic_info.h"
#include "theory/theory.h"
#include "z3/theory_cvc5.h"
#include "z3/theory_datatype.h"

namespace cvc5::internal {
namespace z3 {

void StaticFeatures::collect(const std::vector<Node>& fmls)
{
  std::unordered_set<Node> visited;
  for (const Node& f : fmls)
  {
    collect(f, visited);
  }
}

void StaticFeatures::collect(TNode n, std::unordered_set<Node>& visited)
{
  std::vector<Node> todo{n};
  while (!todo.empty())
  {
    Node cur = todo.back();
    todo.pop_back();
    if (!visited.insert(cur).second)
    {
      continue;
    }
    if (isQuantifier(cur))
    {
      d_numQuantifiers++;
      if (hasPatterns(cur))
      {
        d_numQuantifiersWithPatterns++;
      }
      todo.push_back(getQuantBody(cur));
      continue;
    }
    TypeNode tn = cur.getType();
    if (tn.isInteger())
    {
      d_hasInt = true;
    }
    else if (tn.isReal())
    {
      d_hasReal = true;
    }
    else if (tn.isBitVector())
    {
      d_hasBv = true;
    }
    else if (tn.isArray())
    {
      d_hasArrays = true;
    }
    else if (tn.isDatatype())
    {
      d_hasDatatypes = true;
    }
    else if (tn.isStringLike())
    {
      d_hasStrings = true;
    }
    else if (tn.isFloatingPoint())
    {
      d_hasFp = true;
    }
    switch (cur.getKind())
    {
      case Kind::APPLY_UF: d_hasUf = true; break;
      case Kind::NONLINEAR_MULT: d_numNonLinear++; break;
      case Kind::MULT:
      {
        // a product of two non-constant terms is nonlinear
        size_t nonConst = 0;
        for (const Node& c : cur)
        {
          if (!c.isConst())
          {
            nonConst++;
          }
        }
        if (nonConst > 1)
        {
          d_numNonLinear++;
        }
        break;
      }
      case Kind::DIVISION:
      case Kind::INTS_DIVISION:
      case Kind::INTS_MODULUS:
      case Kind::POW:
      case Kind::POW2: d_numNonLinear++; break;
      default: break;
    }
    if (cur.getNumChildren() == 0 && cur.isVar() && tn.isUninterpretedSort())
    {
      d_hasUf = true;
    }
    for (const Node& c : cur)
    {
      todo.push_back(c);
    }
  }
}

Setup::Setup(SmtContext& ctx, Params& p) : d_ctx(ctx), d_params(p) {}

void Setup::operator()(ConfigMode cm)
{
  switch (cm)
  {
    case CFG_BASIC: setupUnknown(); break;
    case CFG_LOGIC: setupDefault(); break;
    case CFG_AUTO: setupAutoConfig(); break;
  }
}

void Setup::setupDefault()
{
  // None of the logics in scope here (UFBVDTLIA, UFBVDTNIA, ALL and the
  // other quantified combinations) appear in Z3's per-logic table, so Z3
  // itself falls through to setupUnknown for them.
  setupUnknown();
}

void Setup::setupAutoConfig()
{
  StaticFeatures st;
  std::vector<Node> fmls;
  for (size_t i = 0, n = d_ctx.getNumAssertedFormulas(); i < n; ++i)
  {
    fmls.push_back(d_ctx.getAssertedFormula(i));
  }
  st.collect(fmls);
  setupUnknown(st);
}

void Setup::setupUnknown()
{
  StaticFeatures st;
  std::vector<Node> fmls;
  for (size_t i = 0, n = d_ctx.getNumAssertedFormulas(); i < n; ++i)
  {
    fmls.push_back(d_ctx.getAssertedFormula(i));
  }
  st.collect(fmls);
  setupArith();
  setupBv();
  setupDatatypes();
  setupRelevancy(st);
}

void Setup::setupUnknown(const StaticFeatures& st)
{
  if (st.d_numQuantifiers > 0)
  {
    if (st.d_hasReal)
    {
      setupAuflira(false);
    }
    else
    {
      setupAuflia(false);
      setupAuflia(st);
    }
    setupDatatypes();
    setupBv();
    return;
  }

  if (!st.d_hasBv && !st.d_hasInt && !st.d_hasReal && !st.d_hasArrays
      && !st.d_hasDatatypes && !st.d_hasStrings && !st.d_hasFp)
  {
    // a pure equality and uninterpreted function problem
    setupQfUf();
    return;
  }

  setupUnknown();
}

void Setup::setupRelevancy(const StaticFeatures& st)
{
  // Quantifier free bit-vector problems should always run with relevancy
  // disabled; there are other cases where relevancy propagation hurts.
  //
  // The case split queue has already been built, so it is not safe to
  // disable relevancy when the strategy depends on it.
  if (d_params.d_caseSplitStrategy == CS_RELEVANCY
      || d_params.d_caseSplitStrategy == CS_RELEVANCY_ACTIVITY
      || d_params.d_caseSplitStrategy == CS_RELEVANCY_GOAL)
  {
    return;
  }

  if (st.d_hasBv && st.d_numQuantifiers == 0)
  {
    d_params.d_relevancyLvl = 0;
  }
}

void Setup::setupQfUf()
{
  d_params.d_relevancyLvl = 0;
  d_params.d_restartStrategy = RS_LUBY;
  d_params.d_phaseSelection = PS_CACHING_CONSERVATIVE2;
  d_params.d_randomInitialActivity = IA_RANDOM;
}

void Setup::setupAuflia(bool /*simpleArray*/)
{
  d_params.d_phaseSelection = PS_ALWAYS_FALSE;
  d_params.d_restartStrategy = RS_GEOMETRIC;
  d_params.d_restartFactor = 1.5;
  d_params.d_qiQuickChecker = MC_UNSAT;
  d_params.d_qiLazyThreshold = 20;
  // Z3 enables model based instantiation by default here.
  d_params.d_mbqi = true;
  setupArith();
}

void Setup::setupAuflia(const StaticFeatures& st)
{
  d_params.d_qiEagerThreshold = st.d_numQuantifiersWithPatterns == 0 ? 5 : 7;
}

void Setup::setupAuflira(bool /*simpleArray*/)
{
  d_params.d_phaseSelection = PS_ALWAYS_FALSE;
  d_params.d_qiQuickChecker = MC_UNSAT;
  d_params.d_qiEagerThreshold = 5;
  d_params.d_qiLazyThreshold = 20;
  d_params.d_mbqi = true;
  setupArith();
}

void Setup::setupArith()
{
  if (d_ctx.getTheory(theory::THEORY_ARITH) != nullptr)
  {
    return;
  }
  Theory* th = mkTheoryArithBridge(d_ctx);
  if (th != nullptr)
  {
    d_ctx.registerPlugin(th);
  }
}

void Setup::setupBv()
{
  if (d_ctx.getTheory(theory::THEORY_BV) != nullptr)
  {
    return;
  }
  Theory* th = mkTheoryBvBridge(d_ctx);
  if (th != nullptr)
  {
    d_ctx.registerPlugin(th);
  }
}

void Setup::setupDatatypes()
{
  if (d_ctx.getTheory(theory::THEORY_DATATYPES) != nullptr)
  {
    return;
  }
  d_ctx.registerPlugin(mkTheoryDatatype(d_ctx));
}

void SmtContext::setupContext(bool useStaticFeatures)
{
  if (d_setupDone || inconsistent())
  {
    d_relevancyLvl = std::min(d_params.d_relevancyLvl, d_relevancyLvl);
    return;
  }
  d_setupDone = true;
  Setup setup(*this, d_params);
  setup(getConfigMode(useStaticFeatures));
  d_relevancyLvl = d_params.d_relevancyLvl;
  setupComponents();
}

}  // namespace z3
}  // namespace cvc5::internal

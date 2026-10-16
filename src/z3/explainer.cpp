/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The explanation of justifications and equalities as literals.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), the
 * explanation half of file src/smt/smt_conflict_resolution.cpp, and recast in
 * cvc5 style.
 */

#include "z3/explainer.h"

namespace cvc5::internal {
namespace z3 {

Explainer::Explainer(SmtContext& ctx)
    : d_ctx(ctx), d_todoJsQhead(0), d_antecedents(nullptr)
{
}

template <bool Set>
void Explainer::markENodesInTrans(ENode* n)
{
  while (n != nullptr)
  {
    if (Set)
    {
      n->setMark2();
    }
    else
    {
      n->unsetMark2();
    }
    n = n->d_trans.d_target;
  }
}

ENode* Explainer::findCommonAncestor(ENode* n1, ENode* n2)
{
  // Find a common ancestor of n1 and n2 in the proof forest, so that the
  // shared suffix up to the root is left out of the transitivity proof:
  //
  //   n1 = a1 = ... = ai = ANC = ... = root
  //   n2 = b1 = ... = bj = ANC = ... = root
  //
  // giving the irredundant proof n1 = a1 = ... = ai = ANC = bj = ... = n2.
  Assert(n1->getRoot() == n2->getRoot());
  markENodesInTrans<true>(n1);
  while (true)
  {
    Assert(n2 != nullptr);
    if (n2->isMarked2())
    {
      markENodesInTrans<false>(n1);
      return n2;
    }
    n2 = n2->d_trans.d_target;
  }
}

void Explainer::eqJustification2Literals(ENode* lhs,
                                         ENode* rhs,
                                         EqJustification js)
{
  Assert(d_antecedents != nullptr);
  switch (js.getKind())
  {
    case EqJustification::AXIOM: break;
    case EqJustification::EQUATION:
      d_antecedents->push_back(js.getLiteral());
      break;
    case EqJustification::JUSTIFICATION:
      markJustification(js.getJustification());
      break;
    case EqJustification::CONGRUENCE:
    {
      uint32_t numArgs = lhs->getNumArgs();
      Assert(numArgs == rhs->getNumArgs());
      if (js.usedCommutativity())
      {
        Assert(numArgs == 2);
        markEq(lhs->getArg(0), rhs->getArg(1));
        markEq(lhs->getArg(1), rhs->getArg(0));
      }
      else
      {
        for (uint32_t i = 0; i < numArgs; ++i)
        {
          markEq(lhs->getArg(i), rhs->getArg(i));
        }
      }
      break;
    }
  }
}

void Explainer::eqBranch2Literals(ENode* n1, ENode* n2)
{
  while (n1 != n2)
  {
    eqJustification2Literals(
        n1, n1->d_trans.d_target, n1->d_trans.d_justification);
    n1 = n1->d_trans.d_target;
  }
}

void Explainer::eq2Literals(ENode* n1, ENode* n2)
{
  ENode* c = findCommonAncestor(n1, n2);
  eqBranch2Literals(n1, c);
  eqBranch2Literals(n2, c);
}

void Explainer::explain(Justification* js, LiteralVector& result)
{
  Assert(d_todoJsQhead <= d_todoJs.size());
  d_antecedents = &result;
  markJustification(js);
  processJustifications();
}

void Explainer::processJustifications()
{
  while (true)
  {
    size_t sz = d_todoJs.size();
    while (d_todoJsQhead < sz)
    {
      Justification* js = d_todoJs[d_todoJsQhead];
      d_todoJsQhead++;
      js->getAntecedents(*this);
    }
    while (!d_todoEqs.empty())
    {
      ENodePair p = d_todoEqs.back();
      d_todoEqs.pop_back();
      eq2Literals(p.first, p.second);
    }
    if (d_todoJsQhead == d_todoJs.size())
    {
      d_antecedents = nullptr;
      return;
    }
  }
}

void Explainer::rollback(size_t checkpoint)
{
  Assert(checkpoint <= d_todoJs.size());
  for (size_t i = checkpoint, sz = d_todoJs.size(); i < sz; ++i)
  {
    d_todoJs[i]->unsetMark();
  }
  d_todoJs.resize(checkpoint);
  d_todoJsQhead = checkpoint;
  d_todoEqs.clear();
  d_alreadyProcessedEqs.clear();
}

}  // namespace z3
}  // namespace cvc5::internal

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory plugin interface of the ported Z3 SMT core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_theory.cpp, and recast in cvc5 style.
 */

#include "z3/theory.h"

#include "expr/node_manager.h"
#include "z3/smt_context.h"

namespace cvc5::internal {
namespace z3 {

Theory::Theory(SmtContext& ctx, TheoryId fid)
    : d_id(fid), d_ctx(ctx), d_lazyScopes(0), d_lazy(true)
{
}

const Params& Theory::getParams() const { return d_ctx.getParams(); }

void Theory::resetEh() { d_var2ENode.clear(); }

void Theory::pushScopeEh() { d_var2ENodeLim.push_back(d_var2ENode.size()); }

void Theory::popScopeEh(size_t numScopes)
{
  size_t scopeLvl = d_var2ENodeLim.size();
  Assert(numScopes <= scopeLvl);
  size_t newLvl = scopeLvl - numScopes;
  size_t oldSz = d_var2ENodeLim[newLvl];
  d_var2ENode.resize(oldSz);
  d_var2ENodeLim.resize(newLvl);
}

bool Theory::lazyPush()
{
  if (d_lazy)
  {
    ++d_lazyScopes;
  }
  return d_lazy;
}

bool Theory::lazyPop(size_t& numScopes)
{
  size_t n = std::min(numScopes, d_lazyScopes);
  numScopes -= n;
  d_lazyScopes -= n;
  return numScopes == 0;
}

void Theory::forcePush()
{
  bool saved = d_lazy;
  d_lazy = false;
  for (; d_lazyScopes > 0; --d_lazyScopes)
  {
    pushScopeEh();
  }
  d_lazy = saved;
}

void Theory::printVar2ENode(std::ostream& out) const
{
  size_t sz = d_var2ENode.size();
  for (size_t v = 0; v < sz; ++v)
  {
    out << "v" << v << " -> #" << d_var2ENode[v]->getOwnerId() << "\n";
  }
}

bool Theory::isRelevantAndShared(ENode* n) const
{
  return d_ctx.isRelevant(n) && d_ctx.isShared(n);
}

bool Theory::assumeEq(ENode* n1, ENode* n2) { return d_ctx.assumeEq(n1, n2); }

Node Theory::mkEqAtom(TNode lhs, TNode rhs)
{
  NodeManager* nm = lhs.getNodeManager();
  if (lhs.getId() > rhs.getId())
  {
    std::swap(lhs, rhs);
  }
  if (lhs == rhs)
  {
    return nm->mkConst(true);
  }
  if (lhs.isConst() && rhs.isConst())
  {
    // distinct constants of the same type are distinct
    return nm->mkConst(false);
  }
  return nm->mkNode(Kind::EQUAL, lhs, rhs);
}

Literal Theory::mkEq(TNode a, TNode b, bool gateCtx)
{
  if (a == b)
  {
    return s_trueLiteral;
  }
  if (a.isConst() && b.isConst())
  {
    return s_falseLiteral;
  }
  Node eq = d_ctx.mkEqAtom(a, b);
  d_ctx.internalize(eq, gateCtx);
  return d_ctx.getLiteral(eq);
}

Literal Theory::mkPreferredEq(TNode a, TNode b)
{
  d_ctx.assumeEq(ensureENode(a), ensureENode(b));
  Literal lit = mkEq(a, b, false);
  d_ctx.forcePhase(lit);
  return lit;
}

Literal Theory::mkLiteral(TNode e)
{
  TNode atom = e;
  bool isNot = e.getKind() == Kind::NOT;
  if (isNot)
  {
    atom = e[0];
  }
  if (!d_ctx.eInternalized(atom))
  {
    ENode* n = d_ctx.nonGroundInternalize(atom);
    atom = n->getExpr();
  }
  Literal lit = d_ctx.getLiteral(atom);
  d_ctx.markAsRelevant(lit);
  if (isNot)
  {
    lit.neg();
  }
  return lit;
}

ENode* Theory::ensureENode(TNode e)
{
  if (!d_ctx.eInternalized(e))
  {
    d_ctx.internalize(e, isQuantifier(e));
  }
  // make sure theory variables are attached
  d_ctx.ensureInternalized(e);
  ENode* n = d_ctx.getENode(e);
  d_ctx.markAsRelevant(n);
  return n;
}

TheoryVar Theory::getThVar(TNode e) const
{
  return getThVar(d_ctx.getENode(e));
}

}  // namespace z3
}  // namespace cvc5::internal

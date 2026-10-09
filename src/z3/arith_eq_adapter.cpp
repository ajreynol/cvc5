/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Converting the (dis)equalities the core propagates into arithmetic atoms.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), file
 * src/smt/arith_eq_adapter.cpp, and recast in cvc5 style.
 */

#include "z3/arith_eq_adapter.h"

#include "expr/node_manager.h"
#include "util/rational.h"
#include "z3/params.h"
#include "z3/relevancy.h"
#include "z3/smt_context.h"
#include "z3/theory.h"
#include "z3/util/trail.h"

namespace cvc5::internal {
namespace z3 {

namespace {

/**
 * Undoes the insertion of a processed pair. A trail object rather than a
 * local stack, because it guarantees that the enodes are still alive when
 * the undo runs.
 */
class AlreadyProcessedTrail : public Trail
{
 public:
  AlreadyProcessedTrail(ArithEqAdapter::AlreadyProcessed& m,
                        ENode* n1,
                        ENode* n2)
      : d_alreadyProcessed(m), d_n1(n1), d_n2(n2)
  {
  }

  void undo() override { d_alreadyProcessed.erase({d_n1, d_n2}); }

 private:
  ArithEqAdapter::AlreadyProcessed& d_alreadyProcessed;
  ENode* d_n1;
  ENode* d_n2;
};

/**
 * The atoms eq, le and ge should be marked as relevant only after n1 and n2
 * are marked as relevant.
 */
class ArithEqRelevancyEh : public RelevancyEh
{
 public:
  ArithEqRelevancyEh(TNode n1, TNode n2, TNode eq, TNode le, TNode ge)
      : d_n1(n1), d_n2(n2), d_eq(eq), d_le(le), d_ge(ge)
  {
  }

  void operator()(RelevancyPropagator& rp) override
  {
    if (!rp.isRelevant(d_n1))
    {
      return;
    }
    if (!rp.isRelevant(d_n2))
    {
      return;
    }
    rp.markAsRelevant(d_eq);
    rp.markAsRelevant(d_le);
    rp.markAsRelevant(d_ge);
  }

 private:
  TNode d_n1;
  TNode d_n2;
  TNode d_eq;
  TNode d_le;
  TNode d_ge;
};

}  // namespace

ArithEqAdapter::ArithEqAdapter(Theory& owner) : d_owner(owner) {}

SmtContext& ArithEqAdapter::getContext() const { return d_owner.getContext(); }

void ArithEqAdapter::mkAxioms(ENode* n1, ENode* n2)
{
  SmtContext& ctx = getContext();
  if (n1 == n2)
  {
    return;
  }
  if (n1->getOwnerId() > n2->getOwnerId())
  {
    std::swap(n1, n2);
  }
  Node t1 = n1->getExpr();
  Node t2 = n2->getExpr();
  NodeManager* nm = t1.getNodeManager();
  if (t1.isConst() && t2.isConst())
  {
    if (t1 != t2)
    {
      // m.are_distinct(t1, t2): two different values
      Node eq = ctx.mkEqAtom(t1, t2);
      d_keepAlive.push_back(eq);
      ctx.internalize(eq, true);
      Literal lit(ctx.getBoolVar(eq));
      ctx.assign(~lit, static_cast<Justification*>(nullptr), false);
    }
    // We don't need to create axioms for 2 = 3 or 2 = 2.
    return;
  }
  if (t1 == t2)
  {
    return;
  }

  // The atoms d_t1EqT2, d_le, and d_ge should only be marked as relevant
  // after n1 and n2 are marked as relevant.
  if (d_alreadyProcessed.find({n1, n2}) != d_alreadyProcessed.end())
  {
    return;
  }

  d_stats.d_numEqAxioms++;

  Node t1EqT2 = ctx.mkEqAtom(t1, t2);
  Assert(!(t1EqT2.isConst() && !t1EqT2.getConst<bool>()));

  // Requires that the arithmetic internalizer accept non simplified terms of
  // the form t1 - t2 if t1 and t2 already have slacks (theory variables)
  // associated with them. It also accepts terms with repeated variables.
  Node le;
  Node ge;
  if (t1.isConst())
  {
    std::swap(t1, t2);
  }
  if (t2.isConst())
  {
    le = nm->mkNode(Kind::LEQ, t1, t2);
    ge = nm->mkNode(Kind::GEQ, t1, t2);
  }
  else
  {
    TypeNode st = t1.getType();
    Node minusOne = nm->mkConstRealOrInt(st, Rational(-1));
    Node zero = nm->mkConstRealOrInt(st, Rational(0));
    Node t3 = nm->mkNode(Kind::MULT, minusOne, t2);
    Node s = nm->mkNode(Kind::ADD, t1, t3);
    le = nm->mkNode(Kind::LEQ, s, zero);
    ge = nm->mkNode(Kind::GEQ, s, zero);
  }
  d_keepAlive.push_back(t1EqT2);
  d_keepAlive.push_back(le);
  d_keepAlive.push_back(ge);

  ctx.pushTrail(AlreadyProcessedTrail(d_alreadyProcessed, n1, n2));
  d_alreadyProcessed[{n1, n2}] = Data{t1EqT2, le, ge};
  ctx.internalize(t1EqT2, true);
  Literal t1EqT2Lit(ctx.getBoolVar(t1EqT2));
  ctx.internalize(le, true);
  ctx.internalize(ge, true);
  Literal leLit = ctx.getLiteral(le);
  Literal geLit = ctx.getLiteral(ge);
  if (ctx.tryTrueFirst(t1EqT2Lit.var()))
  {
    // The try_true_first flag is propagated to the auxiliary atoms too.
    // Otherwise model based theory combination would be ineffective: if the
    // core case split on leLit and geLit before t1EqT2Lit it would assign an
    // arbitrary phase to t1EqT2Lit.
    ctx.setTrueFirstFlag(leLit.var());
    ctx.setTrueFirstFlag(geLit.var());
  }
  TheoryId tid = d_owner.getId();
  ctx.mkThAxiom(tid, ~t1EqT2Lit, leLit);
  ctx.mkThAxiom(tid, ~t1EqT2Lit, geLit);
  ctx.mkThAxiom(tid, t1EqT2Lit, ~leLit, ~geLit);

  if (ctx.getParams().d_arithAddBinaryBounds)
  {
    ctx.mkThAxiom(tid, leLit, geLit);
  }
  if (ctx.relevancy())
  {
    RelevancyEh* eh = ctx.mkRelevancyEh(
        ArithEqRelevancyEh(n1->getExpr(), n2->getExpr(), t1EqT2, le, ge));
    ctx.addRelevancyEh(n1->getExpr(), eh);
    ctx.addRelevancyEh(n2->getExpr(), eh);
  }
  if (!ctx.getParams().d_arithLazyAdapter && !ctx.atBaseLevel()
      && n1->getIscopeLvl() <= ctx.getBaseLevel()
      && n2->getIscopeLvl() <= ctx.getBaseLevel())
  {
    d_restartPairs.push_back({n1, n2});
  }
}

void ArithEqAdapter::newEqEh(TheoryVar v1, TheoryVar v2)
{
  mkAxioms(d_owner.getENode(v1), d_owner.getENode(v2));
}

void ArithEqAdapter::newDiseqEh(TheoryVar v1, TheoryVar v2)
{
  mkAxioms(d_owner.getENode(v1), d_owner.getENode(v2));
}

void ArithEqAdapter::initSearchEh() { d_restartPairs.clear(); }

void ArithEqAdapter::resetEh()
{
  d_alreadyProcessed.clear();
  d_restartPairs.clear();
  d_stats = Stats();
}

void ArithEqAdapter::restartEh()
{
  SmtContext& ctx = getContext();
  std::vector<std::pair<ENode*, ENode*>> tmp(d_restartPairs);
  d_restartPairs.clear();
  for (const std::pair<ENode*, ENode*>& p : tmp)
  {
    if (ctx.inconsistent())
    {
      break;
    }
    mkAxioms(p.first, p.second);
  }
}

}  // namespace z3
}  // namespace cvc5::internal

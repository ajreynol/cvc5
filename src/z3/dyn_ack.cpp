/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Dynamic Ackermannization.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/dyn_ack.cpp, and recast in cvc5 style.
 */

#include "z3/dyn_ack.h"

#include <algorithm>

#include "expr/node_manager.h"
#include "z3/ast.h"
#include "z3/smt_context.h"

namespace cvc5::internal {
namespace z3 {

namespace {

/** Removes the manager's record of a clause when the clause is deleted. */
class DynAckClauseDelEh : public ClauseDelEh
{
 public:
  DynAckClauseDelEh(DynAckManager& m) : d_m(m) {}
  void operator()(Clause* cls) override
  {
    d_m.delClauseEh(cls);
    delete this;
  }

 private:
  DynAckManager& d_m;
};

}  // namespace

DynAckManager::DynAckManager(SmtContext& ctx, Params& p)
    : d_context(ctx),
      d_params(p),
      d_qhead(0),
      d_numInstances(0),
      d_numPropagationsSinceLastGc(0)
{
}

DynAckManager::~DynAckManager()
{
  resetAppPairs();
  resetExprTriples();
}

void DynAckManager::resetAppPairs() { d_appPairs.clear(); }

void DynAckManager::initSearchEh()
{
  d_appPair2NumOccs.clear();
  resetAppPairs();
  d_toInstantiate.clear();
  d_qhead = 0;
  d_numInstances = 0;
  d_numPropagationsSinceLastGc = 0;

  d_triple.d_app2NumOccs.clear();
  resetExprTriples();
  d_triple.d_toInstantiate.clear();
  d_triple.d_qhead = 0;
}

void DynAckManager::cgEh(TNode n1, TNode n2)
{
  Assert(getDecl(n1) == getDecl(n2));
  Assert(n1.getNumChildren() == n2.getNumChildren());
  Assert(n1 != n2);
  if (n1.getKind() == Kind::EQUAL)
  {
    return;
  }
  if (n1.getId() > n2.getId())
  {
    std::swap(n1, n2);
  }
  AppPair p(n1, n2);
  if (d_instantiated.count(p) != 0)
  {
    return;
  }
  uint32_t numOccs = 0;
  auto it = d_appPair2NumOccs.find(p);
  if (it != d_appPair2NumOccs.end())
  {
    numOccs = it->second + 1;
  }
  else
  {
    numOccs = 1;
    d_appPairs.push_back(p);
  }
  Assert(numOccs > 0);
  d_appPair2NumOccs[p] = numOccs;
  if (numOccs == d_params.d_dackThreshold)
  {
    d_toInstantiate.push_back(p);
  }
}

void DynAckManager::eqEh(TNode n1, TNode n2, TNode r)
{
  if (n1 == n2 || r == n1 || r == n2 || n1.getType().isBoolean())
  {
    return;
  }
  if (n1.getId() > n2.getId())
  {
    std::swap(n1, n2);
  }
  ExprTriple tr(n1, n2, r);
  if (d_triple.d_instantiated.count(tr) != 0)
  {
    return;
  }
  uint32_t numOccs = 0;
  auto it = d_triple.d_app2NumOccs.find(tr);
  if (it != d_triple.d_app2NumOccs.end())
  {
    numOccs = it->second + 1;
  }
  else
  {
    numOccs = 1;
    d_triple.d_apps.push_back(tr);
  }
  Assert(numOccs > 0);
  d_triple.d_app2NumOccs[tr] = numOccs;
  if (numOccs == d_params.d_dackThreshold)
  {
    d_triple.d_toInstantiate.push_back(tr);
  }
}

void DynAckManager::gc()
{
  d_toInstantiate.clear();
  d_qhead = 0;
  std::vector<AppPair> kept;
  kept.reserve(d_appPairs.size());
  for (const AppPair& p : d_appPairs)
  {
    if (d_instantiated.count(p) != 0)
    {
      continue;
    }
    uint32_t numOccs = 0;
    auto it = d_appPair2NumOccs.find(p);
    if (it != d_appPair2NumOccs.end())
    {
      numOccs = it->second;
    }
    // Note the invariant numOccs > 0 does not hold: a pair may have been
    // instantiated and removed from d_appPair2NumOccs but not from
    // d_appPairs.
    numOccs = static_cast<uint32_t>(numOccs * d_params.d_dackGcInvDecay);
    if (numOccs <= 1)
    {
      d_appPair2NumOccs.erase(p);
      continue;
    }
    kept.push_back(p);
    d_appPair2NumOccs[p] = numOccs;
    if (numOccs >= d_params.d_dackThreshold)
    {
      d_toInstantiate.push_back(p);
    }
  }
  d_appPairs = std::move(kept);
  // The comparison is not a total order on pairs, so sort stably to keep the
  // behavior identical across platforms.
  const std::unordered_map<AppPair, uint32_t, AppPairHash>& occs =
      d_appPair2NumOccs;
  std::stable_sort(d_toInstantiate.begin(),
                   d_toInstantiate.end(),
                   [&occs](const AppPair& p1, const AppPair& p2) {
                     uint32_t n1 = 0;
                     uint32_t n2 = 0;
                     auto i1 = occs.find(p1);
                     if (i1 != occs.end())
                     {
                       n1 = i1->second;
                     }
                     auto i2 = occs.find(p2);
                     if (i2 != occs.end())
                     {
                       n2 = i2->second;
                     }
                     return n1 > n2;
                   });
}

void DynAckManager::gcTriples()
{
  d_triple.d_toInstantiate.clear();
  d_triple.d_qhead = 0;
  std::vector<ExprTriple> kept;
  kept.reserve(d_triple.d_apps.size());
  for (const ExprTriple& p : d_triple.d_apps)
  {
    if (d_triple.d_instantiated.count(p) != 0)
    {
      continue;
    }
    uint32_t numOccs = 0;
    auto it = d_triple.d_app2NumOccs.find(p);
    if (it != d_triple.d_app2NumOccs.end())
    {
      numOccs = it->second;
    }
    numOccs = static_cast<uint32_t>(numOccs * d_params.d_dackGcInvDecay);
    if (numOccs <= 1)
    {
      d_triple.d_app2NumOccs.erase(p);
      continue;
    }
    kept.push_back(p);
    d_triple.d_app2NumOccs[p] = numOccs;
    if (numOccs >= d_params.d_dackThreshold)
    {
      d_triple.d_toInstantiate.push_back(p);
    }
  }
  d_triple.d_apps = std::move(kept);
  const std::unordered_map<ExprTriple, uint32_t, ExprTripleHash>& occs =
      d_triple.d_app2NumOccs;
  std::stable_sort(d_triple.d_toInstantiate.begin(),
                   d_triple.d_toInstantiate.end(),
                   [&occs](const ExprTriple& p1, const ExprTriple& p2) {
                     uint32_t n1 = 0;
                     uint32_t n2 = 0;
                     auto i1 = occs.find(p1);
                     if (i1 != occs.end())
                     {
                       n1 = i1->second;
                     }
                     auto i2 = occs.find(p2);
                     if (i2 != occs.end())
                     {
                       n2 = i2->second;
                     }
                     return n1 > n2;
                   });
}

void DynAckManager::delClauseEh(Clause* cls)
{
  d_context.getStats().d_numDelDynAck++;
  auto it = d_clause2AppPair.find(cls);
  if (it != d_clause2AppPair.end())
  {
    d_instantiated.erase(it->second);
    d_clause2AppPair.erase(it);
    return;
  }
  auto it2 = d_triple.d_clause2Apps.find(cls);
  if (it2 != d_triple.d_clause2Apps.end())
  {
    d_triple.d_instantiated.erase(it2->second);
    d_triple.d_clause2Apps.erase(it2);
    return;
  }
}

void DynAckManager::propagateEh()
{
  if (d_params.d_dack == DACK_DISABLED)
  {
    return;
  }
  d_numPropagationsSinceLastGc++;
  if (d_numPropagationsSinceLastGc > d_params.d_dackGc)
  {
    gc();
    d_numPropagationsSinceLastGc = 0;
  }
  size_t maxInstances = static_cast<size_t>(d_context.getNumConflicts()
                                            * d_params.d_dackFactor);
  while (d_numInstances < maxInstances && d_qhead < d_toInstantiate.size())
  {
    AppPair p = d_toInstantiate[d_qhead];
    d_qhead++;
    d_numInstances++;
    instantiate(p.first, p.second);
  }
  while (d_numInstances < maxInstances
         && d_triple.d_qhead < d_triple.d_toInstantiate.size())
  {
    ExprTriple tr = d_triple.d_toInstantiate[d_triple.d_qhead];
    d_triple.d_qhead++;
    d_numInstances++;
    instantiate(std::get<0>(tr), std::get<1>(tr), std::get<2>(tr));
  }
}

Literal DynAckManager::mkEq(TNode n1, TNode n2)
{
  Node eq = n1.getNodeManager()->mkNode(Kind::EQUAL, n1, n2);
  d_context.internalize(eq, true);
  return d_context.getLiteral(eq);
}

void DynAckManager::instantiate(TNode n1, TNode n2)
{
  Assert(d_params.d_dack != DACK_DISABLED);
  Assert(getDecl(n1) == getDecl(n2));
  Assert(n1.getNumChildren() == n2.getNumChildren());
  Assert(n1 != n2);
  d_context.getStats().d_numDynAck++;
  size_t numArgs = n1.getNumChildren();
  LiteralVector lits;
  for (size_t i = 0; i < numArgs; ++i)
  {
    TNode arg1 = n1[i];
    TNode arg2 = n2[i];
    if (arg1 != arg2)
    {
      lits.push_back(~mkEq(arg1, arg2));
    }
  }
  AppPair p(n1, n2);
  Assert(d_appPair2NumOccs.count(p) != 0);
  d_appPair2NumOccs.erase(p);
  // the pair is still in d_appPairs
  d_instantiated.insert(p);
  lits.push_back(mkEq(n1, n2));
  ClauseDelEh* delEh = new DynAckClauseDelEh(*this);

  for (Literal lit : lits)
  {
    d_context.markAsRelevant(lit);
  }

  Clause* cls = d_context.mkClause(
      lits.size(), lits.data(), nullptr, CLS_TH_LEMMA, delEh);
  if (cls == nullptr)
  {
    delete delEh;
    return;
  }
  d_clause2AppPair[cls] = p;
}

void DynAckManager::instantiate(TNode n1, TNode n2, TNode r)
{
  Assert(d_params.d_dack != DACK_DISABLED);
  Assert(n1 != n2 && n1 != r && n2 != r);
  d_context.getStats().d_numDynAck++;
  ExprTriple tr(n1, n2, r);
  Assert(d_triple.d_app2NumOccs.count(tr) != 0);
  d_triple.d_app2NumOccs.erase(tr);
  // the triple is still in d_triple.d_apps
  d_triple.d_instantiated.insert(tr);
  LiteralVector lits;
  Literal eq1 = mkEq(n1, r);
  Literal eq2 = mkEq(n2, r);
  Literal eq3 = mkEq(n1, n2);
  lits.push_back(~eq1);
  lits.push_back(~eq2);
  lits.push_back(eq3);
  ClauseDelEh* delEh = new DynAckClauseDelEh(*this);
  d_context.markAsRelevant(eq1);
  d_context.markAsRelevant(eq2);
  d_context.markAsRelevant(eq3);
  Clause* cls = d_context.mkClause(
      lits.size(), lits.data(), nullptr, CLS_TH_LEMMA, delEh);
  if (cls == nullptr)
  {
    delete delEh;
    return;
  }
  d_triple.d_clause2Apps[cls] = tr;
}

void DynAckManager::resetExprTriples() { d_triple.d_apps.clear(); }

void DynAckManager::reset()
{
  initSearchEh();
  d_instantiated.clear();
  d_clause2AppPair.clear();
  d_triple.d_instantiated.clear();
  d_triple.d_clause2Apps.clear();
}

}  // namespace z3
}  // namespace cvc5::internal

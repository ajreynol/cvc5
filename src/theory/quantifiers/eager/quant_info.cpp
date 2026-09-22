/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Quantifier info for eager instantiation
 */

#include "theory/quantifiers/eager/quant_info.h"

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "smt/env.h"
#include "theory/quantifiers/ematching/pattern_term_selector.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_database_eager.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

namespace eager {

QuantInfo::QuantInfo(TermDbEager& tde)
    : d_tde(tde),
      d_asserted(tde.getSatContext()),
      d_cfindex(tde.getSatContext(), 0),
      d_tstatus(tde.getSatContext(), TriggerStatus::NONE),
      d_hasActivated(false)
{
}

void QuantInfo::initialize(QuantifiersRegistry& qr, const Node& q)
{
  Assert(d_quant.isNull());
  Assert(q.getKind() == Kind::FORALL);
  d_quant = q;
  Stats& s = d_tde.getStats();
  ++(s.d_nquant);
  // TODO: if we have a nested quantified, don't bother?

  // first, collect critical functions
  std::unordered_set<TNode> visited;
  collectCriticalFuns(visited);

  const Options& opts = d_tde.getEnv().getOptions();
  std::map<Node, inst::TriggerTermInfo> tinfo;
  // NOTE: the trigger selection here should be configurable
  inst::PatternTermSelector pts(q, options::TriggerSelMode::MAX);
  // get the user patterns
  std::vector<Node> userPatTerms;
  options::UserPatMode pmode = opts.quantifiers.userPatternsQuant;
  if (pmode != options::UserPatMode::IGNORE)
  {
    if (q.getNumChildren() == 3)
    {
      for (const Node& p : q[2])
      {
        // only consider single triggers
        if (p.getKind() == Kind::INST_PATTERN && p.getNumChildren() == 1)
        {
          Node patu = pts.getIsUsableTrigger(p[0], q);
          if (!patu.isNull())
          {
            userPatTerms.emplace_back(patu);
          }
        }
      }
    }
  }
  std::vector<Node> patTerms;
  if (userPatTerms.empty()
      || (pmode != options::UserPatMode::TRUST
          && pmode != options::UserPatMode::STRICT))
  {
    // auto-infer the patterns
    Node bd = qr.getInstConstantBody(q);
    pts.collect(bd, patTerms, tinfo);
  }
  for (const Node& up : userPatTerms)
  {
    Node upc = qr.substituteBoundVariablesToInstConstants(up, q);
    if (tinfo.find(upc) != tinfo.end())
    {
      // user pattern also chosen as an auto-pattern
      continue;
    }
    tinfo[upc].init(q, upc);
    patTerms.emplace_back(upc);
  }
  Trace("eager-inst-trigger") << "Triggers for " << q << ":" << std::endl;
  size_t nvars = q[0].getNumChildren();
  std::unordered_set<Node> processed;
  std::vector<Node> multiPatPool;
  for (const Node& p : patTerms)
  {
    inst::TriggerTermInfo& tip = tinfo[p];
    // must be a single trigger
    if (tip.d_fv.size() != nvars)
    {
      multiPatPool.emplace_back(p);
      continue;
    }
    // TODO: could use the polarity information in tip to initialize the trigger
    if (processed.find(p) != processed.end())
    {
      // in rare cases there may be a repeated pattern??
      continue;
    }
    processed.insert(p);
    Trace("eager-inst-trigger") << "  * " << p << std::endl;
    // convert back to bound variables
    Node t = qr.substituteInstConstantsToBoundVariables(p, q);
    initializeTrigger(t);
  }
  if (d_triggers.empty() && opts.quantifiers.eagerInstMultiTriggers)
  {
    // construct a multi-trigger
    std::vector<Node> fvs;
    std::vector<Node> mpSel;
    for (const Node& mp : multiPatPool)
    {
      bool newFv = false;
      inst::TriggerTermInfo& tip = tinfo[mp];
      for (const Node& v : tip.d_fv)
      {
        if (std::find(fvs.begin(), fvs.end(), v) == fvs.end())
        {
          newFv = true;
          fvs.push_back(v);
        }
      }
      if (newFv)
      {
        Node mt = qr.substituteInstConstantsToBoundVariables(mp, q);
        mpSel.emplace_back(mt);
        if (fvs.size() == nvars)
        {
          d_mpat = q.getNodeManager()->mkNode(Kind::INST_PATTERN, mpSel);
          break;
        }
      }
    }
    if (!d_mpat.isNull())
    {
      Trace("eager-inst-trigger") << "  * (multi) " << d_mpat << std::endl;
    }
  }
  if (!d_mpat.isNull())
  {
    ++(s.d_nquantMultiTrigger);
    Trace("eager-inst-trigger") << "#multi-trigger=1" << std::endl;
  }
  else
  {
    Trace("eager-inst-trigger")
        << "#triggers=" << d_triggers.size() << std::endl;
  }
  if (d_triggers.empty() && d_mpat.isNull())
  {
    // nothing to do
    ++(s.d_nquantNoTrigger);
  }
  else
  {
    d_tstatus = TriggerStatus::INACTIVE;
    updateStatus();
  }
}

void QuantInfo::collectCriticalFuns(std::unordered_set<TNode>& visited)
{
  Trace("eager-inst-trigger")
      << "Critical functions of " << d_quant << std::endl;
  TermDb& tdb = d_tde.getTermDb();
  std::vector<TNode> toVisit;
  TNode body = d_quant[1];
  if (body.getKind() == Kind::OR)
  {
    toVisit.insert(toVisit.begin(), body.begin(), body.end());
  }
  else
  {
    toVisit.emplace_back(body);
  }
  TNode cur;
  do
  {
    cur = toVisit.back();
    toVisit.pop_back();
    if (visited.find(cur) != visited.end())
    {
      continue;
    }
    visited.insert(cur);
    Kind ck = cur.getKind();
    // cur is entailed, NOT and EQUAL will make both sides relevant, regardless
    // NOTE: also the condition of ITE should always be relevant?
    if (ck == Kind::NOT || ck == Kind::EQUAL || !expr::isBooleanConnective(cur))
    {
      Node op = tdb.getMatchOperator(cur);
      if (!op.isNull())
      {
        FunInfo* finfo = d_tde.getOrMkFunInfo(op, cur.getNumChildren());
        Assert(finfo != nullptr);
        if (std::find(d_criticalFuns.begin(), d_criticalFuns.end(), finfo)
            == d_criticalFuns.end())
        {
          d_criticalFuns.push_back(finfo);
          finfo->watching(this);
          Trace("eager-inst-trigger") << "* " << op << std::endl;
        }
      }
      toVisit.insert(toVisit.begin(), cur.begin(), cur.end());
    }
  } while (!toVisit.empty());
}

bool QuantInfo::notifyAsserted()
{
  Assert(!d_asserted.get());
  d_asserted = true;
  return updateStatus();
}

bool QuantInfo::notifyFun(FunInfo* fi)
{
  // if we are inactive and we just updated the inactive trigger, update status
  if (d_asserted.get() && d_tstatus == TriggerStatus::INACTIVE)
  {
    Assert(d_cfindex.get() < d_criticalFuns.size());
    if (d_criticalFuns[d_cfindex.get()] == fi)
    {
      Trace("eager-inst-status") << "...update status " << d_quant << std::endl;
      return updateStatus();
    }
  }
  return false;
}

bool QuantInfo::updateStatus()
{
  if (!d_asserted.get() || d_tstatus != TriggerStatus::INACTIVE)
  {
    // nothing to do
    return false;
  }
  Assert(d_cfindex.get() <= d_criticalFuns.size());
  Trace("eager-inst-status")
      << "Update status " << d_quant << " " << d_cfindex.get() << " / "
      << d_criticalFuns.size() << std::endl;
  while (d_cfindex.get() < d_criticalFuns.size())
  {
    FunInfo* fnext = d_criticalFuns[d_cfindex.get()];
    if (fnext->getNumTerms() == 0)
    {
      Trace("eager-inst-status")
          << "..." << d_quant << " is still inactive due to "
          << fnext->getOperator() << std::endl;
      // the current function is still inactive
      return false;
    }
    d_cfindex = d_cfindex.get() + 1;
  }

  Trace("eager-inst-status") << "...activate quant: " << d_quant << std::endl;
  if (!d_hasActivated)
  {
    d_hasActivated = true;
    ++(d_tde.getStats().d_nquantActivated);
  }
  // we are at the end, choose a trigger to activate
  d_tstatus = TriggerStatus::ACTIVE;
  size_t minTerms = 0;
  size_t bestIndex = 0;
  bool bestIndexSet = false;
  if (d_triggers.empty())
  {
    Assert(!d_mpat.isNull());
    TermDb& tdb = d_tde.getTermDb();
    // select best within the pattern as the head
    for (size_t i = 0, ntriggers = d_mpat.getNumChildren(); i < ntriggers; i++)
    {
      Node op = tdb.getMatchOperator(d_mpat[i]);
      Assert(!op.isNull());
      FunInfo* finfo = d_tde.getOrMkFunInfo(op, d_mpat[i].getNumChildren());
      Assert(finfo != nullptr);
      size_t cterms = finfo->getNumTerms();
      if (!bestIndexSet || cterms < minTerms)
      {
        bestIndex = i;
        minTerms = cterms;
      }
      bestIndexSet = true;
    }
    bestIndex = 0;
    // TODO: reorder based on heuristic?
    initializeTrigger(d_mpat);
  }
  else
  {
    for (size_t i = 0, ntriggers = d_triggers.size(); i < ntriggers; i++)
    {
      TriggerInfo* tinfo = d_triggers[i];
      TriggerStatus s = tinfo->getStatus();
      if (s == TriggerStatus::ACTIVE)
      {
        bestIndex = i;
        bestIndexSet = true;
        break;
      }
      else
      {
        Node op = tinfo->getOperator();
        Assert(!op.isNull());
        FunInfo* finfo = d_tde.getFunInfo(op);
        size_t cterms = finfo->getNumTerms();
        if (!bestIndexSet || cterms < minTerms)
        {
          bestIndex = i;
          minTerms = cterms;
        }
        bestIndexSet = true;
      }
    }
  }
  Assert(bestIndexSet);
  Assert(d_triggers.size() == d_vlists.size());
  Assert(d_triggers.size() == d_triggerWatching.size());
  d_cfindex = bestIndex;
  watchAndActivateTrigger(bestIndex);
  TriggerInfo* bestTrigger = d_triggers[bestIndex];
  // match all
  if (bestTrigger->doMatchingAll())
  {
    return true;
  }

  // if enabling all
  if (d_tde.getEnv().getOptions().quantifiers.eagerInstTrigger
      == options::EagerInstTriggerMode::ALL)
  {
    // actually watch all
    for (size_t i = 0, ntriggers = d_triggers.size(); i < ntriggers; i++)
    {
      if (i != bestIndex)
      {
        watchAndActivateTrigger(i);
      }
    }
  }
  return false;
}

void QuantInfo::watchAndActivateTrigger(size_t i)
{
  TriggerInfo* t = d_triggers[i];
  // ensure we are signed up to watch the best trigger
  if (!d_triggerWatching[i])
  {
    Trace("eager-inst-debug")
        << "Add watch: " << d_quant << " for " << t->getPattern() << std::endl;
    d_triggerWatching[i] = true;
    t->watch(this, d_vlists[i]);
  }
  // activate the trigger, which if it is not already active will
  t->setStatus(TriggerStatus::ACTIVE);
}

void QuantInfo::initializeTrigger(const Node& t)
{
  expr::TermCanonize& canon = d_tde.getTermCanon();
  std::map<TNode, Node> visited;
  Node tc = canon.getCanonicalTerm(t, visited);
  eager::TriggerInfo* ti = d_tde.getTriggerInfo(tc);
  // get the variable list that we canonized to
  d_vlists.emplace_back();
  std::vector<Node>& vlist = d_vlists.back();
  for (const Node& v : d_quant[0])
  {
    Assert(visited.find(v) != visited.end());
    vlist.emplace_back(visited[v]);
  }
  d_triggers.emplace_back(ti);
  d_triggerWatching.emplace_back(false);
  ++(d_tde.getStats().d_ntriggers);
}

TriggerInfo* QuantInfo::getActiveTrigger()
{
  if (d_tstatus != TriggerStatus::ACTIVE)
  {
    return nullptr;
  }
  Assert(d_cfindex.get() < d_triggers.size());
  return d_triggers[d_cfindex.get()];
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

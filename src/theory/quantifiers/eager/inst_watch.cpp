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
 * Instantiation watch
 */

#include "theory/quantifiers/eager/inst_watch.h"

#include "context/cdo.h"
#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database_eager.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

void collectWatchTerms(const Node& n, std::vector<Node>& watchTerms)
{
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (cur.isClosure() || cur.isConst())
      {
        continue;
      }
      if (expr::isBooleanConnective(cur) || cur.getKind() == Kind::EQUAL)
      {
        // traverse Boolean connectives and equalities
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      else
      {
        watchTerms.emplace_back(cur);
      }
    }
  } while (!visit.empty());
}

InstWatch::InstWatch(TermDbEager& tde)
    : d_tde(tde),
      d_qs(tde.getState()),
      d_processedInst(tde.getEnv().getContext())
{
  d_false = tde.getEnv().getNodeManager()->mkConst(false);
}

void InstWatch::watch(const Node& q,
                      const std::vector<Node>& terms,
                      const Node& entv)
{
  Trace("eager-inst-watch") << "Watch " << entv << std::endl;
  // collect watchable terms
  std::vector<Node> wterms;
  collectWatchTerms(entv, wterms);
  Assert(!wterms.empty());
  Node inst = mkInstantiation(q, terms);
  // have each watch term watch it
  for (const Node& wt : wterms)
  {
    Trace("eager-inst-watch") << "...watch term " << wt << std::endl;
    WatchTermInfo* wti = getWatchTermInfo(wt);
    wti->d_insts[inst] = true;
  }
}

bool InstWatch::eqNotifyMerge(TNode t1, TNode t2)
{
  std::map<Node, WatchTermInfo>::iterator it;
  for (size_t i = 0; i < 2; i++)
  {
    TNode t = i == 0 ? t1 : t2;
    if (t.getKind() == Kind::EQUAL)
    {
      if (eqNotifyMerge(t[0], t[1]))
      {
        return true;
      }
      continue;
    }
    Trace("eager-inst-watch-debug") << "...look at " << t << "?" << std::endl;
    it = d_wtInfo.find(t);
    if (it != d_wtInfo.end())
    {
      WatchTermInfo* wti = &it->second;
      Trace("eager-inst-watch") << "Revisit " << wti->d_insts.size()
                                << " instantiations from " << t << std::endl;
      // revisit instantiations
      for (context::CDHashMap<Node, bool>::iterator itw = wti->d_insts.begin();
           itw != wti->d_insts.end();
           ++itw)
      {
        if ((*itw).second)
        {
          if (revisitInstantiation(wti, (*itw).first))
          {
            return true;
          }
        }
      }
    }
  }
  return false;
}

bool InstWatch::eqNotifyDisequal(TNode t1, TNode t2)
{
  // TODO: different from merge
  return eqNotifyMerge(t1, t2);
}

WatchTermInfo* InstWatch::getWatchTermInfo(const Node& t)
{
  Assert(!t.isNull());
  std::map<Node, WatchTermInfo>::iterator it = d_wtInfo.find(t);
  if (it == d_wtInfo.end())
  {
    d_wtInfo.emplace(t, d_tde.getEnv().getContext());
    it = d_wtInfo.find(t);
  }
  return &it->second;
}

WatchQuantInfo* InstWatch::getWatchQuantInfo(const Node& q)
{
  Assert(!q.isNull());
  std::map<Node, WatchQuantInfo>::iterator it = d_wqInfo.find(q);
  if (it == d_wqInfo.end())
  {
    d_wqInfo.emplace(q, d_tde.getEnv().getContext());
    it = d_wqInfo.find(q);
    // initialize the evaluator and watch the quantified formula
    it->second.d_ieval.reset(
        new ieval::InstEvaluator(d_tde.getEnv(),
                                 d_tde.getState(),
                                 d_tde.getTermDb(),
                                 ieval::TermEvaluatorMode::PROP,
                                 false,
                                 false,
                                 false,
                                 true));
    it->second.d_ieval->watch(q);
  }
  return &it->second;
}

Node InstWatch::mkInstantiation(const Node& q, const std::vector<Node>& terms)
{
  Assert(!terms.empty());
  std::vector<Node> sterms;
  sterms.push_back(q);
  sterms.insert(sterms.end(), terms.begin(), terms.end());
  return q.getNodeManager()->mkNode(Kind::SEXPR, sterms);
}

Node InstWatch::getInstantiation(const Node& inst, std::vector<Node>& terms)
{
  Assert(inst.getKind() == Kind::SEXPR && inst.getNumChildren() >= 2);
  terms.insert(terms.end(), inst.begin() + 1, inst.end());
  return inst[0];
}

bool InstWatch::revisitInstantiation(WatchTermInfo* wti, const Node& inst)
{
  if (d_processedInst.find(inst) != d_processedInst.end())
  {
    // already processed
    wti->d_insts[inst] = false;
    return false;
  }
  std::vector<Node> terms;
  Node q = getInstantiation(inst, terms);
  Trace("eager-inst-watch") << "Revisit " << q << " " << terms << std::endl;
  WatchQuantInfo* wqi = getWatchQuantInfo(q);
  ieval::InstEvaluator* iev = wqi->d_ieval.get();
  iev->resetAll(false);
  Assert(terms.size() == q[0].getNumChildren());
  for (size_t i = 0, nvars = terms.size(); i < nvars; i++)
  {
    if (!iev->push(q[0][i], terms[i]))
    {
      Trace("eager-inst-watch") << "...failed ieval" << std::endl;
      // it is no longer propagating, i.e. it became entailed
      d_processedInst.insert(inst);
      wti->d_insts[inst] = false;
      return false;
    }
  }
  // successful, check the entailment again
  Node newEntv = iev->getEntailedValue(q[1]);
  // disable watching this
  // TODO: disable from other watched terms?
  wti->d_insts[inst] = false;
  // try again
  bool isConflict = (newEntv == d_false);
  if (d_tde.addInstantiation(q, terms, newEntv, isConflict))
  {
    Trace("eager-inst-watch") << "...success" << std::endl;
    // if successful, we mark as processed
    d_processedInst.insert(inst);
    return isConflict;
  }
  Trace("eager-inst-watch") << "...failed add" << std::endl;
  return false;
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

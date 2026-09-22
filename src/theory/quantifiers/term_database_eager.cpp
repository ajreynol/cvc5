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
 * Eager term database
 */

#include "theory/quantifiers/term_database_eager.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

TermDbEager::TermDbEager(Env& env,
                         QuantifiersState& qs,
                         QuantifiersRegistry& qr,
                         TermDb& tdb)
    : EnvObj(env),
      d_qs(qs),
      d_qreg(qr),
      d_qim(nullptr),
      d_tdb(tdb),
      d_cdalloc(context()),
      d_notified(context()),
      // we canonize ground subterms if the option is set
      d_tcanon(
          nullptr, false, true, options().quantifiers.eagerInstMergeTriggers),
      d_stats(statisticsRegistry()),
      d_statsEnabled(options().base.statistics),
      d_whenEqc(options().quantifiers.eagerInstWhen
                == options::EagerInstWhenMode::EQC),
      d_whenEqcDelay(options().quantifiers.eagerInstWhen
                     == options::EagerInstWhenMode::EQC_DELAY),
      d_whenAsserted(options().quantifiers.eagerInstWhen
                     == options::EagerInstWhenMode::ASSERTED),
      d_whenStdCheck(options().quantifiers.eagerInstWhen
                     == options::EagerInstWhenMode::STANDARD_CHECK),
      d_eqcDelay(context()),
      d_qDelay(context()),
      d_entProps(context())
{
  // determine if we will filter instances that are not unit propagating
  options::EagerInstMode mode = options().quantifiers.eagerInstMode;
  d_filterNonUnit = (mode == options::EagerInstMode::UNIT_PROP
                     || mode == options::EagerInstMode::UNIT_PROP_WATCH
                     || mode == options::EagerInstMode::UNIT_PROP_FACT
                     || mode == options::EagerInstMode::CONFLICT_WATCH);
  d_filterConflict = (mode == options::EagerInstMode::CONFLICT_WATCH);
  d_filterFact = (mode == options::EagerInstMode::UNIT_PROP_FACT);
  // check if we will be watching
  if (mode == options::EagerInstMode::UNIT_PROP_WATCH
      || mode == options::EagerInstMode::CONFLICT_WATCH)
  {
    d_instWatch.reset(new eager::InstWatch(*this));
  }
  d_boolType = nodeManager()->booleanType();
}

void TermDbEager::finishInit(QuantifiersInferenceManager* qim) { d_qim = qim; }

void TermDbEager::assertQuantifier(TNode q)
{
  if (d_qs.isConflictingInst())
  {
    // already in conflict
    return;
  }
  if (d_whenStdCheck)
  {
    d_qDelay.push_back(q);
    return;
  }
  if (d_whenEqcDelay)
  {
    refresh();
  }
  // notify now
  notifyQuant(q);
}

bool TermDbEager::notifyQuant(TNode q)
{
  if (d_qreg.getOwner(q) != nullptr)
  {
    // skip quantified formulas that have owners
    return false;
  }
  Trace("eager-inst-notify") << "assertQuantifier: " << q << std::endl;
  eager::QuantInfo* qinfo = getQuantInfo(q);
  bool ret = qinfo->notifyAsserted();
  if (ret)
  {
    // trigger initialized which generated conflicting instantiation
    Trace("eager-inst-notify") << "...conflict" << std::endl;
  }
  else
  {
    Trace("eager-inst-notify") << "...finished" << std::endl;
  }
  // do pending
  d_qim->doPending();
  return ret;
}

void TermDbEager::eqNotifyNewClass(TNode t)
{
  if (d_qs.isConflictingInst())
  {
    // already in conflict
    return;
  }
  Trace("eager-inst-notify") << "eqNotifyNewClass: " << t << std::endl;
  // always notify now, indicate asserted if d_whenEqc is true
  notifyTerm(t, d_whenEqc);
  if (d_whenEqcDelay || d_whenStdCheck)
  {
    d_eqcDelay.push_back(t);
  }
  Trace("eager-inst-notify") << "...finished" << std::endl;
}
void TermDbEager::eqNotifyMerge(TNode t1, TNode t2)
{
  Trace("eager-inst-notify")
      << "eqNotifyMerge: " << t1 << " " << t2 << std::endl;
  // alternative strategy where you notify triggers only when this is the first
  // time seeing t1 / t2. This indicates that terms are processed when
  // they are asserted.
  if (d_whenAsserted)
  {
    // notify both, recursively
    std::vector<TNode> visit{t1, t2};
    TNode cur;
    do
    {
      cur = visit.back();
      visit.pop_back();
      if (d_notified.find(cur) == d_notified.end())
      {
        d_notified.insert(cur);
        // notice we notify top down
        if (notifyTerm(cur, true))
        {
          // already in conflict
          Trace("eager-inst-notify") << "...conflict notifyTerm" << std::endl;
          return;
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      // otherwise already notified
    } while (!visit.empty());
  }
  else if (d_whenEqcDelay)
  {
    refresh();
  }
  if (d_instWatch != nullptr)
  {
    if (d_instWatch->eqNotifyMerge(t1, t2))
    {
      Trace("eager-inst-notify") << "...conflict instWatch" << std::endl;
      return;
    }
  }
  Trace("eager-inst-notify") << "...finished" << std::endl;
}

void TermDbEager::eqNotifyDisequal(TNode t1, TNode t2)
{
  if (d_instWatch != nullptr)
  {
    if (d_instWatch->eqNotifyDisequal(t1, t2))
    {
      Trace("eager-inst-notify") << "...conflict instWatch" << std::endl;
      return;
    }
  }
}

void TermDbEager::eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  if (!d_filterFact || d_qs.isInConflict())
  {
    return;
  }
  d_qs.notifyInConflict();
  Node lit = t1.eqNode(t2);
  eq::EqualityEngine* mee = d_qs.getEqualityEngine();
  Node conf = mee->mkExplainLit(lit);
  Trace("eager-inst-fact") << "Conflict (from fact?): " << conf << std::endl;
  for (const Node& c : conf)
  {
    if (c.getKind() == Kind::SKOLEM)
    {
      std::vector<Node> terms;
      Node q = getExplainInst(c, terms);
      if (!q.isNull())
      {
        Trace("eager-inst-fact")
            << "...instantiation: " << q << " " << terms << std::endl;
        addInstantiationInternal(q, terms, false);
      }
    }
  }
  Trace("eager-inst-fact") << "...finish" << std::endl;
  d_qim->doPending();
}

bool TermDbEager::notifyTerm(TNode t, bool isAsserted)
{
  if (TermUtil::hasInstConstAttr(t))
  {
    return false;
  }
  // add to the eager trie
  TNode f = d_tdb.getMatchOperator(t);
  if (f.isNull())
  {
    return false;
  }
  Trace("eager-inst-notify") << "notifyTerm: " << t << std::endl;
  eager::FunInfo* finfo = getFunInfo(f);
  if (finfo == nullptr)
  {
    finfo = getOrMkFunInfo(f, t.getNumChildren());
  }
  // only add once, which we skip if d_whenAsserted is true and isAsserted is
  // true, since we should have already added
  if (d_whenEqc || !isAsserted)
  {
    ++(d_stats.d_nterms);
    if (finfo->addTerm(t))
    {
      Trace("eager-inst-notify") << "...conflict addTerm" << std::endl;
      return true;
    }
  }
  if (isCongruent(t))
  {
    Trace("eager-inst-notify") << "...congruent" << std::endl;
    // maybe was already congruent
    return false;
  }
  // if we successfully added, we do the matching now
  bool ret = finfo->notifyTriggers(t, isAsserted);
  Trace("eager-inst-notify") << "...return, conflict=" << ret << std::endl;
  d_qim->doPending();
  return ret;
}

bool TermDbEager::inRelevantDomain(TNode f, size_t i, TNode r)
{
  eager::FunInfo* finfo = getFunInfo(f);
  if (finfo == nullptr)
  {
    return false;
  }
  return finfo->inRelevantDomain(i, r);
}

TNode TermDbEager::getCongruentTerm(TNode f, const std::vector<TNode>& args)
{
  eager::FunInfo* finfo = getFunInfo(f);
  if (finfo == nullptr)
  {
    return d_null;
  }
  // add using the iterator
  CDTNodeTrieIterator itt(&d_cdalloc, d_qs);
  itt.initialize(finfo->getTrie(), args.size());
  for (TNode a : args)
  {
    if (!itt.push(a))
    {
      // failed
      return d_null;
    }
  }
  return itt.getCurrentData();
}

bool TermDbEager::isCongruent(TNode t) const
{
  return d_cdalloc.isCongruent(t);
}

eager::TriggerInfo* TermDbEager::getTriggerInfo(const Node& t)
{
  std::map<Node, eager::TriggerInfo>::iterator it = d_tinfo.find(t);
  if (it == d_tinfo.end())
  {
    Trace("eager-inst-db") << "mkTriggerInfo: " << t << std::endl;
    d_tinfo.emplace(t, *this);
    it = d_tinfo.find(t);
    Node tu;
    std::vector<Node> mtus;
    if (t.getKind() == Kind::INST_PATTERN)
    {
      tu = t[0];
      mtus.insert(mtus.end(), t.begin() + 1, t.end());
    }
    else
    {
      tu = t;
    }
    it->second.initialize(tu, mtus);
    ++(d_stats.d_ntriggersUnique);
    // add to triggers for the function
    TNode f = d_tdb.getMatchOperator(tu);
    Assert(!f.isNull());
    eager::FunInfo* finfo = getOrMkFunInfo(f, tu.getNumChildren());
    finfo->addTrigger(&it->second);
  }
  return &it->second;
}

eager::FunInfo* TermDbEager::getFunInfo(TNode f)
{
  Assert(!f.isNull());
  std::map<TNode, eager::FunInfo>::iterator it = d_finfo.find(f);
  if (it == d_finfo.end())
  {
    return nullptr;
  }
  return &it->second;
}

eager::FunInfo* TermDbEager::getOrMkFunInfo(TNode f, size_t nchild)
{
  Assert(!f.isNull());
  std::map<TNode, eager::FunInfo>::iterator it = d_finfo.find(f);
  if (it == d_finfo.end())
  {
    Trace("eager-inst-db") << "mkFunInfo: " << f << std::endl;
    d_finfo.emplace(f, *this);
    it = d_finfo.find(f);
    it->second.initialize(f, nchild);
  }
  return &it->second;
}

eager::QuantInfo* TermDbEager::getQuantInfo(TNode q)
{
  std::map<TNode, eager::QuantInfo>::iterator it = d_qinfo.find(q);
  if (it == d_qinfo.end())
  {
    Trace("eager-inst-db") << "mkQuantInfo: " << q << std::endl;
    d_qinfo.emplace(q, *this);
    it = d_qinfo.find(q);
    it->second.initialize(d_qreg, q);
  }
  return &it->second;
}

bool TermDbEager::addInstantiation(const Node& q,
                                   std::vector<Node>& terms,
                                   const Node& entv,
                                   bool isConflict)
{
  Trace("eager-inst-debug")
      << "addInstantiation: " << q << ", " << terms
      << ", isConflict=" << isConflict << ", ent=" << entv << std::endl;
  if (!entv.isNull() && entv.isConst() && entv.getConst<bool>())
  {
    // entailed true, can happen in rare cases e.g. a tautological combination
    // of equalities between known terms.
    return false;
  }
  // AlwaysAssert( !isConflict || entv.isConst());
  if (d_filterNonUnit)
  {
    //  if already propagated, skip
    if (d_entProps.find(entv) != d_entProps.end())
    {
      Trace("eager-inst-debug") << "...already entailed!" << std::endl;
      ++(d_stats.d_instFailDuplicateProp);
      return false;
    }
    d_entProps.insert(entv);
    Assert(!entv.isNull());
    bool success = false;
    bool entvPol = entv.getKind() != Kind::NOT;
    Node entvAtom = entvPol ? entv : entv[0];
    if (d_filterConflict)
    {
      // must be false
      success = (entv.isConst() && !entv.getConst<bool>());
    }
    else
    {
      // don't propagate connectives
      // don't propagate connectives or disequalities
      if (entvAtom.getKind() == Kind::EQUAL)
      {
        // equality betwee known terms? exclude equality between Booleans here
        if (!entvAtom[0].getType().isBoolean())
        {
          success = (entvPol && d_qs.hasTerm(entvAtom[0])
                     && d_qs.hasTerm(entvAtom[1]));
        }
      }
      else
      {
        // known predicate?
        success = d_qs.hasTerm(entvAtom);
      }
    }
    if (!success)
    {
      Trace("eager-inst-debug") << "...add to watch " << entv << std::endl;
      if (d_instWatch != nullptr)
      {
        d_instWatch->watch(q, terms, entv);
      }
      ++(d_stats.d_instFailFilterProp);
      return false;
    }
    Trace("eager-inst-ent") << "Instance entails: " << entv << std::endl;
    if (!entv.isConst())
    {
      if (d_filterFact)
      {
        Node exp = mkExplainInst(q, terms);
        eq::EqualityEngine* mee = d_qs.getEqualityEngine();
        Trace("eager-inst-fact") << "Infer: " << entv << std::endl;
        if (entvAtom.getKind() == Kind::EQUAL)
        {
          mee->assertEquality(entvAtom, entvPol, exp);
        }
        else
        {
          mee->assertPredicate(entvAtom, entvPol, exp);
        }
        return false;
      }
    }
    else
    {
      Assert(!entv.getConst<bool>());
    }
  }
#if 0
  Node inst = d_qim->getInstantiate()->getInstantiation(q, terms);
  if (!isPropagatingInstance(inst))
  {
    AlwaysAssert(false);
  }
#endif
  return addInstantiationInternal(q, terms, isConflict);
}
bool TermDbEager::addInstantiationInternal(const Node& q,
                                           std::vector<Node>& terms,
                                           bool isConflict)
{
  ++(d_stats.d_inst);
  InferenceId iid = InferenceId::QUANTIFIERS_INST_EAGER;
  if (isConflict)
  {
    iid = InferenceId::QUANTIFIERS_INST_EAGER_CONFLICT;
  }
  bool ret = d_qim->getInstantiate()->addInstantiation(q, terms, iid);
  if (!ret)
  {
    // Assert(!isConflict);
    Trace("eager-inst-debug") << "...failed!" << std::endl;
    Trace("eager-inst-warn") << "Bad instantiation: " << q << std::endl;
  }
  else
  {
    if (isConflict)
    {
      d_qs.notifyConflictingInst();
    }
    ++(d_stats.d_instSuccess);
    Trace("eager-inst-debug") << "...success!" << std::endl;
    Trace("eager-inst") << "* EagerInst: added instantiation "
                        << (isConflict ? "(conflict) " : "") << std::endl;
  }
  // note we don't flush pending lemmas yet
  return ret;
}

bool TermDbEager::isInactive(const Node& q)
{
  eager::QuantInfo* qi = getQuantInfo(q);
  // only if the trigger status is inactive
  return qi->getStatus() == eager::TriggerStatus::INACTIVE;
}

bool TermDbEager::isAsserted(TNode n)
{
  // if we are not doing eagerInstWhenAsserted, then we assume everything is
  // asserted.
  return !d_whenAsserted || d_notified.find(n) != d_notified.end();
}

bool TermDbEager::isPropagatingInstance(Node n)
{
  return isPropagatingTerm(n).isNull();
}

Node TermDbEager::isPropagatingTerm(Node n)
{
  NodeManager* nm = nodeManager();
  std::unordered_map<TNode, TNode> visited;
  std::unordered_map<TNode, TNode>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  eq::EqualityEngine* ee = d_qs.getEqualityEngine();
  do
  {
    cur = visit.back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = Node::null();
      if (!expr::hasBoundVar(cur))
      {
        if (!ee->hasTerm(cur))
        {
          return Node::null();
        }
        visit.pop_back();
        continue;
      }
      else if (cur.getKind() == Kind::FORALL)
      {
        return Node::null();
      }
      // otherwise visit children
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    if (it->second.isNull())
    {
      std::vector<TNode> children;
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        children.emplace_back(it->second);
      }
      Node ret;
      Node op = d_tdb.getMatchOperator(cur);
      if (!op.isNull())
      {
        ret = getCongruentTerm(op, children);
        if (ret.isNull())
        {
          return Node::null();
        }
        Assert(ee->hasTerm(ret));
      }
      else
      {
        ret = nm->mkNode(cur.getKind(), children);
        ret = rewrite(ret);
        if (!ee->hasTerm(ret))
        {
          return Node::null();
        }
      }
      ret = ee->getRepresentative(ret);
      visited[cur] = ret;
    }
    visit.pop_back();
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  return visited[n];
}

void TermDbEager::refresh()
{
  std::vector<TNode> next;
  d_qDelay.get(next);
  for (TNode n : next)
  {
    if (notifyQuant(n))
    {
      return;
    }
  }
  next.clear();
  d_eqcDelay.get(next);
  for (TNode n : next)
  {
    if (notifyTerm(n, true))
    {
      return;
    }
  }
}

Node TermDbEager::mkExplainInst(const Node& q, const std::vector<Node>& terms)
{
  std::vector<Node> qterms;
  qterms.push_back(q);
  qterms.insert(qterms.end(), terms.begin(), terms.end());
  SkolemManager* skm = nodeManager()->getSkolemManager();
  return skm->mkInternalSkolemFunction(
      InternalSkolemId::QUANTIFIERS_INST, d_boolType, {qterms});
}

Node TermDbEager::getExplainInst(const Node& i, std::vector<Node>& terms)
{
  Node cacheVal;
  SkolemId id;
  SkolemManager* skm = nodeManager()->getSkolemManager();
  if (skm->isSkolemFunction(i, id, cacheVal))
  {
    terms.insert(terms.end(), cacheVal.begin() + 2, cacheVal.end());
    return cacheVal[1];
  }
  return Node::null();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

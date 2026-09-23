/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Term manager.
 */

#include "theory/term_manager.h"

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers_engine.h"

namespace cvc5::internal {
namespace theory {

TermDbManager::TermDbManager(Env& env, TheoryEngine* engine)
    : TheoryEngineModule(env, engine, "TermDbManager"),
      d_omap(userContext()),
      d_qinLevel(userContext()),
      d_inputTerms(userContext())
{
}

void TermDbManager::notifyPreprocessedAssertions(
    const std::vector<Node>& assertions)
{
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  Node nullq;
  std::vector<TermOrigin*> emptyVec;
  visit.insert(visit.end(), assertions.begin(), assertions.end());
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (cur.getKind() == Kind::INST_PATTERN_LIST)
    {
      d_inputTerms.insert(cur);
      continue;
    }
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (!expr::isBooleanConnective(cur) && !expr::hasFreeVar(cur))
      {
        d_inputTerms.insert(cur);
        addOrigin(cur, InferenceId::NONE, nullq, emptyVec);
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}

void TermDbManager::notifyLemma(TNode n,
                                InferenceId id,
                                LemmaProperty p,
                                const std::vector<Node>& skAsserts,
                                const std::vector<Node>& sks)
{
  Trace("term-origin") << "Notify lemma: " << n << std::endl;
  std::unordered_set<TNode> visited;
  Node q;
  Node lem = n;
  std::vector<TermOrigin*> args;
  if (n.getKind() == Kind::IMPLIES && n[0].getKind() == Kind::FORALL)
  {
    q = n[0];
    // Assume any lemma of the form (=> (forall ...) ...) is an instantiation
    // lemma.
    QuantifiersEngine* qe = d_val.getQuantifiersEngine();
    std::vector<Node> inst;
    if (qe->getTermVectorForInstantiation(n, inst))
    {
      Trace("term-origin") << "Lemma is instantiation " << q << " with " << inst
                           << std::endl;
      for (const Node& nc : inst)
      {
        // do not visit the terms we are instantiating
        visited.insert(nc);
        args.emplace_back(getOrMkTermOrigin(nc));
      }
      // minor optimization: only look at new terms in the conclusion
      lem = n[1];
    }
    // TODO: do not visit ground subterms of the quantified formula
  }
  // get new terms
  std::vector<TNode> visit;
  TNode cur;
  visit.emplace_back(lem);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (d_inputTerms.find(cur) != d_inputTerms.end())
    {
      // input terms never change origin
      continue;
    }
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (!expr::isBooleanConnective(cur))
      {
        addOrigin(cur, id, q, args);
      }
      // do not traverse closures
      if (!cur.isClosure())
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  } while (!visit.empty());
}

TermDbManager::TermOrigin::TermOrigin(context::Context* c, const Node& t)
    : d_this(t), d_children(c), d_parents(c), d_quantDepth(c)
{
}

int64_t TermDbManager::TermOrigin::getQuantifierDepth(const Node& q) const
{
  context::CDHashMap<Node, int64_t>::iterator it = d_quantDepth.find(q);
  if (it != d_quantDepth.end())
  {
    return it->second;
  }
  return 0;
}

TermDbManager::TermOrigin* TermDbManager::getOrMkTermOrigin(const Node& n)
{
  context::CDHashMap<Node, std::shared_ptr<TermOrigin>>::iterator it =
      d_omap.find(n);
  if (it != d_omap.end())
  {
    return it->second.get();
  }
  std::shared_ptr<TermOrigin> tor =
      std::make_shared<TermOrigin>(userContext(), n);
  initializeTerm(n);
  d_omap.insert(n, tor);
  return tor.get();
}

void TermDbManager::addOrigin(const Node& n,
                              InferenceId id,
                              const Node& q,
                              const std::vector<TermOrigin*>& args)
{
  TermOrigin* t = getOrMkTermOrigin(n);
}

void TermDbManager::initializeTerm(const Node& n)
{
  if (n.getKind() == Kind::FORALL)
  {
    // get the origin level specified by user attribute
    // :quant-inst-origin-max-level.
    quantifiers::QAttributes qa;
    quantifiers::QuantAttributes::computeQuantAttributes(n, qa);
    if (qa.d_qinstNestedLevel != -1)
    {
      d_qinLevel[n] = qa.d_qinstNestedLevel;
      Trace("term-origin") << "Quantified formula " << n
                           << " has inst nested level " << qa.d_qinstNestedLevel
                           << std::endl;
    }
  }
}

int64_t TermDbManager::getInstNestedMaxLimit(const Node& q) const
{
  context::CDHashMap<Node, int64_t>::iterator it = d_qinLevel.find(q);
  if (it != d_qinLevel.end())
  {
    return it->second;
  }
  return options().quantifiers.instNestedMaxLevel;
}

bool TermDbManager::canInstantiate(const Node& q, const Node& n)
{
  int64_t maxLevel = getInstNestedMaxLimit(q);
  if (maxLevel == -1)
  {
    return true;
  }
  // input terms have a depth of 0 always
  if (d_inputTerms.find(n) != d_inputTerms.end())
  {
    return maxLevel > 0;
  }
  context::CDHashMap<Node, std::shared_ptr<TermOrigin>>::iterator it =
      d_omap.find(n);
  if (it == d_omap.end())
  {
    return true;
  }
  return it->second->getQuantifierDepth(q) <= maxLevel;
}

}  // namespace theory
}  // namespace cvc5::internal

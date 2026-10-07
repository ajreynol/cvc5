/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The queue of pending instances of eager E-matching.
 */

#include "theory/quantifiers/eager/inst_queue.h"

#include "options/quantifiers_options.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

Fingerprints::Fingerprints(Trail& trail) : d_trail(trail) {}

bool Fingerprints::add(TNode q, const std::vector<ENode*>& bindings)
{
  // z3 keys the fingerprint on the representatives of the bindings, so that
  // two matches that differ only up to the current equalities count as one.
  std::vector<Node> roots;
  roots.reserve(bindings.size());
  for (ENode* b : bindings)
  {
    roots.push_back(b->getRoot()->getNode());
  }
  std::pair<Node, std::vector<Node>> key(q, roots);
  if (d_fps.find(key) != d_fps.end())
  {
    return false;
  }
  d_fps.insert(key);
  d_trail.onPop([this, key]() { d_fps.erase(key); });
  return true;
}

InstQueue::InstQueue(Env& env, Trail& trail)
    : EnvObj(env),
      d_trail(trail),
      d_sink(nullptr),
      d_fps(trail),
      d_eagerThreshold(10.0),
      d_lazyThreshold(20.0)
{
}

InstQueue::~InstQueue() {}

uint32_t InstQueue::getWeight(CVC5_UNUSED TNode q) const
{
  // TODO: z3 reads the :weight annotation of the quantifier, which defaults to
  // 1 for quantifiers with nested quantifiers and 0 otherwise. See README.md
  // section 9, step 5.
  return 0;
}

double InstQueue::getCost(TNode q, uint32_t generation) const
{
  // z3's default cost function, (+ weight generation)
  return static_cast<double>(getWeight(q)) + static_cast<double>(generation);
}

uint32_t InstQueue::getNewGeneration(TNode q,
                                     uint32_t generation,
                                     CVC5_UNUSED double cost) const
{
  // z3's default new_gen behaviour
  return getWeight(q) > 0 ? generation : generation + 1;
}

void InstQueue::onMatch(TNode q,
                        TNode pat,
                        const std::vector<ENode*>& bindings,
                        uint32_t maxGeneration,
                        CVC5_UNUSED uint32_t minTopGeneration,
                        CVC5_UNUSED uint32_t maxTopGeneration)
{
  d_stats.d_numMatches++;
  Assert(bindings.size() == q[0].getNumChildren());
  if (!d_fps.add(q, bindings))
  {
    d_stats.d_numDuplicates++;
    return;
  }
  if (TraceIsOn("eager-inst-match"))
  {
    // the bindings are canonicalized to their representatives, as z3 does when
    // it logs a match, so that the two can be compared
    Trace("eager-inst-match") << "MATCH " << q.getId();
    for (ENode* b : bindings)
    {
      Trace("eager-inst-match") << " " << b->getRoot()->getNode();
    }
    Trace("eager-inst-match") << std::endl;
  }
  std::vector<Node> terms;
  terms.reserve(bindings.size());
  for (ENode* b : bindings)
  {
    terms.push_back(b->getNode());
  }
  Entry ent;
  ent.d_quant = q;
  ent.d_pattern = pat;
  ent.d_terms = terms;
  ent.d_generation = maxGeneration;
  ent.d_cost = getCost(q, maxGeneration);
  ent.d_instantiated = false;
  if (TraceIsOn("eager-inst-queue"))
  {
    Trace("eager-inst-queue") << "InstQueue: insert " << q << " with";
    for (const Node& t : terms)
    {
      Trace("eager-inst-queue") << " " << t;
    }
    Trace("eager-inst-queue") << ", cost " << ent.d_cost << std::endl;
  }
  d_newEntries.push_back(ent);
}

void InstQueue::instantiate()
{
  // z3: qi_queue::instantiate()
  for (Entry& ent : d_newEntries)
  {
    if (ent.d_cost <= d_eagerThreshold)
    {
      instantiate(ent);
    }
    else
    {
      // TODO: z3 additionally promotes an instance whose body is already false
      // under the current assignment (qi.promote_unsat). Needs the inner
      // solver's evaluation. See README.md section 9, step 6.
      size_t sz = d_delayed.size();
      d_delayed.push_back(ent);
      d_trail.onPop([this, sz]() { d_delayed.resize(sz); });
    }
  }
  d_newEntries.clear();
}

bool InstQueue::finalCheck()
{
  // z3: qi_queue::final_check_eh
  bool result = true;
  for (size_t i = 0; i < d_delayed.size(); i++)
  {
    Entry& ent = d_delayed[i];
    if (!ent.d_instantiated && ent.d_cost <= d_lazyThreshold)
    {
      result = false;
      d_stats.d_numLazyInstances++;
      instantiate(ent);
      // z3 records the index so that the entry becomes available again if we
      // backtrack past this point (qi_queue::m_instantiated_trail)
      d_trail.onPop([this, i]() { d_delayed[i].d_instantiated = false; });
    }
  }
  return result;
}

void InstQueue::instantiate(Entry& ent)
{
  // z3: qi_queue::instantiate(entry&)
  ent.d_instantiated = true;
  TNode q = ent.d_quant;
  std::vector<Node> vars(q[0].begin(), q[0].end());
  Node body = q[1].substitute(
      vars.begin(), vars.end(), ent.d_terms.begin(), ent.d_terms.end());
  body = rewrite(body);
  if (body.isConst() && body.getConst<bool>())
  {
    d_stats.d_numTrivial++;
    return;
  }
  NodeManager* nm = nodeManager();
  Node lemma;
  if (body.getKind() == Kind::OR)
  {
    std::vector<Node> disjuncts;
    disjuncts.push_back(q.notNode());
    disjuncts.insert(disjuncts.end(), body.begin(), body.end());
    lemma = nm->mkNode(Kind::OR, disjuncts);
  }
  else if (body.isConst())
  {
    Assert(!body.getConst<bool>());
    lemma = q.notNode();
  }
  else
  {
    lemma = nm->mkNode(Kind::OR, q.notNode(), body);
  }
  d_stats.d_numInstances++;
  uint32_t gen = getNewGeneration(q, ent.d_generation, ent.d_cost);
  Trace("eager-inst-queue")
      << "InstQueue: instance " << lemma << ", generation " << gen << std::endl;
  if (d_sink != nullptr)
  {
    d_sink->addInstance(q, ent.d_terms, lemma, gen);
  }
}

void InstQueue::clearWork() { d_newEntries.clear(); }

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

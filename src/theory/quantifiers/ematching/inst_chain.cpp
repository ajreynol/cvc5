/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of chained instantiation.
 */

#include "theory/quantifiers/ematching/inst_chain.h"

#include <algorithm>

#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_util.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

InstChain::InstChain(Env& env,
                     QuantifiersState& qs,
                     QuantifiersInferenceManager& qim,
                     QuantifiersRegistry& qr,
                     TermRegistry& tr)
    : EnvObj(env),
      d_qstate(qs),
      d_qim(qim),
      d_qreg(qr),
      d_treg(tr),
      d_stats(statisticsRegistry())
{
}

void InstChain::registerQuantifier(Node q)
{
  Assert(q.getKind() == Kind::FORALL);
  // only quantified formulas with user patterns are chained
  if (q.getNumChildren() != 3)
  {
    return;
  }
  if (!d_registered.insert(q).second)
  {
    return;
  }
  size_t nvars = q[0].getNumChildren();
  TermDb* tdb = d_treg.getTermDatabase();
  // the patterns of q, with its bound variables replaced by its instantiation
  // constants, which is the form the matching below expects
  Node ipl = d_qreg.substituteBoundVariablesToInstConstants(q[2], q);
  for (const Node& p : ipl)
  {
    if (p.getKind() != Kind::INST_PATTERN)
    {
      continue;
    }
    // multi-triggers are left to the ordinary round, see inst_chain.h
    if (p.getNumChildren() != 1)
    {
      continue;
    }
    Node pat = p[0];
    if (TermUtil::getInstConstAttr(pat) != q)
    {
      continue;
    }
    Node op = tdb->getMatchOperator(pat);
    if (op.isNull())
    {
      continue;
    }
    // the pattern must bind every variable of q, otherwise a match does not
    // determine an instantiation
    std::vector<Node> ics;
    TermUtil::computeInstConstContainsForQuant(q, pat, ics);
    std::unordered_set<size_t> vnums;
    for (const Node& ic : ics)
    {
      vnums.insert(ic.getAttribute(InstVarNumAttribute()));
    }
    if (vnums.size() != nvars)
    {
      continue;
    }
    Trace("inst-chain") << "InstChain: index " << pat << " for " << q
                        << std::endl;
    d_index[op].push_back(ChainPattern{q, pat});
  }
}

void InstChain::resetRound() { d_seen.clear(); }

uint64_t InstChain::check()
{
  if (d_index.empty())
  {
    return 0;
  }
  Instantiate* ie = d_qim.getInstantiate();
  // Note this vector grows as chained instantiations are added below, which
  // is how the chain advances from one depth to the next. It is indexed by
  // position for that reason.
  const std::vector<Node>& bodies = ie->getRoundInstBodies();
  uint64_t added = 0;
  uint64_t limit = options().quantifiers.instChainLimit;
  size_t cursor = 0;
  bool active = false;
  for (uint64_t d = 0, depth = options().quantifiers.instChainDepth; d < depth;
       d++)
  {
    size_t end = bodies.size();
    if (cursor >= end)
    {
      break;
    }
    std::vector<Node> newTerms;
    for (size_t i = cursor; i < end; i++)
    {
      collectNewTerms(bodies[i], newTerms);
    }
    cursor = end;
    if (newTerms.empty())
    {
      break;
    }
    active = true;
    d_stats.d_terms += newTerms.size();
    Trace("inst-chain") << "InstChain: depth " << d << ", " << newTerms.size()
                        << " new ground terms" << std::endl;
    for (const Node& t : newTerms)
    {
      added += processTerm(t);
      if (d_qstate.isInConflict())
      {
        return added;
      }
      if (limit > 0 && added >= limit)
      {
        Trace("inst-chain") << "InstChain: reached round limit" << std::endl;
        return added;
      }
    }
  }
  if (active)
  {
    ++(d_stats.d_rounds);
  }
  return added;
}

void InstChain::collectNewTerms(TNode body, std::vector<Node>& newTerms)
{
  TermDb* tdb = d_treg.getTermDatabase();
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  visit.push_back(body);
  do
  {
    TNode cur = visit.back();
    visit.pop_back();
    if (!visited.insert(cur).second)
    {
      continue;
    }
    // do not descend into nested quantified formulas
    if (cur.isClosure())
    {
      continue;
    }
    Node op = tdb->getMatchOperator(cur);
    // A term already in the equality engine is one the ordinary round either
    // has seen or will see, so only terms this round introduced are of
    // interest here.
    if (!op.isNull() && !d_qstate.hasTerm(cur) && d_index.count(op) > 0
        && d_seen.insert(cur).second)
    {
      newTerms.push_back(cur);
    }
    visit.insert(visit.end(), cur.begin(), cur.end());
  } while (!visit.empty());
}

uint64_t InstChain::processTerm(TNode t)
{
  TermDb* tdb = d_treg.getTermDatabase();
  Node op = tdb->getMatchOperator(t);
  std::map<Node, std::vector<ChainPattern>>::const_iterator it =
      d_index.find(op);
  if (it == d_index.end())
  {
    return 0;
  }
  FirstOrderModel* m = d_treg.getModel();
  Instantiate* ie = d_qim.getInstantiate();
  uint64_t added = 0;
  for (const ChainPattern& cp : it->second)
  {
    if (!m->isQuantifierActive(cp.d_quant))
    {
      continue;
    }
    ++(d_stats.d_pairs);
    std::vector<Node> subst(cp.d_quant[0].getNumChildren());
    if (!matchPattern(cp.d_pattern, t, subst))
    {
      continue;
    }
    // registerQuantifier only indexes patterns that bind every variable, so a
    // successful match is a complete substitution
    Assert(std::find(subst.begin(), subst.end(), Node::null()) == subst.end());
    Trace("inst-chain") << "InstChain: " << cp.d_pattern << " matched " << t
                        << std::endl;
    if (ie->addInstantiation(
            cp.d_quant, subst, InferenceId::QUANTIFIERS_INST_E_MATCHING_CHAIN))
    {
      added++;
      ++(d_stats.d_inst);
    }
    if (d_qstate.isInConflict())
    {
      break;
    }
  }
  return added;
}

bool InstChain::matchPattern(TNode pat, TNode t, std::vector<Node>& subst) const
{
  if (pat.getKind() == Kind::INST_CONSTANT)
  {
    if (pat.getType() != t.getType())
    {
      return false;
    }
    size_t vn = pat.getAttribute(InstVarNumAttribute());
    Assert(vn < subst.size());
    if (subst[vn].isNull())
    {
      subst[vn] = t;
      return true;
    }
    return subst[vn] == t || areEqualInContext(subst[vn], t);
  }
  if (!TermUtil::hasInstConstAttr(pat))
  {
    // a ground position of the pattern, which the term must agree with in the
    // current context
    return pat == t || areEqualInContext(pat, t);
  }
  // otherwise the two must have the same match operator, and their arguments
  // must match pairwise. Note we do not search the equality engine here: t is
  // not one of its terms, so it has no congruent terms to search.
  TermDb* tdb = d_treg.getTermDatabase();
  Node pop = tdb->getMatchOperator(pat);
  if (pop.isNull() || pop != tdb->getMatchOperator(t)
      || pat.getNumChildren() != t.getNumChildren())
  {
    return false;
  }
  for (size_t i = 0, nchild = pat.getNumChildren(); i < nchild; i++)
  {
    if (!matchPattern(pat[i], t[i], subst))
    {
      return false;
    }
  }
  return true;
}

bool InstChain::areEqualInContext(TNode a, TNode b) const
{
  return d_qstate.hasTerm(a) && d_qstate.hasTerm(b) && d_qstate.areEqual(a, b);
}

InstChain::Statistics::Statistics(StatisticsRegistry& sr)
    : d_rounds(sr.registerInt("InstChain::Rounds")),
      d_terms(sr.registerInt("InstChain::Speculative_Terms")),
      d_pairs(sr.registerInt("InstChain::Term_Pattern_Pairs")),
      d_inst(sr.registerInt("InstChain::Instantiations"))
{
}

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

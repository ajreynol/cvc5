/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Replay untrusted instantiation hints through native quantifier reasoning.
 */

#include "theory/quantifiers/inst_strategy_z3_replay.h"

#include "expr/node_algorithm.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/term_util.h"

namespace cvc5::internal::theory::quantifiers {

InstStrategyZ3Replay::InstStrategyZ3Replay(Env& env,
                                           QuantifiersState& qs,
                                           QuantifiersInferenceManager& qim,
                                           QuantifiersRegistry& qr,
                                           TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_received(
          env.getStatisticsRegistry().registerInt("z3::replay::received")),
      d_attempted(
          env.getStatisticsRegistry().registerInt("z3::replay::attempted")),
      d_invalid(env.getStatisticsRegistry().registerInt("z3::replay::invalid")),
      d_added(env.getStatisticsRegistry().registerInt("z3::replay::added"))
{
}

void InstStrategyZ3Replay::setInstantiations(Instantiations insts)
{
  d_pending = std::move(insts);
  d_received += getNumPending();
}

bool InstStrategyZ3Replay::needsCheck(Theory::Effort e)
{
  return !d_pending.empty() && !d_qstate.isInConflict()
         && e >= Theory::EFFORT_FULL;
}

void InstStrategyZ3Replay::registerQuantifier(Node q)
{
  d_registered.insert(q);
}

void InstStrategyZ3Replay::check(CVC5_UNUSED Theory::Effort e, QEffort quant_e)
{
  if (quant_e != QEFFORT_CONFLICT)
  {
    return;
  }
  beginCallDebug();
  // Only instantiate quantifiers actually asserted by native cvc5. In
  // particular, a port-prepared or nested quantifier is not an assumption.
  std::vector<Node> asserted;
  for (auto it = d_qstate.factsBegin(THEORY_QUANTIFIERS),
            end = d_qstate.factsEnd(THEORY_QUANTIFIERS);
       it != end;
       ++it)
  {
    Node q = (*it).d_assertion;
    if (q.getKind() == Kind::FORALL && d_pending.find(q) != d_pending.end())
    {
      asserted.push_back(q);
    }
  }
  for (Node q : asserted)
  {
    auto it = d_pending.find(q);
    if (it == d_pending.end())
    {
      continue;
    }
    auto& vectors = it->second;
    while (!vectors.empty())
    {
      if (d_qstate.isInConflict())
      {
        endCallDebug();
        return;
      }
      std::vector<Node> terms = std::move(vectors.back());
      vectors.pop_back();
      bool valid = terms.size() == q[0].getNumChildren();
      for (size_t i = 0; valid && i < terms.size(); ++i)
      {
        valid = !terms[i].isNull() && terms[i].getType() == q[0][i].getType()
                && !expr::hasFreeVar(terms[i])
                && !TermUtil::containsUninterpretedConstant(terms[i])
                && TermUtil::getInstConstAttr(terms[i]).isNull();
      }
      if (!valid)
      {
        ++d_invalid;
        continue;
      }
      ++d_attempted;
      if (d_qim.getInstantiate()->addInstantiation(
              q, terms, InferenceId::QUANTIFIERS_INST_Z3_REPLAY))
      {
        ++d_added;
      }
    }
    d_pending.erase(it);
  }
  endCallDebug();
}

size_t InstStrategyZ3Replay::getNumPending() const
{
  size_t count = 0;
  for (const auto& [q, vectors] : d_pending)
  {
    count += vectors.size();
  }
  return count;
}

std::string InstStrategyZ3Replay::identify() const { return "z3-replay"; }

size_t InstStrategyZ3Replay::getNumUnmapped() const
{
  size_t count = 0;
  for (const auto& [q, vectors] : d_pending)
  {
    if (d_registered.find(q) == d_registered.end())
    {
      count += vectors.size();
    }
  }
  return count;
}

}  // namespace cvc5::internal::theory::quantifiers

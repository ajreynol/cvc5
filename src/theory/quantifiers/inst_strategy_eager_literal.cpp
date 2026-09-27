/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Eager instantiation from falsified predicate literals.
 */

#include "theory/quantifiers/inst_strategy_eager_literal.h"

#include <algorithm>
#include <unordered_set>

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_util.h"
#include "theory/valuation.h"

namespace cvc5::internal::theory::quantifiers {

InstStrategyEagerLiteral::Anchor::Anchor(context::Context* c,
                                         Node q,
                                         Node atom,
                                         FactList& facts)
    : d_quant(q), d_atom(atom), d_facts(facts), d_index(c, 0)
{
}

InstStrategyEagerLiteral::InstStrategyEagerLiteral(
    Env& env, QuantifiersState& qs, QuantifiersInferenceManager& qim)
    : EnvObj(env),
      d_qstate(qs),
      d_qim(qim),
      d_active(context()),
      d_seenFacts(context()),
      d_candidates(0),
      d_statCandidates(statisticsRegistry().registerInt(
          "theory::quantifiers::eagerLiteral::candidates")),
      d_statConflicts(statisticsRegistry().registerInt(
          "theory::quantifiers::eagerLiteral::conflicts")),
      d_statUnits(statisticsRegistry().registerInt(
          "theory::quantifiers::eagerLiteral::units")),
      d_statRejected(statisticsRegistry().registerInt(
          "theory::quantifiers::eagerLiteral::rejected"))
{
}

void InstStrategyEagerLiteral::presolve() { d_candidates = 0; }

InstStrategyEagerLiteral::FactList& InstStrategyEagerLiteral::getFacts(
    const FactKey& key)
{
  auto& facts = d_facts[key];
  if (!facts)
  {
    facts = std::make_unique<FactList>(context());
  }
  return *facts;
}

void InstStrategyEagerLiteral::registerQuantifier(Node q)
{
  Node body = q[1];
  if (expr::hasClosure(body))
  {
    return;
  }
  std::vector<Node> lits;
  if (body.getKind() == Kind::OR)
  {
    lits.assign(body.begin(), body.end());
  }
  else
  {
    lits.push_back(body);
  }
  // Do not turn a non-clausal body into clauses or interpret its connectives
  // as literals. Ordinary instantiation handles such formulas.
  for (Node lit : lits)
  {
    Node atom = lit.getKind() == Kind::NOT ? lit[0] : lit;
    if (expr::isBooleanConnective(atom))
    {
      return;
    }
  }
  std::vector<Node> vars(q[0].begin(), q[0].end());
  options::UserPatMode pmode = options().quantifiers.userPatternsQuant;
  bool restrictPatterns = pmode == options::UserPatMode::STRICT
                          || pmode == options::UserPatMode::TRUST;
  std::vector<Node> patterns;
  bool hasPatterns = false;
  if (restrictPatterns && q.getNumChildren() == 3)
  {
    for (Node p : q[2])
    {
      if (p.getKind() == Kind::INST_PATTERN)
      {
        hasPatterns = true;
        if (p.getNumChildren() == 1)
        {
          patterns.push_back(p[0]);
        }
      }
    }
  }
  for (Node lit : lits)
  {
    bool polarity = lit.getKind() != Kind::NOT;
    Node atom = polarity ? lit : lit[0];
    if (atom.getKind() != Kind::APPLY_UF
        || (hasPatterns
            && std::find(patterns.begin(), patterns.end(), atom)
                   == patterns.end()))
    {
      continue;
    }
    std::vector<int64_t> indices;
    std::vector<bool> covered(vars.size(), false);
    bool flat = true;
    for (Node arg : atom)
    {
      auto it = std::find(vars.begin(), vars.end(), arg);
      if (it != vars.end())
      {
        size_t index = it - vars.begin();
        indices.push_back(index);
        covered[index] = true;
      }
      else if (!expr::hasBoundVar(arg))
      {
        indices.push_back(-1);
      }
      else
      {
        flat = false;
        break;
      }
    }
    if (!flat
        || std::find(covered.begin(), covered.end(), false) != covered.end())
    {
      continue;
    }
    // Only facts falsifying this literal can yield a candidate. In particular,
    // a merely preregistered term, or a fact of the other sign, does no work.
    FactList& facts = getFacts({atom.getOperator(), !polarity});
    auto anchor = std::make_unique<Anchor>(context(), q, atom, facts);
    anchor->d_varIndices = std::move(indices);
    d_anchors.push_back(std::move(anchor));
  }
}

void InstStrategyEagerLiteral::assertQuantifier(Node q) { d_active.insert(q); }

void InstStrategyEagerLiteral::notifyAssertedFact(TNode fact)
{
  if (d_candidates >= options().quantifiers.eagerInstLiteralBudget)
  {
    return;
  }
  bool polarity = fact.getKind() != Kind::NOT;
  Node atom = polarity ? fact : fact[0];
  if (atom.getKind() != Kind::APPLY_UF || expr::hasBoundVar(atom)
      || TermUtil::hasInstConstAttr(atom)
      || TermUtil::containsUninterpretedConstant(atom)
      || !d_seenFacts.insert(fact))
  {
    return;
  }
  getFacts({atom.getOperator(), polarity}).d_list.push_back(atom);
}

int InstStrategyEagerLiteral::classify(Node body, Node fact)
{
  body = rewrite(body);
  std::vector<Node> lits;
  if (body.getKind() == Kind::OR)
  {
    lits.assign(body.begin(), body.end());
  }
  else
  {
    lits.push_back(body);
  }
  int unassigned = 0;
  Node unit;
  for (Node lit : lits)
  {
    if (lit.isConst())
    {
      if (lit.getConst<bool>())
      {
        return -1;
      }
      continue;
    }
    Node atom = lit.getKind() == Kind::NOT ? lit[0] : lit;
    if (expr::isBooleanConnective(atom))
    {
      return -1;
    }
    bool value;
    if (d_qstate.getValuation().hasSatValue(lit, value))
    {
      if (value)
      {
        return -1;
      }
    }
    else
    {
      if (++unassigned > 1)
      {
        return -1;
      }
      unit = atom;
    }
  }
  if (!unit.isNull())
  {
    // Allow new Boolean atoms over the anchor's existing terms, but leave
    // units that generate terms (e.g. Q(x) => Q(x+1)) to lazy instantiation.
    // Check after rewriting so this also catches fresh computed constants.
    std::vector<Node> visit{unit};
    std::unordered_set<Node> visited;
    while (!visit.empty())
    {
      Node n = visit.back();
      visit.pop_back();
      if (!visited.insert(n).second)
      {
        continue;
      }
      if (!n.getType().isBoolean()
          || (n != unit && n.getKind() == Kind::APPLY_UF))
      {
        if (!expr::hasSubterm(fact, n))
        {
          return -1;
        }
      }
      else
      {
        visit.insert(visit.end(), n.begin(), n.end());
      }
    }
  }
  return unassigned;
}

void InstStrategyEagerLiteral::check()
{
  if (d_qstate.isInConflict()
      || d_candidates >= options().quantifiers.eagerInstLiteralBudget)
  {
    return;
  }
  for (const auto& ap : d_anchors)
  {
    Anchor& a = *ap;
    if (!d_active.contains(a.d_quant))
    {
      continue;
    }
    while (a.d_index.get() < a.d_facts.d_list.size())
    {
      if (d_candidates >= options().quantifiers.eagerInstLiteralBudget)
      {
        return;
      }
      d_qim.safePoint(Resource::QuantifierStep);
      Node fact = a.d_facts.d_list[a.d_index.get()];
      a.d_index = a.d_index.get() + 1;
      ++d_candidates;
      ++d_statCandidates;
      std::vector<Node> terms(a.d_quant[0].getNumChildren());
      bool matches = true;
      for (size_t i = 0, n = a.d_varIndices.size(); i < n; ++i)
      {
        int64_t v = a.d_varIndices[i];
        if (v < 0)
        {
          matches = a.d_atom[i] == fact[i];
        }
        else if (terms[v].isNull())
        {
          terms[v] = fact[i];
        }
        else
        {
          matches = terms[v] == fact[i];
        }
        if (!matches)
        {
          break;
        }
      }
      if (!matches)
      {
        ++d_statRejected;
        continue;
      }
      std::vector<Node> vars(a.d_quant[0].begin(), a.d_quant[0].end());
      Node body = a.d_quant[1].substitute(
          vars.begin(), vars.end(), terms.begin(), terms.end());
      int status = classify(body, fact);
      if (status < 0)
      {
        // A later falsifying anchor fact can try again. We do not maintain
        // watches on rejected instances; lazy instantiation remains available.
        ++d_statRejected;
        continue;
      }
      InferenceId id =
          status == 0 ? InferenceId::QUANTIFIERS_INST_EAGER_LITERAL_CONFLICT
                      : InferenceId::QUANTIFIERS_INST_EAGER_LITERAL_UNIT;
      if (d_qim.getInstantiate()->addInstantiation(a.d_quant, terms, id))
      {
        if (status == 0)
        {
          ++d_statConflicts;
        }
        else
        {
          ++d_statUnits;
        }
        Trace("eager-inst-literal") << "standard effort " << id << ": "
                                    << a.d_quant << " -> " << body << std::endl;
        // Use the regular guarded instantiation lemma and its proof. The SAT
        // assignment is a selection heuristic, never a proof premise.
        d_qim.doPending();
        d_qim.getInstantiate()->notifyEndRound();
        return;
      }
    }
  }
}

}  // namespace cvc5::internal::theory::quantifiers

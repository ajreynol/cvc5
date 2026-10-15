/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * When the instances of the matches found are made.
 */

#include "z3/instance_policy.h"

#include <fstream>

#include "options/z3_options.h"
#include "smt/env.h"
#include "z3/ast.h"
#include "z3/enode.h"
#include "z3/fingerprints.h"
#include "z3/params.h"
#include "z3/quantifier_manager.h"
#include "z3/quantifier_services.h"
#include "z3/quantifier_stat.h"
#include "z3/statistics.h"

namespace cvc5::internal {
namespace z3 {

InstancePolicy::InstancePolicy(QuantifierManager& qm,
                               QuantifierServices& ctx,
                               Params& p)
    : d_qm(qm), d_context(ctx), d_params(p), d_checker(ctx)
{
}

TNode InstancePolicy::getQuantifier(Fingerprint* f) const
{
  return d_qm.getQuantifierById(f->getData());
}

bool InstancePolicy::skipSatisfied(TNode q,
                                   QuantifierStat* stat,
                                   size_t numBindings,
                                   ENode* const* bindings)
{
  if (d_context.getEnv().getOptions().z3.z3QiChecker
      && d_checker.isSat(getQuantBody(q), numBindings, bindings))
  {
    // The instance is already satisfied, so creating it would be wasted
    // work. It still counts as an instantiation, as it does in Z3.
    stat->incNumInstancesCheckerSat();
    d_context.getStats().d_numInstancesCheckerSat++;
    return true;
  }
  return false;
}

Node InstancePolicy::mkLemma(TNode q,
                             QuantifierStat* stat,
                             size_t numBindings,
                             ENode* const* bindings)
{
  // Substitute the bindings for the canonical quantified variables. Note
  // bindings[i] is the binding of the i-th variable of the bound variable
  // list, which is the variable at de Bruijn level i.
  TNode bvl = q[0];
  Assert(bvl.getNumChildren() == numBindings);
  std::vector<Node> vars;
  std::vector<Node> subs;
  for (size_t i = 0; i < numBindings; ++i)
  {
    vars.push_back(bvl[i]);
    subs.push_back(bindings[i]->getExpr());
  }
  Node instance = getQuantBody(q).substitute(
      vars.begin(), vars.end(), subs.begin(), subs.end());

  Trace("z3-qi-raw") << "RAWINST " << instance << std::endl;
  Trace("z3-events") << "INSTANCE " << instance << std::endl;
  const std::string& dumpTo =
      d_context.getEnv().getOptions().z3.z3DumpInstances;
  if (!dumpTo.empty())
  {
    // One line per instance, before the rewriter runs, which is the point at
    // which Z3's qi_queue trace prints its "new instance".
    std::ofstream out(dumpTo, std::ios::app);
    out << instance << "\n";
  }
  if (d_qm.inForcedRematch())
  {
    Trace("z3-qi-missed") << "MISSED q" << q.getId() << " " << instance
                          << std::endl;
  }
  Node sInstance = d_context.rewriteInstance(instance);

  if (sInstance.getKind() == Kind::CONST_BOOLEAN && sInstance.getConst<bool>())
  {
    stat->incNumInstancesSimplifyTrue();
    d_context.getStats().d_numInstancesSimplifyTrue++;
    return Node::null();
  }

  NodeManager* nm = q.getNodeManager();
  Node notQ = nm->mkNode(Kind::NOT, q);
  Node lemma;
  if (sInstance.getKind() == Kind::OR)
  {
    std::vector<Node> args;
    args.push_back(notQ);
    args.insert(args.end(), sInstance.begin(), sInstance.end());
    lemma = nm->mkNode(Kind::OR, args);
  }
  else if (sInstance.getKind() == Kind::CONST_BOOLEAN
           && !sInstance.getConst<bool>())
  {
    lemma = notQ;
  }
  else
  {
    lemma = nm->mkNode(Kind::OR, notQ, sInstance);
  }
  if (d_params.d_qiPermanent)
  {
    auto it = d_permanentInstances.find(lemma);
    if (it != d_permanentInstances.end())
    {
      // the instance is still asserted
      d_context.getStats().d_numInstancesRediscovered++;
      if (d_params.d_qiPermanentLocal)
      {
        d_context.reactivateInstance(it->second);
      }
      return Node::null();
    }
  }
  stat->incNumInstances();
  d_context.getStats().d_numInstances++;
  return lemma;
}

void InstancePolicy::assertLemma(TNode lemma, uint32_t generation)
{
  Trace("z3-qi-lemma") << "  lemma: " << lemma << std::endl;
  Node root;
  if (d_context.internalizeInstance(lemma, generation, root))
  {
    d_permanentInstances[lemma] = root;
  }
}

// ------------------------------------------------- the cvc5-like policy

Cvc5InstancePolicy::Cvc5InstancePolicy(QuantifierManager& qm,
                                       QuantifierServices& ctx,
                                       Params& p,
                                       bool eager)
    : InstancePolicy(qm, ctx, p),
      d_eager(eager),
      d_numInstances(0),
      d_sinceLastCheck(0)
{
}

void Cvc5InstancePolicy::insert(Fingerprint* f,
                                TNode /*pat*/,
                                uint32_t generation,
                                uint32_t /*minTopGeneration*/,
                                uint32_t /*maxTopGeneration*/)
{
  if (d_eager)
  {
    d_new.emplace_back(f, generation);
  }
  else
  {
    d_roundEntries.emplace_back(f, generation);
  }
}

bool Cvc5InstancePolicy::make(Entry& e)
{
  if (d_context.getCancelFlag())
  {
    return false;
  }
  if (d_numInstances > d_params.d_qiMaxInstances)
  {
    d_context.setReasonUnknown(
        "the maximum number of quantifier instances was reached");
    return false;
  }
  // periodically check that we did not run out of time or memory
  if (d_sinceLastCheck++ > 100)
  {
    d_sinceLastCheck = 0;
    if (d_context.resourceLimitsExceeded())
    {
      return false;
    }
  }
  if (d_context.inconsistent())
  {
    return true;
  }
  e.d_instantiated = true;
  Fingerprint* f = e.d_qb;
  TNode q = getQuantifier(f);
  QuantifierStat* stat = d_qm.getStat(q);
  if (skipSatisfied(q, stat, f->getNumArgs(), f->getArgs()))
  {
    return true;
  }
  Node lemma = mkLemma(q, stat, f->getNumArgs(), f->getArgs());
  if (lemma.isNull())
  {
    return true;
  }
  d_numInstances++;
  Trace("z3-qi") << "[instance] q" << q.getId() << " nargs " << f->getNumArgs()
                 << " gen " << e.d_generation << " newgen "
                 << (e.d_generation + 1) << std::endl;
  assertLemma(lemma, e.d_generation + 1);
  return true;
}

void Cvc5InstancePolicy::instantiate()
{
  for (Entry& e : d_new)
  {
    if (!make(e))
    {
      break;
    }
  }
  d_new.clear();
}

bool Cvc5InstancePolicy::finalCheckEh()
{
  bool result = true;
  for (size_t i = 0, n = d_roundEntries.size(); i < n; ++i)
  {
    Entry& e = d_roundEntries[i];
    if (e.d_instantiated)
    {
      continue;
    }
    d_instantiatedTrail.push_back(i);
    if (!make(e))
    {
      // Nothing more is made (cancellation or a limit), and the final check
      // stops asking: with quantifiers left, the answer is then "unknown".
      return true;
    }
    result = false;
  }
  return result;
}

void Cvc5InstancePolicy::pushScope()
{
  Assert(d_context.inconsistent() || d_new.empty());
  d_scopes.push_back(Scope{d_roundEntries.size(), d_instantiatedTrail.size()});
}

void Cvc5InstancePolicy::popScope(size_t numScopes)
{
  size_t newLvl = d_scopes.size() - numScopes;
  const Scope& s = d_scopes[newLvl];
  for (size_t i = s.d_instantiatedTrailLim, n = d_instantiatedTrail.size();
       i < n;
       ++i)
  {
    d_roundEntries[d_instantiatedTrail[i]].d_instantiated = false;
  }
  d_instantiatedTrail.resize(s.d_instantiatedTrailLim);
  d_roundEntries.resize(s.d_roundEntriesLim, Entry(nullptr, 0));
  d_new.clear();
  d_scopes.resize(newLvl);
}

void Cvc5InstancePolicy::reset()
{
  d_new.clear();
  d_roundEntries.clear();
  d_instantiatedTrail.clear();
  d_scopes.clear();
}

}  // namespace z3
}  // namespace cvc5::internal

/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Deferred blocker module
 */

#include "theory/deferred_blocker.h"

#include "options/smt_options.h"
#include "options/theory_options.h"
#include "proof/unsat_core.h"
#include "smt/set_defaults.h"
#include "theory/smt_engine_subsolver.h"

namespace cvc5::internal {

namespace theory {

DeferredBlocker::DeferredBlocker(Env& env,
                                 TheoryEngine* theoryEngine,
                                 prop::PropEngine* propEngine)
    : TheoryEngineModule(env, theoryEngine, "DeferredBlocker"),
      d_propEngine(propEngine),
      d_blockers(userContext()),
      d_filtered(userContext(), false),
      d_filteredLems(userContext()),
      d_filterIndex(userContext(), 0),
      d_bbSplit(context()),
      d_cache(userContext())
{
  // determine the options to use for the verification subsolvers we spawn
  // we start with the provided options
  d_subOptions.copyValues(options());
  // disable checking first
  smt::SetDefaults::disableChecking(d_subOptions);
  // requires unsat cores
  d_subOptions.write_smt().produceUnsatCores = true;
  d_subOptions.write_theory().deferBlock = false;
}

void DeferredBlocker::postsolve(prop::SatValue result) {}

void DeferredBlocker::check(Theory::Effort e) {}

bool DeferredBlocker::filterLemma(TNode n, InferenceId id, LemmaProperty p)
{
  // if (id==InferenceId::ARITH_BB_LEMMA ||
  // id==InferenceId::ARITH_NL_TANGENT_PLANE ||
  // id==InferenceId::ARITH_NL_INFER_BOUNDS_NT)
  if (id == InferenceId::ARITH_BB_LEMMA)
  {
    Assert(n.getKind() == Kind::OR && n[0].getNumChildren() == 2
           && n[0][1].isConst());
    Node term = n[0][0];
    if (d_bbSplit.find(term) == d_bbSplit.end())
    {
      d_bbSplit.insert(term);
      return false;
    }
    Trace("defer-block-debug") << "...filtered " << id << std::endl;
    d_filtered = true;
    d_filteredLems.push_back(n);
    return true;
  }
  return false;
}

bool DeferredBlocker::needsCandidateModel()
{
  if (!d_filtered)
  {
    return false;
  }
  Trace("defer-block-debug")
      << "DeferredBlocker: notifyCandidateModel" << std::endl;
  if (d_valuation.needCheck())
  {
    Trace("defer-block-debug") << "...already needs check" << std::endl;
    return false;
  }
  if (!d_filtered.get())
  {
    Trace("defer-block-debug") << "...didnt filter" << std::endl;
    return false;
  }
  Trace("defer-block-debug") << "...run check" << std::endl;
  Trace("defer-block") << "DeferredBlocker: notifyCandidateModel" << std::endl;
  // maybe just delaying?
  if (options().theory.deferBlockMode == options::DeferBlockMode::DELAY)
  {
    while (d_filterIndex.get() < d_filteredLems.size())
    {
      Node n = d_filteredLems[d_filterIndex.get()];
      d_filterIndex = d_filterIndex.get() + 1;
      if (d_cache.find(n) == d_cache.end())
      {
        d_cache.insert(n);
        Trace("defer-block") << "...now send " << n << std::endl;
        d_out.lemma(n, InferenceId::DEFER_BLOCK_UC);
      }
    }
    return false;
  }
  std::vector<Node> assertions;
  std::unordered_set<Node> quants;
  const LogicInfo& logicInfo = d_env.getLogicInfo();
  for (TheoryId tid = THEORY_FIRST; tid < THEORY_LAST; ++tid)
  {
    if (!logicInfo.isTheoryEnabled(tid))
    {
      continue;
    }
    // collect all assertions from theory
    for (context::CDList<Assertion>::const_iterator
             it = d_valuation.factsBegin(tid),
             itEnd = d_valuation.factsEnd(tid);
         it != itEnd;
         ++it)
    {
      Node a = (*it).d_assertion;
      assertions.push_back(a);
    }
  }
  // do subsolver check
  SubsolverSetupInfo ssi(d_env, d_subOptions);
  std::unique_ptr<SolverEngine> deferChecker;
  uint64_t timeout = 0;
  initializeSubsolver(nodeManager(), deferChecker, ssi, timeout != 0, timeout);
  // assert and check-sat
  for (const Node& a : assertions)
  {
    if (a.getKind() != Kind::FORALL)
    {
      deferChecker->assertFormula(a);
    }
  }
  Trace("defer-block-solve") << ">>> Check subsolver..." << std::endl;
  Result r = deferChecker->checkSat();
  Trace("defer-block-solve") << "...result " << r << std::endl;
  if (r.getStatus() == Result::UNSAT)
  {
    // Add the computed unsat core as a conflict, which will cause a backtrack.
    UnsatCore uc = deferChecker->getUnsatCore();
    Node ucc = nodeManager()->mkAnd(uc.getCore());
    Trace("defer-block-solve-debug") << "Unsat core is " << ucc << std::endl;
    Trace("defer-block-solve")
        << "Core size = " << uc.getCore().size() << std::endl;
    TrustNode trn = TrustNode::mkTrustLemma(ucc.notNode(), nullptr);
    d_out.trustedLemma(trn, InferenceId::DEFER_BLOCK_UC);
  }
  return false;
}

}  // namespace theory
}  // namespace cvc5::internal

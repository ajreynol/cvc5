/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of instantiation engine class
 */

#include "theory/quantifiers/ematching/instantiation_engine.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/ematching/inst_strategy_e_matching.h"
#include "theory/quantifiers/ematching/inst_strategy_e_matching_user.h"
#include "theory/quantifiers/ematching/trigger.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"

using namespace cvc5::internal::kind;
using namespace cvc5::context;
using namespace cvc5::internal::theory::quantifiers::inst;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

InstantiationEngine::InstantiationEngine(Env& env,
                                         QuantifiersState& qs,
                                         QuantifiersInferenceManager& qim,
                                         QuantifiersRegistry& qr,
                                         TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_instStrategies(),
      d_isup(),
      d_i_ag(),
      d_quants(),
      d_trdb(d_env, qs, qim, qr, tr),
      d_quant_rel(nullptr)
{
  if (options().quantifiers.relevantTriggers)
  {
    d_quant_rel.reset(new quantifiers::QuantRelevance(env));
  }
  if (options().quantifiers.eMatching)
  {
    // these are the instantiation strategies for E-matching
    // user-provided patterns
    if (options().quantifiers.userPatternsQuant != options::UserPatMode::IGNORE)
    {
      d_isup.reset(
          new InstStrategyUserPatterns(d_env, d_trdb, qs, qim, qr, tr));
      d_instStrategies.push_back(d_isup.get());
    }

    // auto-generated patterns
    d_i_ag.reset(new InstStrategyAutoGenTriggers(
        d_env, d_trdb, qs, qim, qr, tr, d_quant_rel.get()));
    d_instStrategies.push_back(d_i_ag.get());
  }
}

InstantiationEngine::~InstantiationEngine() {}

std::string InstantiationEngine::identify() const { return "ematching"; }

void InstantiationEngine::presolve()
{
  for (unsigned i = 0; i < d_instStrategies.size(); ++i)
  {
    d_instStrategies[i]->presolve();
  }
}

void InstantiationEngine::doInstantiationRound(Theory::Effort effort,
                                               ieval::TermEvaluatorMode tev)
{
  size_t lastWaiting = d_qim.numPendingLemmas();
  // iterate over an internal effort level e
  int e = 0;
  int eLimit = effort == Theory::EFFORT_LAST_CALL ? 10 : 2;
  bool finished = false;
  bool singleQuant = (tev == ieval::TermEvaluatorMode::CONFLICT
                      && !options().quantifiers.cbqiAllConflict);
  //while unfinished, try effort level=0,1,2....
  while( !finished && e<=eLimit ){
    Trace("inst-engine-debug") << "IE: Prepare instantiation (" << e << ")." << std::endl;
    finished = true;
    //instantiate each quantifier
    for (const Node& q : d_quants)
    {
      Trace("inst-engine-debug") << "IE: Instantiate " << q << "..." << std::endl;
      //int e_use = d_quantEngine->getRelevance( q )==-1 ? e - 1 : e;
      int e_use = e;
      if (e_use >= 0)
      {
        Trace("inst-engine-debug") << "inst-engine : " << q << std::endl;
        //check each instantiation strategy
        for (InstStrategy* is : d_instStrategies)
        {
          Trace("inst-engine-debug") << "Do " << is->identify() << " " << e_use << std::endl;
          InstStrategyStatus quantStatus = is->process(q, effort, e_use, tev);
          Trace("inst-engine-debug")
              << " -> unfinished= "
              << (quantStatus == InstStrategyStatus::STATUS_UNFINISHED)
              << ", conflict=" << d_qstate.isInConflict() << std::endl;
          if (d_qstate.isInConflict())
          {
            return;
          }
          else if (quantStatus == InstStrategyStatus::STATUS_UNFINISHED)
          {
            finished = false;
          }
          if (singleQuant && d_qim.hasPendingLemma())
          {
            return;
          }
        }
      }
    }
    // do not consider another level if already added lemma at this level
    if (d_qim.numPendingLemmas() > lastWaiting)
    {
      finished = true;
    }
    e++;
  }
}

bool InstantiationEngine::needsCheck( Theory::Effort e ){
  if (options().quantifiers.ematchingStratifyIEval && e==Theory::EFFORT_FULL)
  {
    return true;
  }
  return d_qstate.getInstWhenNeedsCheck(e);
}

void InstantiationEngine::reset_round(Theory::Effort e)
{
  // if not, proceed to instantiation round
  // reset the instantiation strategies
  for (unsigned i = 0; i < d_instStrategies.size(); ++i)
  {
    InstStrategy* is = d_instStrategies[i];
    is->processResetInstantiationRound(e);
  }
}

void InstantiationEngine::check(Theory::Effort e, QEffort quant_e)
{
  QuantifiersStatistics& qs = d_qstate.getStats();
  CodeTimer codeTimer(qs.d_ematching_time);
  if (quant_e != QEFFORT_STANDARD)
  {
    return;
  }
  beginCallDebug();
  // collect all active quantified formulas belonging to this
  bool quantActive = false;
  d_quants.clear();
  FirstOrderModel* m = d_treg.getModel();
  size_t nquant = m->getNumAssertedQuantifiers();
  for (size_t i = 0; i < nquant; i++)
  {
    Node q = m->getAssertedQuantifier(i, true);
    if (shouldProcess(q) && m->isQuantifierActive(q))
    {
      quantActive = true;
      d_quants.push_back(q);
    }
  }
  Trace("inst-engine-debug")
      << "InstEngine: check: # asserted quantifiers " << d_quants.size() << "/";
  Trace("inst-engine-debug") << nquant << " " << quantActive << std::endl;
  if (quantActive)
  {
    size_t lastWaiting = d_qim.numPendingLemmas();
    size_t starti, endi;
    if (options().quantifiers.ematchingStratifyIEval && e==Theory::EFFORT_FULL)
    {
      starti = 0;
      endi = d_qstate.getInstWhenNeedsCheck(e) ? 2 : 1;
    }
    else
    {
      starti = 2;
      endi = 2;
    }
    for (size_t i = starti; i <= endi; i++)
    {
      ieval::TermEvaluatorMode tev =
          (i == 0 ? ieval::TermEvaluatorMode::CONFLICT
                  : (i == 1 ? ieval::TermEvaluatorMode::PROP
                            : ieval::TermEvaluatorMode::NO_ENTAIL));
      doInstantiationRound(e, tev);
      if (d_qstate.isInConflict() || d_qim.hasPendingLemma())
      {
        Assert(d_qim.numPendingLemmas() > lastWaiting);
        if (TraceIsOn("inst-engine"))
        {
          Trace("inst-engine")
              << "Added lemmas = " << (d_qim.numPendingLemmas() - lastWaiting)
              << ", from ieval effort " << tev;
          if (d_qstate.isInConflict())
          {
            Trace("inst-engine") << ", in conflict";
          }
          Trace("inst-engine") << std::endl;
        }
        qs.d_ematchingLevel << tev;
        break;
      }
    }
  }
  else
  {
    d_quants.clear();
  }
  endCallDebug();
}

bool InstantiationEngine::checkCompleteFor(CVC5_UNUSED Node q)
{
  // TODO?
  return false;
}

void InstantiationEngine::checkOwnership(Node q)
{
  if (options().quantifiers.userPatternsQuant == options::UserPatMode::STRICT
      && q.getNumChildren() == 3)
  {
    // if strict triggers, take ownership of this quantified formula
    if (QuantAttributes::hasPattern(q))
    {
      d_qreg.setOwner(q, this, 1);
    }
  }
}

void InstantiationEngine::registerQuantifier(Node q)
{
  if (!shouldProcess(q))
  {
    return;
  }
  if (d_quant_rel)
  {
    d_quant_rel->registerQuantifier(q);
  }
  // take into account user patterns
  if (q.getNumChildren() == 3)
  {
    Node subsPat = d_qreg.substituteBoundVariablesToInstConstants(q[2], q);
    // add patterns
    for (const Node& p : subsPat)
    {
      if (p.getKind() == Kind::INST_PATTERN)
      {
        addUserPattern(q, p);
      }
      else if (p.getKind() == Kind::INST_NO_PATTERN)
      {
        addUserNoPattern(q, p);
      }
    }
  }
}

void InstantiationEngine::addUserPattern(Node q, Node pat)
{
  if (d_isup)
  {
    d_isup->addUserPattern(q, pat);
  }
}

void InstantiationEngine::addUserNoPattern(Node q, Node pat)
{
  if (d_i_ag)
  {
    d_i_ag->addUserNoPattern(q, pat);
  }
}

bool InstantiationEngine::shouldProcess(Node q)
{
  if (!d_qreg.hasOwnership(q, this))
  {
    return false;
  }
  // also ignore internal quantifiers
  QuantAttributes& qattr = d_qreg.getQuantAttributes();
  if (qattr.isQuantBounded(q))
  {
    return false;
  }
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

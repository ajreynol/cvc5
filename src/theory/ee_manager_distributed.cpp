/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Management of a distributed approach for equality sharing.
 */

#include "theory/ee_manager_distributed.h"

#include "options/theory_options.h"
#include "smt/env.h"
#include "theory/quantifiers_engine.h"
#include "theory/shared_solver.h"
#include "theory/theory_engine.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {

EqEngineManagerDistributed::EqEngineManagerDistributed(Env& env,
                                                       TheoryEngine& te,
                                                       SharedSolver& shs)
    : EqEngineManager(env, te, shs),
      d_masterEENotify(nullptr),
      d_shareUfDt(false)
{
}

EqEngineManagerDistributed::~EqEngineManagerDistributed() {}

void EqEngineManagerDistributed::initializeTheories()
{
  context::Context* c = context();
  // initialize the shared solver
  EeSetupInfo esis;
  if (d_sharedSolver.needsEqualityEngine(esis))
  {
    // allocate an equality engine for the shared terms database
    d_stbEqualityEngine.reset(allocateEqualityEngine(esis, c));
    d_sharedSolver.setEqualityEngine(d_stbEqualityEngine.get());
  }
  else
  {
    Unhandled() << "Expected shared solver to use equality engine";
  }

  const LogicInfo& logicInfo = d_env.getLogicInfo();
  if (logicInfo.isQuantified())
  {
    // construct the master equality engine
    Assert(d_masterEqualityEngine == nullptr);
    QuantifiersEngine* qe = d_te.getQuantifiersEngine();
    Assert(qe != nullptr);
    d_masterEENotify.reset(new quantifiers::MasterNotifyClass(qe));
    d_masterEqualityEngine = std::make_unique<eq::EqualityEngine>(
        d_env, c, *d_masterEENotify.get(), "theory::master", false);
  }
  // Allocate the equality engine that the theories of UF and datatypes share,
  // if we are asked to and they can.
  EeSetupInfo esiUf, esiDt;
  d_shareUfDt = computeShareUfDt(esiUf, esiDt);
  if (d_shareUfDt)
  {
    d_ufDtNotify = std::make_unique<SharedUfDtNotifyClass>(
        d_env, esiUf.d_notify, esiDt.d_notify);
    // The engine is set up as the theory of UF asked for, other than its
    // notify class and its name.
    EeSetupInfo esiShared = esiUf;
    esiShared.d_notify = d_ufDtNotify.get();
    esiShared.d_name = "theory::uf-dt::ee";
    d_ufDtEqualityEngine.reset(allocateEqualityEngine(esiShared, c));
    if (d_masterEqualityEngine != nullptr)
    {
      d_ufDtEqualityEngine->setMasterEqualityEngine(
          d_masterEqualityEngine.get());
    }
  }
  // allocate equality engines per theory
  for (TheoryId theoryId = theory::THEORY_FIRST;
       theoryId != theory::THEORY_LAST;
       ++theoryId)
  {
    Theory* t = d_te.theoryOf(theoryId);
    if (t == nullptr)
    {
      // theory not active, skip
      continue;
    }
    // always allocate an object in d_einfo here
    EeTheoryInfo& eet = d_einfo[theoryId];
    EeSetupInfo esi;
    if (!t->needsEqualityEngine(esi))
    {
      // the theory said it doesn't need an equality engine, skip
      continue;
    }
    if (esi.d_useMaster)
    {
      // the theory said it wants to use the master equality engine
      eet.d_usedEe = d_masterEqualityEngine.get();
      continue;
    }
    if (d_shareUfDt && (theoryId == THEORY_UF || theoryId == THEORY_DATATYPES))
    {
      // the theory uses the equality engine it shares with the other one
      eet.d_usedEe = d_ufDtEqualityEngine.get();
      continue;
    }
    // allocate the equality engine
    eet.d_allocEe.reset(allocateEqualityEngine(esi, c));
    // the theory uses the equality engine
    eet.d_usedEe = eet.d_allocEe.get();
    // if there is a master equality engine
    if (d_masterEqualityEngine != nullptr)
    {
      // set the master equality engine of the theory's equality engine
      eet.d_allocEe->setMasterEqualityEngine(d_masterEqualityEngine.get());
    }
  }
}

bool EqEngineManagerDistributed::computeShareUfDt(EeSetupInfo& esiUf,
                                                  EeSetupInfo& esiDt)
{
  if (!options().theory.eeShareUfDt)
  {
    return false;
  }
  Theory* tuf = d_te.theoryOf(THEORY_UF);
  Theory* tdt = d_te.theoryOf(THEORY_DATATYPES);
  if (tuf == nullptr || tdt == nullptr)
  {
    // one of the two theories is not active
    return false;
  }
  if (!tuf->needsEqualityEngine(esiUf) || !tdt->needsEqualityEngine(esiDt))
  {
    // one of the two theories does not want an equality engine
    return false;
  }
  if (esiUf.d_useMaster || esiDt.d_useMaster)
  {
    // one of the two theories wants the master equality engine
    return false;
  }
  if (esiUf.d_notify == nullptr || esiDt.d_notify == nullptr)
  {
    // we can only dispatch notifications if both theories have a notify class
    return false;
  }
  if (esiUf.d_constantsAreTriggers != esiDt.d_constantsAreTriggers)
  {
    // the two theories disagree on how the engine should be constructed
    return false;
  }
  Trace("ee-distributed")
      << "Theories of UF and datatypes share one equality engine" << std::endl;
  return true;
}

EqEngineManagerDistributed::SharedUfDtNotifyClass::SharedUfDtNotifyClass(
    Env& env,
    eq::EqualityEngineNotify* ufNotify,
    eq::EqualityEngineNotify* dtNotify)
    : d_env(env), d_ufNotify(ufNotify), d_dtNotify(dtNotify)
{
}

eq::EqualityEngineNotify*
EqEngineManagerDistributed::SharedUfDtNotifyClass::notifyFor(TNode t) const
{
  return t.getType().isDatatype() ? d_dtNotify : d_ufNotify;
}

bool EqEngineManagerDistributed::SharedUfDtNotifyClass::
    eqNotifyTriggerPredicate(TNode predicate, bool value)
{
  // the theory that is responsible for the predicate registered it
  eq::EqualityEngineNotify* notify =
      d_env.theoryOf(predicate) == THEORY_DATATYPES ? d_dtNotify : d_ufNotify;
  return notify->eqNotifyTriggerPredicate(predicate, value);
}

bool EqEngineManagerDistributed::SharedUfDtNotifyClass::
    eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value)
{
  // the tag is the identifier of the theory that registered the trigger term
  eq::EqualityEngineNotify* notify =
      tag == THEORY_DATATYPES ? d_dtNotify : d_ufNotify;
  return notify->eqNotifyTriggerTermEquality(tag, t1, t2, value);
}

void EqEngineManagerDistributed::SharedUfDtNotifyClass::
    eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  // the theory that is responsible for the terms reports the conflict, which
  // it explains using the shared equality engine
  notifyFor(t1)->eqNotifyConstantTermMerge(t1, t2);
}

void EqEngineManagerDistributed::SharedUfDtNotifyClass::eqNotifyNewClass(
    TNode t)
{
  d_ufNotify->eqNotifyNewClass(t);
  d_dtNotify->eqNotifyNewClass(t);
}

void EqEngineManagerDistributed::SharedUfDtNotifyClass::eqNotifyMerge(TNode t1,
                                                                      TNode t2)
{
  d_ufNotify->eqNotifyMerge(t1, t2);
  d_dtNotify->eqNotifyMerge(t1, t2);
}

void EqEngineManagerDistributed::SharedUfDtNotifyClass::eqNotifyDisequal(
    TNode t1, TNode t2, TNode reason)
{
  d_ufNotify->eqNotifyDisequal(t1, t2, reason);
  d_dtNotify->eqNotifyDisequal(t1, t2, reason);
}

bool EqEngineManagerDistributed::usesSharedUfDtEqualityEngine() const
{
  return d_shareUfDt;
}

void EqEngineManagerDistributed::notifyModel(CVC5_UNUSED bool incomplete)
{
  // should have a consistent master equality engine
  if (d_masterEqualityEngine.get() != nullptr)
  {
    AlwaysAssert(d_masterEqualityEngine->consistent());
  }
}

}  // namespace theory
}  // namespace cvc5::internal

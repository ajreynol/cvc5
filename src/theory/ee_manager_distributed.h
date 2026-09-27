/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Management of a distributed approach for equality engines over
 * all theories.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__EE_MANAGER_DISTRIBUTED__H
#define CVC5__THEORY__EE_MANAGER_DISTRIBUTED__H

#include <memory>

#include "theory/ee_manager.h"
#include "theory/ee_setup_info.h"
#include "theory/quantifiers/master_eq_notify.h"

namespace cvc5::internal {
namespace theory {

namespace eq {
class EqualityEngine;
}

/**
 * The (distributed) equality engine manager. This encapsulates an architecture
 * in which all theories maintain their own copy of an equality engine.
 *
 * This class is not responsible for actually initializing equality engines in
 * theories (since this class does not have access to the internals of Theory).
 * Instead, it is only responsible for the construction of the equality
 * engine objects themselves. TheoryEngine is responsible for querying this
 * class during finishInit() to determine the equality engines to pass to each
 * theories based on getEeTheoryInfo.
 *
 * This class is also responsible for setting up the master equality engine,
 * which is used as a special communication channel to quantifiers engine (e.g.
 * for ensuring quantifiers E-matching is aware of terms from all theories).
 */
class EqEngineManagerDistributed : public EqEngineManager
{
 public:
  EqEngineManagerDistributed(Env& env, TheoryEngine& te, SharedSolver& shs);
  ~EqEngineManagerDistributed();
  /**
   * Initialize theories. This method allocates unique equality engines
   * per theories and connects them to a master equality engine.
   */
  void initializeTheories() override;
  /** Notify model */
  void notifyModel(bool incomplete) override;
  /** Do the theories of UF and datatypes share one equality engine? */
  bool usesSharedUfDtEqualityEngine() const override;

 private:
  /**
   * Notify class for an equality engine that is shared by the theories of UF
   * and datatypes, allocated when the option ee-share-uf-dt is enabled. It
   * dispatches each notification from the shared equality engine to the notify
   * class of one or both of those two theories.
   *
   * Notifications that a theory would have received for every term in its own
   * equality engine (new class, merge, disequal) are sent to both, since in
   * this architecture an equality engine issues them unconditionally and both
   * theories already filter the terms they act on.
   *
   * The three notifications that lead to a propagation or a conflict name one
   * interested theory and are sent to it alone, so that each theory still
   * reports what it would have reported with an equality engine of its own: a
   * trigger term carries the identifier of the theory that registered it, and
   * a trigger predicate and a constant merge are classified by term. Either
   * theory may then be asked to explain a fact the other one was sent, which
   * TheoryEngine::getExplanation handles.
   */
  class SharedUfDtNotifyClass : public eq::EqualityEngineNotify
  {
   public:
    SharedUfDtNotifyClass(Env& env,
                          eq::EqualityEngineNotify* ufNotify,
                          eq::EqualityEngineNotify* dtNotify);
    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override;
    bool eqNotifyTriggerTermEquality(TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override;
    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override;
    void eqNotifyNewClass(TNode t) override;
    void eqNotifyMerge(TNode t1, TNode t2) override;
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override;

   private:
    /**
     * The notify class of the theory that is responsible for t, which is
     * datatypes if t is of datatype type and UF otherwise.
     */
    eq::EqualityEngineNotify* notifyFor(TNode t) const;
    /** Reference to the environment */
    Env& d_env;
    /** The notify class of the theory of UF */
    eq::EqualityEngineNotify* d_ufNotify;
    /** The notify class of the theory of datatypes */
    eq::EqualityEngineNotify* d_dtNotify;
  };
  /**
   * Determine whether the theories of UF and datatypes can share one equality
   * engine. If so, the setup information of each is stored in the arguments.
   */
  bool computeShareUfDt(EeSetupInfo& esiUf, EeSetupInfo& esiDt);
  /** The master equality engine notify class */
  std::unique_ptr<quantifiers::MasterNotifyClass> d_masterEENotify;
  /** The master equality engine. */
  std::unique_ptr<eq::EqualityEngine> d_masterEqualityEngine;
  /** The equality engine of the shared solver / shared terms database. */
  std::unique_ptr<eq::EqualityEngine> d_stbEqualityEngine;
  /** The notify class of the shared UF/datatypes equality engine, if any */
  std::unique_ptr<SharedUfDtNotifyClass> d_ufDtNotify;
  /** The equality engine shared by UF and datatypes, if any */
  std::unique_ptr<eq::EqualityEngine> d_ufDtEqualityEngine;
  /** Whether UF and datatypes share an equality engine */
  bool d_shareUfDt;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__EE_MANAGER_DISTRIBUTED__H */

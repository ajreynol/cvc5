/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Notification class for the master equality engine
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__MASTER_EQ_NOTIFY__H
#define CVC5__THEORY__QUANTIFIERS__MASTER_EQ_NOTIFY__H

#include <memory>
#include <vector>

#include "theory/uf/equality_engine_notify.h"

namespace cvc5::internal {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

/** notify class for master equality engine */
class MasterNotifyClass : public theory::eq::EqualityEngineNotify
{
 public:
  MasterNotifyClass(QuantifiersEngine* qe);
  /**
   * Add a listener, which receives the new class, merge and disequality
   * notifications of the master equality engine in addition to this class.
   * Used by modules that observe the master equality engine directly, e.g.
   * eager E-matching. The listener must outlive this object.
   */
  void addListener(theory::eq::EqualityEngineNotify* n);
  /**
   * Called when a new equivalence class is created in the master equality
   * engine.
   */
  void eqNotifyNewClass(TNode t) override;

  bool eqNotifyTriggerPredicate(CVC5_UNUSED TNode predicate,
                                CVC5_UNUSED bool value) override
  {
    return true;
  }
  bool eqNotifyTriggerTermEquality(CVC5_UNUSED TheoryId tag,
                                   CVC5_UNUSED TNode t1,
                                   CVC5_UNUSED TNode t2,
                                   CVC5_UNUSED bool value) override
  {
    return true;
  }
  void eqNotifyConstantTermMerge(CVC5_UNUSED TNode t1,
                                 CVC5_UNUSED TNode t2) override
  {
  }
  void eqNotifyMerge(CVC5_UNUSED TNode t1, CVC5_UNUSED TNode t2) override;
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override;

 private:
  /** Pointer to quantifiers engine */
  QuantifiersEngine* d_quantEngine;
  /** The additional listeners */
  std::vector<theory::eq::EqualityEngineNotify*> d_listeners;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__MASTER_EQ_NOTIFY__H */

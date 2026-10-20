/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The equalities of cvc5's theories, for the shadow of the ported core.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__QUANTIFIERS__SHADOW_FEED_H
#define CVC5__Z3__QUANTIFIERS__SHADOW_FEED_H

#include <cstdint>
#include <utility>
#include <vector>

#include "context/cdhashmap.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/uf/equality_engine_notify.h"

namespace cvc5::internal {

namespace theory::eq {
class EqualityEngine;
}

namespace z3 {

class SharedBackend;

/**
 * Feeds the E-graph of the ported core, a shadow of cvc5's own theories,
 * with the equalities those theories derive, so that the core matches modulo
 * them. They come from cvc5's master equality engine, which collects the terms
 * and merges of the equality engines of all theories, as it does for cvc5's
 * quantifiers engine.
 *
 * The feed keeps, for each class of the master equality engine, a term the
 * core has internalized, and when two such classes merge, it merges their
 * terms in the core.
 *
 * The master equality engine keeps no reasons, so the core cannot explain
 * these merges (ExternalEqJustification).
 */
class ShadowFeed : protected EnvObj, public theory::eq::EqualityEngineNotify
{
 public:
  ShadowFeed(Env& env, SharedBackend& backend);
  ~ShadowFeed();
  /** Set the master equality engine, which then notifies this. */
  void setMasterEqualityEngine(theory::eq::EqualityEngine* ee)
  {
    d_master = ee;
  }
  /**
   * Queue in the core the merges notified since the last call, and those of
   * the terms the core internalized since then, for its next propagation.
   */
  void apply();
  /** The SAT context popped: the merges notified and not applied are void. */
  void notifyPop() { d_pending.clear(); }

  //---------------------------------------------- EqualityEngineNotify
  bool eqNotifyTriggerPredicate(TNode predicate, bool value) override;
  bool eqNotifyTriggerTermEquality(theory::TheoryId tag,
                                   TNode t1,
                                   TNode t2,
                                   bool value) override;
  void eqNotifyConstantTermMerge(TNode t1, TNode t2) override;
  void eqNotifyNewClass(TNode t) override;
  void eqNotifyMerge(TNode t1, TNode t2) override;
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override;

 private:
  /** The term of the core recorded for the representative rep, or null. */
  Node coreTermOf(TNode rep) const;
  /** Merge a and b, both internalized in the core, there. */
  void merge(TNode a, TNode b);

  /** The ported core. */
  SharedBackend& d_backend;
  /** cvc5's master equality engine, or null. */
  theory::eq::EqualityEngine* d_master;
  /**
   * For a representative of the master equality engine, a term of the core
   * in its class, in the SAT context.
   */
  context::CDHashMap<Node, Node> d_coreTerm;
  /**
   * How many of the terms the core internalized were looked up in the
   * master equality engine. In the SAT context, as the core's scopes are.
   */
  context::CDO<size_t> d_coreIdx;
  /**
   * The merges notified since the last apply, as the representative that
   * survived and the one that was merged into it.
   */
  std::vector<std::pair<Node, Node>> d_pending;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIERS__SHADOW_FEED_H */

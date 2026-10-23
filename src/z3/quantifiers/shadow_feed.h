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

class HostCore;

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
 * these merges, and it does not need to: the core keeps no explanations.
 */
class ShadowFeed : protected EnvObj, public theory::eq::EqualityEngineNotify
{
 public:
  ShadowFeed(Env& env, HostCore& core);
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
  /**
   * The SAT context popped to lvl: the merges notified above lvl and not
   * applied are void. With --z3-mirror=equalities, the core's equalities come
   * only from the master equality engine, whose merges at or below lvl may
   * have been applied to the core above it, where the core undoes them: the
   * next apply then applies them again (see d_applied).
   */
  void notifyPop(uint32_t lvl);

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
  Node coreTermOf(TNode rep);
  /** Merge a and b, both internalized in the core, there. */
  void merge(TNode a, TNode b);
  /**
   * Record the term c of the core for the representative rep (if isMap) or
   * merge the terms rep and c of the core, for a merge the master equality
   * engine made at level lvl.
   */
  void applyMerge(TNode rep, TNode c, bool isMap, uint32_t lvl);

 public:
  /** TEMPORARY diagnostic */
  void debugCheck();
  void debugCheckCore();

 private:

  /** The core under cvc5's prop engine, which owns the feed. */
  HostCore& d_core;
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
  struct Pending
  {
    Node d_r1;
    Node d_r2;
    /** the level of the SAT context of the merge */
    uint32_t d_lvl;
  };
  std::vector<Pending> d_pending;
  /** A change applyMerge made, see there. */
  struct Applied
  {
    Node d_a;
    Node d_b;
    bool d_isMap;
    /** the level of the merge in the master equality engine */
    uint32_t d_lvl;
    /** the level of the SAT context when it was applied */
    uint32_t d_appliedLvl;
  };
  /**
   * With --z3-mirror=equalities, the changes applied, by increasing level
   * applied, and those a pop undid while the master equality engine keeps
   * them, to apply again.
   */
  std::vector<Applied> d_applied;
  std::vector<Applied> d_reapply;
  /** Whether d_applied is kept, see there. */
  bool d_replay;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIERS__SHADOW_FEED_H */

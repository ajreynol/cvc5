/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Eager E-matching, driven by notifications from the master equality engine.
 *
 * This module is the analogue of z3's smt::quantifier_manager together with
 * its default plugin (smt/smt_quantifier.cpp): it owns the matching abstract
 * machines, decides which patterns are matched eagerly and which are left for
 * final check, and hands the matches to the instance queue. It does not use
 * any of cvc5's existing instantiation machinery, which continues to run
 * alongside it.
 *
 * See theory/quantifiers/eager/README.md.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__EAGER_INST_ENGINE_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__EAGER_INST_ENGINE_H

#include <memory>
#include <unordered_set>

#include "theory/quantifiers/eager/egraph.h"
#include "theory/quantifiers/eager/inner_smt_solver.h"
#include "theory/quantifiers/eager/inst_queue.h"
#include "theory/quantifiers/eager/mam.h"
#include "theory/quantifiers/eager/trail.h"
#include "theory/quantifiers/quant_module.h"
#include "theory/uf/equality_engine_notify.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

class EagerInstEngine;

/**
 * The notification class we register with the master equality engine. z3 gets
 * the same two events from smt::context, as mam::relevant_eh and
 * mam::add_eq_eh.
 */
class EagerEqNotify : public theory::eq::EqualityEngineNotify
{
 public:
  EagerEqNotify(EagerInstEngine& e) : d_engine(e) {}
  void eqNotifyNewClass(TNode t) override;
  void eqNotifyMerge(TNode t1, TNode t2) override;
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override;
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

 private:
  EagerInstEngine& d_engine;
};

/**
 * Eager E-matching.
 */
class EagerInstEngine : public QuantifiersModule, public InstanceSink
{
 public:
  EagerInstEngine(Env& env,
                  QuantifiersState& qs,
                  QuantifiersInferenceManager& qim,
                  QuantifiersRegistry& qr,
                  TermRegistry& tr);
  ~EagerInstEngine();

  /**
   * The notification class to register with the master equality engine. It
   * lives as long as this module.
   */
  theory::eq::EqualityEngineNotify* getEqNotify() { return &d_notify; }

  //------------------------------------------- notifications
  /** z3: mam::relevant_eh, called when a term enters the e-graph */
  void notifyNewClass(TNode t);
  /** z3: mam::add_eq_eh, called when two classes are merged */
  void notifyMerge(TNode t1, TNode t2);
  /** Called when two classes are asserted disequal */
  void notifyDisequal(TNode t1, TNode t2, TNode reason);
  //--------------------------------------- end notifications

  //------------------------------------------- QuantifiersModule
  bool needsCheck(Theory::Effort e) override;
  void check(Theory::Effort e, QEffort quantE) override;
  /** z3: default_qm_plugin::assign_eh, which compiles the patterns of q */
  void assertNode(Node q) override;
  void presolve() override;
  std::string identify() const override { return "eager-inst"; }
  //--------------------------------------- end QuantifiersModule

  //---------------------------------------------------- InstanceSink
  /**
   * The bring-up sink, used with --eager-inst-output=lemma: forward the
   * instance to cvc5's lemma channel instead of the inner solver.
   */
  void addInstance(TNode q,
                   const std::vector<Node>& terms,
                   TNode lemma,
                   uint32_t generation) override;
  //------------------------------------------------ end InstanceSink

 private:
  /**
   * Align our trail with the current context level, pushing or popping scopes
   * as needed. Called at the start of every entry point; see README.md section
   * 3.2.
   */
  void syncScopes();
  /** Run the matcher and process what it found */
  void doMatch();
  /** The multi-patterns of q, from its annotation */
  void getPatterns(TNode q, std::vector<Node>& pats) const;
  /** Print the statistics under -t eager-inst */
  void traceStats() const;

  /** The notification class */
  EagerEqNotify d_notify;
  /** The trail shared by all of the components below */
  Trail d_trail;
  /** The e-graph mirror */
  EGraph d_egraph;
  /** The eager matcher. z3: default_qm_plugin::m_mam */
  Mam d_mam;
  /**
   * The matcher for the patterns that are only used at final check. z3:
   * default_qm_plugin::m_lazy_mam.
   */
  Mam d_lazyMam;
  /** The instance queue */
  InstQueue d_queue;
  /** The inner SMT solver */
  InnerSmtSolver d_inner;
  /** The quantified formulas whose patterns have been compiled */
  std::unordered_set<Node> d_asserted;
  /** The scope level our trail is at */
  size_t d_trailLevel;
  /**
   * The number of times the final-check matcher has been run, as z3 bounds
   * this by qi.max_lazy_multipattern_matching.
   */
  uint32_t d_numLazyMatches;
  /** Whether to send instances to cvc5's lemma channel */
  bool d_outputLemmas;
  /** Whether to run the matcher from the notifications */
  bool d_matchOnNotify;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif

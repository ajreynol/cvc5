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
#include <set>
#include <unordered_set>

#include "context/cdhashmap.h"
#include "context/cdo.h"
#include "theory/quantifiers/eager/egraph.h"
#include "theory/quantifiers/eager/inner_smt_solver.h"
#include "theory/quantifiers/eager/inst_queue.h"
#include "theory/quantifiers/eager/mam.h"
#include "theory/quantifiers/eager/pattern_inference.h"
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
class EagerInstEngine : public QuantifiersModule,
                        public InstanceSink,
                        public InstanceEvaluator
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

  /**
   * Run the matcher and queue what it finds. Called once per round of the
   * propagation fixpoint of the theory engine, which is where z3 calls its
   * quantifier manager (context::propagate). Produces no output.
   */
  void propagate(Theory::Effort e);
  /**
   * Send what the matcher found to the rest of the solver: the instantiations
   * of the pending instances, or, with --eager-inst-output=inner, the conflicts
   * and propagations of the inner SMT solver. Called from check, so that output
   * happens at a point where cvc5 expects it.
   */
  void flush(Theory::Effort e);

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
   * With --eager-inst-output=inst, the default, the instance is queued and
   * turned into an instantiation of q at the next check; with
   * --eager-inst-output=lemma the lemma is sent to the lemma channel directly.
   */
  void addInstance(TNode q,
                   const std::vector<Node>& terms,
                   TNode lemma,
                   uint32_t generation) override;
  //------------------------------------------------ end InstanceSink

  //---------------------------------------------------- InstanceEvaluator
  /**
   * With --eager-inst-quick-check, an instance is only created if its body is
   * already false under the current assignment, or, in the prop mode, if it is
   * one literal away from being false.
   */
  bool isUseful(TNode body) override;
  //------------------------------------------------ end InstanceEvaluator

 private:
  /**
   * Align our trail with the current context level, pushing or popping scopes
   * as needed. Called at the start of every entry point; see README.md section
   * 3.2.
   */
  void syncScopes();
  /** The multi-patterns of q, from its annotation */
  void getPatterns(TNode q, std::vector<Node>& pats) const;
  /** Whether another contribution is allowed */
  bool mayContribute() const
  {
    return d_maxContributions == 0 || d_numContributed < d_maxContributions;
  }
  /**
   * Three-valued evaluation of the formula n under the current assignment:
   * 1 if true, -1 if false, 0 if not determined. Counts the leaves that are
   * not determined in numUnknown, which the prop mode needs.
   */
  int evalFormula(TNode n, size_t& numUnknown) const;
  /** Three-valued evaluation of an atom */
  int evalAtom(TNode n) const;
  /** Print the statistics under -t eager-inst */
  void traceStats() const;
  /**
   * Register the terms of the facts that have been asserted since the last
   * call as candidates for matching. This is our stand-in for the calls z3
   * makes to mam::relevant_eh: cvc5 has no term-level relevancy propagation,
   * and RelevanceManager::isRelevant is defined on literals and only during a
   * full effort check, so the available notion is the one cvc5's own term
   * database uses (TermDb::reset), namely the terms that occur in an asserted
   * fact of some theory.
   */
  void sweepFacts();
  /** Turn the pending instances into instantiations */
  void flushInstances();
  /** Report what the inner SMT solver derived */
  void flushInner();

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
  /** Pattern inference, for the quantifiers with no usable annotation */
  PatternInference d_patInfer;
  /** The instance queue */
  InstQueue d_queue;
  /**
   * The inner SMT solver, allocated only with --eager-inst-output=inner. It is
   * off the default path: the instances of eager E-matching go to cvc5 as
   * instantiations, as they do in z3, so that cvc5 processes them, their terms
   * reach the equality engine, and the matcher sees them. See README.md
   * section 6.3.
   */
  std::unique_ptr<InnerSmtSolver> d_inner;
  /** The quantified formulas whose patterns have been compiled */
  std::unordered_set<Node> d_asserted;
  /** Whether matching is restricted to the terms of the asserted facts */
  bool d_relevantOnly;
  /** Which instances are worth creating */
  options::EagerInstQuickCheckMode d_quickCheck;
  /**
   * How many facts of each theory sweepFacts has seen, keyed on the theory id.
   * Context dependent, as the fact lists themselves are, so that a pop takes
   * the cursor back to where it was at that level.
   */
  context::CDHashMap<uint32_t, size_t> d_factCursor;
  /** The scope level our trail is at */
  size_t d_trailLevel;
  /**
   * The level of the last call to syncScopes, as seen from the current
   * context. It is less than d_trailLevel when the context popped below
   * d_trailLevel and pushed back since then, which the level alone does not
   * show.
   */
  context::CDO<size_t> d_syncedLevel;
  /**
   * The number of times the final-check matcher has been run, as z3 bounds
   * this by qi.max_lazy_multipattern_matching.
   */
  uint32_t d_numLazyMatches;
  /** Whether to send instances to cvc5's lemma channel */
  bool d_outputLemmas;
  /** Whether the instances become instantiations, the default */
  bool d_outputInst;
  /** Whether the instances are given to the inner SMT solver */
  bool d_useInner;
  /** One instance waiting to be turned into an instantiation */
  struct PendingInst
  {
    Node d_quant;
    std::vector<Node> d_terms;
  };
  /** The instances the matcher found and that have not been added yet */
  std::vector<PendingInst> d_pendingInsts;
  /** Whether to run the matcher from the notifications */
  bool d_matchOnNotify;
  /** The number of contributions allowed in total, 0 for no limit */
  uint64_t d_maxContributions;
  /** How many have been made */
  uint64_t d_numContributed;
  /**
   * What has already been contributed at the current scope. A conflict is
   * rederived every round, because the round that found it is undone to keep
   * the state consistent, so without this the same instantiation is sent over
   * and over.
   */
  std::set<std::pair<Node, std::vector<Node>>> d_emittedInst;
  std::unordered_set<Node> d_emittedConflict;

};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif

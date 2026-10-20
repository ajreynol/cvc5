/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The quantifiers engine of the ported Z3 core.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__QUANTIFIERS__Z3_QUANTIFIERS_ENGINE_H
#define CVC5__Z3__QUANTIFIERS__Z3_QUANTIFIERS_ENGINE_H

#include <memory>

#include "theory/quantifiers_engine.h"
#include "z3/quantifiers/host_core.h"
#include "z3/util/assertion_target.h"
#include "z3/relevancy/relevancy_tracker.h"
#include "z3/quantifiers/shared_backend.h"

namespace cvc5::internal {

namespace theory {
class OutputChannel;
}

namespace z3 {

/**
 * The quantifiers engine of cvc5's quantifiers theory with --z3, which owns
 * the ported core. cvc5's own theories do the ground reasoning, with their
 * equality engines and theory combination; the core matches and instantiates
 * over a shadow of the ground state:
 * - it receives every literal the SAT solver asserts, for its E-graph and
 *   for relevancy (RelevancyTracker), and the equalities cvc5's theories
 *   derive, through the master equality engine, which notifies this engine
 *   (ShadowFeed);
 * - it sends lemmas only (instances, conflicts and splits), which need no
 *   explanation, and reports no propagations;
 * - the formulas it asserts go through cvc5's preprocessing first.
 *
 * None of the modules of cvc5's quantifiers engine are made. What it keeps of
 * the native engine is skolemization: a quantified formula the core assigns
 * false is skolemized with the lemma of cvc5's Skolemize utility, which the
 * core asserts as it does an instance.
 */
class Z3QuantifiersEngine : public theory::QuantifiersEngine,
                            public HostCoreOutput,
                            public AssertionTarget
{
 public:
  Z3QuantifiersEngine(Env& env,
                      theory::OutputChannel& out,
                      theory::quantifiers::QuantifiersState& qs,
                      theory::quantifiers::QuantifiersRegistry& qr,
                      theory::quantifiers::TermRegistry& tr,
                      theory::quantifiers::QuantifiersInferenceManager& qim,
                      ProofNodeManager* pnm);
  ~Z3QuantifiersEngine();
  //---------------------- AssertionTarget, for Z3AssertionPreparation
  void resetCore(TheoryEngine* te) override;
  QuantifierNormalizer& getNormalizer() override;
  Node preprocessForTheories(TNode n, std::vector<Node>& defs) override;
  void assertPrepared(TNode n) override;
  /**
   * The literals the SAT solver asserted in the current context, or null
   * before finishInit (in quantifier-free logics).
   */
  const context::CDList<Node>* getAssertedLiterals() const;

  //--------------------------------------------- the quantifiers engine
  /** None: the model builder of TheoryEngine is the default one. */
  theory::quantifiers::QModelBuilder* getModelBuilder() const override
  {
    return nullptr;
  }
  void presolve() override;
  void ppNotifyAssertions(
      CVC5_UNUSED const std::vector<Node>& assertions) override
  {
  }
  /** Run the core, at standard and full effort. */
  void check(theory::Theory::Effort e) override;
  void notifyCombineTheories() override {}
  void preRegisterQuantifier(Node q) override;
  /**
   * Nothing: the core takes the quantified formulas asserted to this engine
   * with every other literal, from the relevancy tracker.
   */
  void assertFact(TNode atom, bool pol, TNode fact) override;
  void eqNotifyNewClass(CVC5_UNUSED TNode t) override {}
  /** Give the merge to the feed of the shadow. */
  void eqNotifyMerge(TNode t1, TNode t2) override;

  //------------------------- the commands, which the core does not support
  void getInstantiatedQuantifiedFormulas(std::vector<Node>& qs) override;
  void getInstantiationTermVectors(
      Node q, std::vector<std::vector<Node>>& tvecs) override;
  void getInstantiationTermVectors(
      std::map<Node, std::vector<std::vector<Node>>>& insts) override;
  void getInstantiations(Node q, std::vector<Node>& insts) override;
  void getSkolemTermVectors(
      std::map<Node, std::vector<Node>>& sks) const override;
  void declarePool(Node p, const std::vector<Node>& initValue) override;
  void declareOracleFun(Node f) override;

  //------------------------------------- HostCoreOutput, through the channel
  void lemma(const Node& lem, theory::LemmaProperty p) override;
  void setModelUnsound(theory::IncompleteId id) override;
  /** The skolemization of cvc5's Skolemize utility, see above. */
  Node getSkolemization(TNode q) override;

 private:
  /**
   * Throw a ModalException for what, which the core does not support: the
   * core records no instantiations, and uses no term pools or oracles.
   */
  [[noreturn]] static void unsupported(const char* what);
  /**
   * Make the relevancy tracker, the one module of the theory engine; none of
   * the modules of cvc5's quantifiers engine are made.
   */
  void finishInit(TheoryEngine* te) override;

  /** The output channel of the quantifiers theory. */
  theory::OutputChannel& d_out;
  /** The ported core. */
  SharedBackend d_backend;
  /** The core under cvc5's prop engine. */
  std::unique_ptr<HostCore> d_core;
  /** Gives the core the literals the SAT solver asserts. */
  std::unique_ptr<RelevancyTracker> d_tracker;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIERS__Z3_QUANTIFIERS_ENGINE_H */

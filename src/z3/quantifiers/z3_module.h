/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The quantifiers module of the ported Z3 core.
 *
 * Not ported from Z3: this is cvc5 integration code.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__QUANTIFIERS__Z3_MODULE_H
#define CVC5__Z3__QUANTIFIERS__Z3_MODULE_H

#include <memory>

#include "theory/quantifiers/quant_module.h"
#include "z3/quantifiers/smt_context.h"

namespace cvc5::internal {
namespace z3 {

/**
 * The module of cvc5's quantifiers engine with --z3, the only one, which owns
 * the ported core. cvc5's own theories do the ground reasoning, with their
 * equality engines and theory combination; the core matches and instantiates
 * over a shadow of the ground state:
 * - it receives every literal the SAT solver asserts, for its E-graph and
 *   for relevancy (RelevancyTracker), and the equalities cvc5's theories
 *   derive, through the master equality engine, of whose merges the
 *   quantifiers engine notifies this module (notifyMasterMerge);
 * - it sends lemmas only (instances, conflicts and splits), which need no
 *   explanation, and reports no propagations;
 * - the formulas it asserts go through cvc5's preprocessing first.
 *
 * The rest is the quantifiers engine's: it registers the quantified formulas,
 * and skolemizes those asserted false. The core also takes the skolemization
 * of a quantified formula assigned false that is relevant to it, so that the
 * witnesses are relevant as well.
 */
class Z3Module : public theory::quantifiers::QuantifiersModule
{
 public:
  Z3Module(Env& env,
           theory::quantifiers::QuantifiersState& qs,
           theory::quantifiers::QuantifiersInferenceManager& qim,
           theory::quantifiers::QuantifiersRegistry& qr,
           theory::quantifiers::TermRegistry& tr);
  ~Z3Module();
  /** Make the core, for the theory engine te. */
  void finishInit(TheoryEngine* te) override;
  void presolve() override;
  /** Assert the preprocessed assertions to the core. */
  void ppNotifyAssertions(const std::vector<Node>& assertions) override;
  /** Run the core, at standard and full effort. */
  bool needsCheck(theory::Theory::Effort e) override;
  void check(theory::Theory::Effort e, QEffort quant_e) override;
  void preRegisterQuantifier(Node q) override;
  /** Give the merge to the core. */
  void notifyMasterMerge(TNode t1, TNode t2) override;
  std::string identify() const override { return "z3"; }

 private:
  /** The ported core, under cvc5's prop engine. */
  std::unique_ptr<SmtContext> d_core;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIERS__Z3_MODULE_H */

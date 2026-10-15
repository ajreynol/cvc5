/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Replay untrusted instantiation hints through native quantifier reasoning.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INST_STRATEGY_Z3_REPLAY_H
#define CVC5__THEORY__QUANTIFIERS__INST_STRATEGY_Z3_REPLAY_H

#include <unordered_set>

#include "theory/quantifiers/quant_module.h"
#include "util/statistics_stats.h"

namespace cvc5::internal::theory::quantifiers {

/** Only native Instantiate constructs lemmas. No port-produced formula or
 * explanation is ever asserted by this module. */
class InstStrategyZ3Replay : public QuantifiersModule
{
 public:
  using Instantiations = std::map<Node, std::vector<std::vector<Node>>>;
  InstStrategyZ3Replay(Env& env,
                       QuantifiersState& qs,
                       QuantifiersInferenceManager& qim,
                       QuantifiersRegistry& qr,
                       TermRegistry& tr);
  void setInstantiations(Instantiations insts);
  void registerQuantifier(Node q) override;
  bool needsCheck(Theory::Effort e) override;
  void check(Theory::Effort e, QEffort quant_e) override;
  std::string identify() const override;
  /** Hints for quantifiers not encountered in native search. */
  size_t getNumPending() const;
  /** Pending hints whose quantified formula was never registered natively. */
  size_t getNumUnmapped() const;

 private:
  Instantiations d_pending;
  std::unordered_set<Node> d_registered;
  IntStat d_received;
  IntStat d_attempted;
  IntStat d_invalid;
  IntStat d_added;
};

}  // namespace cvc5::internal::theory::quantifiers

#endif

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A conservative filter for excluding quantified formulas from E-matching.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EMATCHING__EMATCHING_FILTER_H
#define CVC5__THEORY__QUANTIFIERS__EMATCHING__EMATCHING_FILTER_H

#include <cstdint>
#include <map>
#include <vector>

#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

namespace inst {
class Trigger;
}

/**
 * A conservative estimate of quantified formulas for which it is not useful to
 * run E-matching. Quantified formulas excluded by this class should not produce
 * instantiations when E-matching is run on them.
 *
 * The filter tracks equality-engine events and marks triggers dirty when new
 * events are relevant to their match operators. At last-call effort, all
 * triggers are processed as a conservative backstop.
 */
class EmatchingFilter : public QuantifiersModule
{
 public:
  EmatchingFilter(Env& env,
                  QuantifiersState& qs,
                  QuantifiersInferenceManager& qim,
                  QuantifiersRegistry& qr,
                  TermRegistry& tr);

  bool needsCheck(Theory::Effort e) override;
  void check(Theory::Effort e, QEffort quant_e) override;
  void registerQuantifier(Node q) override;
  /** Returns true if quantified formula q should be excluded from E-matching.
   */
  bool exclude(Node q) const;
  /** Register a trigger that may be filtered by this class. */
  void registerTrigger(inst::Trigger* tr);
  /** Returns true if trigger tr should be processed this round. */
  bool shouldProcessTrigger(inst::Trigger* tr);
  /** Notify that trigger tr has been fully processed this round. */
  void notifyTriggerProcessed(inst::Trigger* tr);
  /** Get the number of filtered triggers in the current round. */
  uint64_t getNumFilteredTriggers() const;
  /** Get the number of unfiltered triggers in the current round. */
  uint64_t getNumUnfilteredTriggers() const;
  /** Identify this module. */
  std::string identify() const override;

 private:
  /** Snapshot current master equality engine events and compute their delta. */
  void updateMasterEqEvents();
  /** Update trigger dirty bits based on the current master equality event diff.
   */
  void updateTriggerProcessingNeeds();
  /** Account for a trigger filtering decision. */
  void accountTriggerDecision(inst::Trigger* tr, bool shouldProcess);
  /** Print the current round master equality engine event delta. */
  void traceMasterEqEventDiff(size_t previousSize) const;
  /** Compute whether quantified formula q should be excluded. */
  bool shouldExclude(Node q) const;
  /** Cached exclusion decision per quantified formula. */
  std::map<Node, bool> d_excluded;
  /** Current effort for the filter. */
  Theory::Effort d_effort;
  /** Whether we already have a master equality event snapshot. */
  bool d_hasMasterEqEventSnapshot;
  /** The most recent master equality engine event snapshot. */
  std::vector<TermRegistry::MasterEqEvent> d_masterEqEventSnapshot;
  /** Events removed from the previous snapshot. */
  std::vector<TermRegistry::MasterEqEvent> d_masterEqEventsRemoved;
  /** Events added since the previous snapshot. */
  std::vector<TermRegistry::MasterEqEvent> d_masterEqEventsAdded;
  /** The set of triggers registered with this filter. */
  std::map<inst::Trigger*, bool> d_registeredTriggers;
  /** Whether a trigger has been processed since it was registered. */
  std::map<inst::Trigger*, bool> d_triggersProcessed;
  /** Whether a trigger must be reprocessed due to relevant EE changes. */
  std::map<inst::Trigger*, bool> d_triggerNeedsProcessing;
  /** Whether a trigger decision has already been counted this round. */
  std::map<inst::Trigger*, bool> d_accountedTriggers;
  /** Number of filtered triggers in the current round. */
  uint64_t d_numFilteredTriggers;
  /** Number of unfiltered triggers in the current round. */
  uint64_t d_numUnfilteredTriggers;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EMATCHING__EMATCHING_FILTER_H */

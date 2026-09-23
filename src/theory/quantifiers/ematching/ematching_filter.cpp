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

#include "theory/quantifiers/ematching/ematching_filter.h"

#include <algorithm>

#include "theory/quantifiers/ematching/trigger.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

EmatchingFilter::EmatchingFilter(Env& env,
                                 QuantifiersState& qs,
                                 QuantifiersInferenceManager& qim,
                                 QuantifiersRegistry& qr,
                                 TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_effort(Theory::EFFORT_STANDARD),
      d_hasMasterEqEventSnapshot(false),
      d_numFilteredTriggers(0),
      d_numUnfilteredTriggers(0)
{
}

bool EmatchingFilter::needsCheck(Theory::Effort e)
{
  return d_qstate.getInstWhenNeedsCheck(e);
}

void EmatchingFilter::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e != QEFFORT_STANDARD)
  {
    return;
  }
  d_effort = e;
  d_accountedTriggers.clear();
  d_numFilteredTriggers = 0;
  d_numUnfilteredTriggers = 0;
  updateMasterEqEvents();
  updateTriggerProcessingNeeds();
}

void EmatchingFilter::registerQuantifier(Node q)
{
  d_excluded[q] = shouldExclude(q);
}

bool EmatchingFilter::exclude(Node q) const
{
  std::map<Node, bool>::const_iterator it = d_excluded.find(q);
  return it != d_excluded.end() && it->second;
}

void EmatchingFilter::registerTrigger(inst::Trigger* tr)
{
  if (tr == nullptr
      || d_registeredTriggers.find(tr) != d_registeredTriggers.end())
  {
    return;
  }
  d_registeredTriggers[tr] = true;
  d_triggersProcessed[tr] = false;
  d_triggerNeedsProcessing[tr] = true;
}

bool EmatchingFilter::shouldProcessTrigger(inst::Trigger* tr)
{
  registerTrigger(tr);
  bool shouldProcess = !d_triggersProcessed[tr] || d_triggerNeedsProcessing[tr];
  accountTriggerDecision(tr, shouldProcess);
  return shouldProcess;
}

void EmatchingFilter::notifyTriggerProcessed(inst::Trigger* tr)
{
  registerTrigger(tr);
  d_triggersProcessed[tr] = true;
  d_triggerNeedsProcessing[tr] = false;
}

uint64_t EmatchingFilter::getNumFilteredTriggers() const
{
  return d_numFilteredTriggers;
}

uint64_t EmatchingFilter::getNumUnfilteredTriggers() const
{
  return d_numUnfilteredTriggers;
}

std::string EmatchingFilter::identify() const { return "ematching-filter"; }

void EmatchingFilter::updateMasterEqEvents()
{
  std::vector<TermRegistry::MasterEqEvent> currentEvents;
  d_treg.getMasterEqEvents(currentEvents);
  const size_t previousSize = d_masterEqEventSnapshot.size();
  d_masterEqEventsRemoved.clear();
  d_masterEqEventsAdded.clear();
  if (!d_hasMasterEqEventSnapshot)
  {
    d_masterEqEventsAdded = currentEvents;
  }
  else
  {
    size_t prefix = 0;
    size_t maxPrefix =
        std::min(d_masterEqEventSnapshot.size(), currentEvents.size());
    while (prefix < maxPrefix
           && d_masterEqEventSnapshot[prefix] == currentEvents[prefix])
    {
      ++prefix;
    }
    d_masterEqEventsRemoved.insert(d_masterEqEventsRemoved.end(),
                                   d_masterEqEventSnapshot.begin() + prefix,
                                   d_masterEqEventSnapshot.end());
    d_masterEqEventsAdded.insert(d_masterEqEventsAdded.end(),
                                 currentEvents.begin() + prefix,
                                 currentEvents.end());
  }
  d_masterEqEventSnapshot.swap(currentEvents);
  Trace("ematching-filter")
      << "Master equality engine events: New=" << d_masterEqEventsAdded.size()
      << ", Same=" << previousSize - d_masterEqEventsRemoved.size()
      << ", Deleted=" << d_masterEqEventsRemoved.size() << std::endl;
  if (TraceIsOn("ematching-filter-events"))
  {
    traceMasterEqEventDiff(previousSize);
  }
  d_hasMasterEqEventSnapshot = true;
}

void EmatchingFilter::updateTriggerProcessingNeeds()
{
  for (std::pair<inst::Trigger* const, bool>& entry : d_registeredTriggers)
  {
    inst::Trigger* tr = entry.first;
    if (tr == nullptr || d_triggerNeedsProcessing[tr]
        || !d_triggersProcessed[tr])
    {
      continue;
    }
    if (d_effort >= Theory::EFFORT_LAST_CALL)
    {
      d_triggerNeedsProcessing[tr] = true;
      continue;
    }
    bool needsProcessing = false;
    for (const TermRegistry::MasterEqEvent& event : d_masterEqEventsAdded)
    {
      if (event.d_kind == TermRegistry::MasterEqEventKind::NEW_CLASS)
      {
        needsProcessing = tr->isRelevantTerm(event.d_first);
      }
      else if (event.d_kind == TermRegistry::MasterEqEventKind::MERGE)
      {
        needsProcessing = tr->isRelevantTerm(event.d_first)
                          || tr->isRelevantTerm(event.d_second);
      }
      if (needsProcessing)
      {
        break;
      }
    }
    d_triggerNeedsProcessing[tr] = needsProcessing;
  }
}

void EmatchingFilter::accountTriggerDecision(inst::Trigger* tr,
                                             bool shouldProcess)
{
  if (tr == nullptr
      || d_accountedTriggers.find(tr) != d_accountedTriggers.end())
  {
    return;
  }
  d_accountedTriggers[tr] = true;
  if (shouldProcess)
  {
    ++d_numUnfilteredTriggers;
  }
  else
  {
    ++d_numFilteredTriggers;
  }
}

void EmatchingFilter::traceMasterEqEventDiff(size_t previousSize) const
{
  Trace("ematching-filter-events")
      << "Master equality engine events: previous=" << previousSize
      << ", current=" << d_masterEqEventSnapshot.size();
  Trace("ematching-filter-events")
      << ", removed=" << d_masterEqEventsRemoved.size()
      << ", added=" << d_masterEqEventsAdded.size() << "." << std::endl;
  for (const TermRegistry::MasterEqEvent& event : d_masterEqEventsRemoved)
  {
    Trace("ematching-filter-events") << "  removed: " << event << std::endl;
  }
  for (const TermRegistry::MasterEqEvent& event : d_masterEqEventsAdded)
  {
    Trace("ematching-filter-events") << "  added: " << event << std::endl;
  }
}

bool EmatchingFilter::shouldExclude(CVC5_UNUSED Node q) const
{
  // Criteria will be added incrementally. Exclude nothing until then.
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

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

#include "theory/quantifiers/master_eq_notify.h"

#include "theory/quantifiers_engine.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

MasterNotifyClass::MasterNotifyClass(QuantifiersEngine* qe) : d_quantEngine(qe)
{
}

void MasterNotifyClass::eqNotifyNewClass(TNode t)
{
  d_quantEngine->eqNotifyNewClass(t);
}

void MasterNotifyClass::eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  d_quantEngine->eqNotifyConstantTermMerge(t1, t2);
}

void MasterNotifyClass::eqNotifyMerge(TNode t1, TNode t2)
{
  d_quantEngine->eqNotifyMerge(t1, t2);
}

void MasterNotifyClass::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  d_quantEngine->eqNotifyDisequal(t1, t2);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

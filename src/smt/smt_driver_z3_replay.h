/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Confirm the ported Z3 core with native cvc5.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__SMT_DRIVER_Z3_REPLAY_H
#define CVC5__SMT__SMT_DRIVER_Z3_REPLAY_H

#include "options/options.h"
#include "smt/smt_driver.h"
#include "util/statistics_stats.h"

namespace cvc5::internal::smt {

/** The port is only a source of instantiation hints. The main solver remains
 * native cvc5, with its own preprocessing and optional proof production. */
class SmtDriverZ3Replay : public SmtDriverSingleCall
{
 public:
  SmtDriverZ3Replay(Env& env,
                    SmtSolver& smt,
                    ContextManager* ctx,
                    const Options& portOptions);

 protected:
  Result checkSatNext(preprocessing::AssertionPipeline& ap) override;

 private:
  Options d_portOptions;
  TimerStat d_portTime;
  TimerStat d_replayTime;
  IntStat d_confirmed;
  IntStat d_unconfirmed;
  IntStat d_refuted;
  IntStat d_pending;
  IntStat d_unmapped;
};

}  // namespace cvc5::internal::smt

#endif

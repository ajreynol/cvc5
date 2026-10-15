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

#include "smt/smt_driver_z3_replay.h"

#include <algorithm>

#include "options/base_options.h"
#include "options/main_options.h"
#include "options/proof_options.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/z3_options.h"
#include "smt/set_defaults.h"
#include "smt/smt_solver.h"
#include "theory/quantifiers/inst_strategy_z3_replay.h"
#include "theory/quantifiers_engine.h"
#include "theory/smt_engine_subsolver.h"

namespace cvc5::internal::smt {

SmtDriverZ3Replay::SmtDriverZ3Replay(Env& env,
                                     SmtSolver& smt,
                                     ContextManager* ctx,
                                     const Options& portOptions)
    : SmtDriverSingleCall(env, smt, ctx),
      d_portTime(
          env.getStatisticsRegistry().registerTimer("z3::replay::portTime")),
      d_replayTime(
          env.getStatisticsRegistry().registerTimer("z3::replay::nativeTime")),
      d_confirmed(
          env.getStatisticsRegistry().registerInt("z3::replay::confirmed")),
      d_unconfirmed(
          env.getStatisticsRegistry().registerInt("z3::replay::unconfirmed")),
      d_refuted(env.getStatisticsRegistry().registerInt("z3::replay::refuted")),
      d_pending(env.getStatisticsRegistry().registerInt("z3::replay::pending")),
      d_unmapped(
          env.getStatisticsRegistry().registerInt("z3::replay::unmapped"))
{
  d_portOptions.copyValues(portOptions);
  SetDefaults::disableChecking(d_portOptions);
  d_portOptions.write_z3().z3 = true;
  d_portOptions.write_z3().z3Replay = false;
  d_portOptions.write_z3().z3RecordInstantiations = true;
  // Proofs, cores, and models belong exclusively to the native solver.
  auto& smtOpts = d_portOptions.write_smt();
  smtOpts.proofMode = options::ProofMode::OFF;
  smtOpts.produceUnsatCores = false;
  smtOpts.unsatCoresMode = options::UnsatCoresMode::OFF;
  smtOpts.minimalUnsatCores = false;
  smtOpts.unsatAssumptions = false;
  smtOpts.produceModels = false;
  smtOpts.produceAssignments = false;
  smtOpts.produceInterpolants = false;
  smtOpts.produceAbducts = false;
  smtOpts.produceDifficulty = false;
  smtOpts.produceLearnedLiterals = false;
  d_portOptions.write_base().incrementalSolving = false;
  // Avoid a second round of nontrivial simplification of the quantifiers.
  smtOpts.simplificationMode = options::SimplificationMode::NONE;
  auto& driverOpts = d_portOptions.write_driver();
  driverOpts.dumpInstantiations = false;
  driverOpts.dumpInstantiationsDebug = false;
  driverOpts.dumpProofs = false;
  driverOpts.dumpUnsatCores = false;
  driverOpts.dumpUnsatCoresLemmas = false;
  driverOpts.dumpModels = false;
  driverOpts.dumpDifficulty = false;
  d_portOptions.write_proof().checkProofsComplete = false;
  // A cumulative time limit is enforced by the parent, not a fresh subsolver.
  d_portOptions.write_base().cumulativeMillisecondLimit = 0;
}

Result SmtDriverZ3Replay::checkSatNext(preprocessing::AssertionPipeline& ap)
{
  Assert(!options().z3.z3);
  d_smt.preprocess(ap);
  if (options().base.preprocessOnly)
  {
    return Result(Result::UNKNOWN, UnknownExplanation::REQUIRES_FULL_CHECK);
  }
  d_smt.assertToInternal(ap);

  ResourceManager* rm = d_env.getResourceManager();
  if (rm->out())
  {
    return Result(Result::UNKNOWN,
                  rm->outOfResources() ? UnknownExplanation::RESOURCEOUT
                                       : UnknownExplanation::TIMEOUT);
  }
  // Reserve half the remaining per-query time for native confirmation. The
  // parent's timer continues to run while the port is solving.
  uint64_t timeout = options().base.perCallMillisecondLimit == 0
                         ? 0
                         : std::max<uint64_t>(1, rm->getRemainingTime() / 2);
  std::unique_ptr<SolverEngine> port;
  theory::SubsolverSetupInfo ssi(d_env, d_portOptions);
  theory::initializeSubsolver(nodeManager(), port, ssi, timeout != 0, timeout);
  Result portResult;
  std::map<Node, std::vector<std::vector<Node>>> insts;
  {
    TimerStat::CodeTimer timer(d_portTime);
    for (Node a : d_smt.getPreprocessedAssertions())
    {
      port->assertFormula(a);
    }
    portResult = port->checkSat();
    Trace("z3-replay") << "z3-replay: port " << portResult << std::endl;
    if (portResult.getStatus() == Result::UNSAT)
    {
      port->getInstantiationTermVectors(insts);
    }
  }
  if (portResult.getStatus() != Result::UNSAT)
  {
    ++d_unconfirmed;
    Trace("z3-replay") << "z3-replay: unconfirmed (port did not refute)"
                       << std::endl;
    return portResult.isUnknown()
               ? portResult
               : Result(Result::UNKNOWN, UnknownExplanation::UNKNOWN_REASON);
  }
  // Node references in the hints keep their terms alive after the port exits.
  port.reset();
  theory::QuantifiersEngine* qe = d_smt.getQuantifiersEngine();
  auto* replay = qe == nullptr ? nullptr : qe->getZ3Replay();
  if (replay != nullptr)
  {
    replay->setInstantiations(std::move(insts));
  }
  Result result;
  {
    TimerStat::CodeTimer timer(d_replayTime);
    result = d_smt.checkSatInternal();
  }
  if (replay != nullptr)
  {
    d_pending += replay->getNumPending();
    d_unmapped += replay->getNumUnmapped();
    Trace("z3-replay") << "z3-replay: pending hints " << replay->getNumPending()
                       << ", unmapped " << replay->getNumUnmapped()
                       << std::endl;
  }
  if (result.getStatus() == Result::UNSAT)
  {
    ++d_confirmed;
    Trace("z3-replay") << "z3-replay: confirmed" << std::endl;
  }
  else if (result.getStatus() == Result::SAT)
  {
    ++d_refuted;
    Warning() << "z3-replay: REFUTED: native cvc5 returned sat after the "
                 "ported Z3 core returned unsat"
              << std::endl;
  }
  else
  {
    ++d_unconfirmed;
    Trace("z3-replay") << "z3-replay: unconfirmed (native " << result << ")"
                       << std::endl;
  }
  return result;
}

}  // namespace cvc5::internal::smt

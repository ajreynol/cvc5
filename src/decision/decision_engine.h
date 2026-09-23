/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Decision engine.
 */

#include "cvc5_private.h"

#ifndef CVC5__DECISION__DECISION_ENGINE_H
#define CVC5__DECISION__DECISION_ENGINE_H

#include "expr/node.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_types.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace decision {

class DecisionEngine : protected EnvObj
{
 public:
  /** Constructor */
  DecisionEngine(Env& env, prop::CDCLTSatSolver* ss, prop::CnfStream* cs);
  virtual ~DecisionEngine() {}

  /** Presolve, called at the beginning of each check-sat call */
  virtual void presolve() {}

  /**
   * Gets the next decision based on strategies that are enabled. This sets
   * stopSearch to true if no further SAT variables need to be assigned in
   * this SAT context.
   */
  prop::SatLiteral getNext(bool& stopSearch);

  /** Is the DecisionEngine in a state where it has solved everything? */
  virtual bool isDone() = 0;
  /**
   * Adds assertions lems to satisfy that persist in the user context.
   * All input assertions and relevant lemmas are added via this call.
   * @param lems The lemmas to add.
   */
  virtual void addAssertions(const std::vector<TNode>& lems) = 0;
  /**
   * Adds assertions lems to satisfy that persist in the SAT context.
   * By default, only skolem definitions from input and lemmas are added via
   * this call.
   * @param lems The lemmas to add.
   */
  virtual void addLocalAssertions(CVC5_UNUSED const std::vector<TNode>& lems) {}
  /**
   * Notify that the given instantiation lemmas have become active, i.e. their
   * associated quantified formula has just been asserted. These lemmas are
   * already present as (user-context) assertions, but may have been skipped
   * while their quantified formula was not asserted; this call prompts the
   * decision engine to revisit them in the current SAT context.
   * @param lems The instantiation lemmas to revisit.
   */
  virtual void notifyInstLemmasActive(
      CVC5_UNUSED const std::vector<TNode>& lems)
  {
  }

 protected:
  /** Get next internal, the engine-specific implementation of getNext */
  virtual prop::SatLiteral getNextInternal(bool& stopSearch) = 0;
  /** Pointer to the SAT solver */
  prop::CDCLTSatSolver* d_satSolver;
  /** Pointer to the CNF stream */
  prop::CnfStream* d_cnfStream;
};

/**
 * Instance of the above class which does nothing. This is used when
 * the decision mode is set to internal.
 */
class DecisionEngineEmpty : public DecisionEngine
{
 public:
  DecisionEngineEmpty(Env& env);
  bool isDone() override;
  void addAssertions(const std::vector<TNode>& lems) override;

 protected:
  prop::SatLiteral getNextInternal(bool& stopSearch) override;
};

}  // namespace decision
}  // namespace cvc5::internal

#endif /* CVC5__DECISION__DECISION_ENGINE_H */

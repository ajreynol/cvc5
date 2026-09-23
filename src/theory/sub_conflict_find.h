/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Relevance manager.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SUB_CONFLICT_FIND__H
#define CVC5__THEORY__SUB_CONFLICT_FIND__H

#include <unordered_map>
#include <unordered_set>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "expr/node.h"
#include "expr/term_context.h"
#include "theory/difficulty_manager.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/theory_engine_module.h"
#include "theory/valuation.h"

namespace cvc5::internal {

class SolverEngine;

namespace theory {

class TheoryModel;

/**
 * This class manages queries related to relevance of asserted literals.
 * In particular, note the following definition:
 *
 * Let F be a formula, and let L = { l_1, ..., l_n } be a set of
 * literals that propositionally entail it. A "relevant selection of L with
 * respect to F" is a subset of L that also propositionally entails F.
 *
 * This class computes a relevant selection of the current assertion stack
 * at FULL effort with respect to the input formula + theory lemmas that are
 * critical to justify (see LemmaProperty::NEEDS_JUSTIFY). By default, theory
 * lemmas are not critical to justify; in fact, all T-valid theory lemmas
 * are not critical to justify, since they are guaranteed to be satisfied in
 * all inputs. However, some theory lemmas that introduce skolems need
 * justification.
 *
 * As an example of such a lemma, take the example input formula:
 *   (and (exists ((x Int)) (P x)) (not (P 0)))
 * A skolemization lemma like the following needs justification:
 *   (=> (exists ((x Int)) (P x)) (P k))
 * Intuitively, this is because the satisfiability of the existential above is
 * being deferred to the satisfiability of (P k) where k is fresh. Thus,
 * a relevant selection must include both (exists ((x Int)) (P x)) and (P k)
 * in this example.
 *
 * Theories are responsible for marking such lemmas using the NEEDS_JUSTIFY
 * property when calling OutputChannel::lemma.
 *
 * Notice that this class has some relation to the justification decision
 * heuristic (--decision=justification), which constructs a relevant selection
 * of the input formula by construction. This class is orthogonal to this
 * method, since it computes relevant selection *after* a full assignment. Thus
 * its main advantage with respect to decision=justification is that it can be
 * used in combination with any SAT decision heuristic.
 *
 * Internally, this class stores the input assertions and can be asked if an
 * asserted literal is part of the current relevant selection. The relevant
 * selection is computed lazily, i.e. only when someone asks if a literal is
 * relevant, and only at most once per FULL effort check.
 */
class SubConflictFind : public TheoryEngineModule
{
 public:
  /**
   * @param env The environment
   * @param engine The parent theory engine
   */
  SubConflictFind(Env& env, TheoryEngine* engine);
  /**
   * Begin round, called at the beginning of a full effort check in
   * TheoryEngine.
   */
  void check(Theory::Effort effort) override;

 private:
  /** The options for subsolver calls */
  Options d_subOptions;
  /** */
  std::unique_ptr<SolverEngine> d_findConflict;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__RELEVANCE_MANAGER__H */

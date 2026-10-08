/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Regular expression solver for the theory of strings.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__REGEXP_SOLVER_H
#define CVC5__THEORY__STRINGS__REGEXP_SOLVER_H

#include <map>

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/strings/extf_solver.h"
#include "theory/strings/inference_manager.h"
#include "theory/strings/regexp_entail.h"
#include "theory/strings/regexp_operation.h"
#include "theory/strings/sequences_stats.h"
#include "theory/strings/skolem_cache.h"
#include "theory/strings/solver_state.h"
#include "theory/strings/term_registry.h"
#include "util/string.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

class RegExpSolver : protected EnvObj
{
  typedef context::CDList<Node> NodeList;
  typedef context::CDHashMap<Node, bool> NodeBoolMap;
  typedef context::CDHashMap<Node, int> NodeIntMap;
  typedef context::CDHashMap<Node, unsigned> NodeUIntMap;
  typedef context::CDHashMap<Node, Node> NodeNodeMap;
  typedef context::CDHashSet<Node> NodeSet;

 public:
  RegExpSolver(Env& env,
               SolverState& s,
               InferenceManager& im,
               TermRegistry& tr,
               CoreSolver& cs,
               ExtfSolver& es,
               SequencesStatistics& stats);
  ~RegExpSolver() {}

  /** check regular expression memberships
   *
   * This checks the satisfiability of all regular expression memberships
   * of the form (not) s in R. We use various heuristic techniques based on
   * unrolling, combined with techniques from Liang et al, "A Decision Procedure
   * for Regular Membership and Length Constraints over Unbounded Strings",
   * FroCoS 2015.
   */
  void checkMemberships(Theory::Effort e);
  /**
   * Check regular expression memberships eagerly, before running the CAV 14
   * procedure for word equations. Adds lemmas based on our strategy involving
   * reductions or simplifications.
   */
  void checkMembershipsEager();

 private:
  /** compute asserted memberships, store in d_assertedMems */
  void computeAssertedMemberships();
  /** Compute active extended terms of kind k, grouped by representative. */
  std::map<Node, std::vector<Node>> computeAssertions(Kind k) const;
  /**
   * Check inclusions,
   * Assumes d_assertedMems has been computed.
   *
   * @param e The current effort.
   */
  void checkInclusions(Theory::Effort e);
  /**
   * Process the memberships whose regular expression contains a re.loop term,
   * which are handled by abstraction refinement when option
   * --re-loop-abstract is enabled. Assumes d_assertedMems has been computed;
   * this method removes the memberships it processes from d_assertedMems.
   *
   * For each such membership, we mark it as reduced, so that we do not attempt
   * to unfold it. Moreover:
   * (1) If it is asserted with true polarity, we add the lemma
   *       (x in R) => (x in R')
   * where R' is an over-approximation of R in which all re.loop terms have
   * been eliminated, together with the length bounds implied by R.
   * (2) We add the lemma
   *       (x in R) => (x in R'')     (resp. its converse for false polarity)
   * where R'' is the result of eliminating all re.loop terms in R, and hence
   * is equivalent to R. In eager mode this is done immediately, in which case
   * the lemma from (1) is logically redundant and serves only to guide the
   * search. In lazy mode it is done only at last call effort, and only for
   * memberships that are not already satisfied in the candidate model.
   *
   * @param e The current effort.
   */
  void checkLoopAbstraction(Theory::Effort e);
  /**
   * Helper for the above method, called on a single membership assertion m,
   * whose atom is atom and whose polarity is pol.
   */
  void processLoopMembership(Theory::Effort e,
                             const Node& m,
                             const Node& atom,
                             bool pol);
  /**
   * Return the conclusion of the abstraction lemma for atom, which is a
   * membership (x in R) where R contains a re.loop term. This is the
   * conjunction of (x in R') for the over-approximation R' of R computed by
   * utils::mkReLoopOverApprox, and the length bounds on x implied by R.
   * Returns the null node if no such conclusion could be computed.
   */
  Node getLoopAbstractLemma(const Node& atom);
  /**
   * Return the membership (x in R'') where R'' is the result of eliminating
   * all re.loop terms in R, for atom of the form (x in R).
   */
  Node getLoopElimMembership(const Node& atom);
  /**
   * Check evaluations, which applies substitutions for normal forms to
   * regular expression memberships and evaluates them, and also calls
   * other methods (e.g. partial derivative computations) for the purposes
   * of discovering conflictx.
   * Assumes d_assertedMems has been computed.
   */
  void checkEvaluations();
  /**
   * Check unfold, which unfolds regular expression memberships based on the
   * effort level.
   * Assumes d_assertedMems has been computed.
   */
  void checkUnfold(Theory::Effort effort);
  /**
   * Check memberships in equivalence class for regular expression
   * inclusion.
   *
   * This method returns false if it discovered a conflict for this set of
   * assertions, and true otherwise. It discovers a conflict e.g. if mems
   * contains str.in.re(xi, Ri) and ~str.in.re(xj, Rj) and Rj includes Ri.
   *
   * @param e The current effort.
   * @param mems Vector of memberships of the form: (~)str.in.re(x1, R1)
   *             ... (~)str.in.re(xn, Rn) where x1 = ... = xn in the
   *             current context. The function removes elements from this
   *             vector that were marked as reduced.
   * @return False if a conflict was detected, true otherwise
   */
  bool checkEqcInclusion(Theory::Effort e, std::vector<Node>& mems);

  /**
   * Check memberships for equivalence class.
   * The vector mems is a vector of memberships of the form:
   *   (~) (x1 in R1 ) ... (~) (xn in Rn)
   * where x1 = ... = xn in the current context.
   *
   * This method may add lemmas or conflicts via the inference manager.
   *
   * This method returns false if it discovered a conflict for this set of
   * assertions, and true otherwise. It discovers a conflict e.g. if mems
   * contains (xi in Ri) and (xj in Rj) and intersect(xi,xj) is empty.
   */
  bool checkEqcIntersect(const std::vector<Node>& mems);
  /**
   * Return true if we should process regular expression unfoldings with
   * the given polarity at the given effort.
   */
  bool shouldUnfold(Theory::Effort e, bool pol) const;
  /**
   * Add the unfolding lemma for asserted regular expression membership
   * assertion. Return true if a lemma was successfully sent to the inference
   * manager.
   */
  bool doUnfold(const Node& assertion);
  // Constants
  Node d_emptyString;
  Node d_emptyRegexp;
  Node d_true;
  Node d_false;
  /** The solver state of the parent of this object */
  SolverState& d_state;
  /** the output channel of the parent of this object */
  InferenceManager& d_im;
  /** reference to the core solver, used for certain queries */
  CoreSolver& d_csolver;
  /** reference to the extended function solver of the parent */
  ExtfSolver& d_esolver;
  /** Reference to the statistics for the theory of strings/sequences. */
  SequencesStatistics& d_statistics;
  /**
   * Check partial derivative
   *
   * Returns false if a lemma pertaining to checking the partial derivative
   * of x in r was added. In this case, addedLemma is updated to true.
   *
   * The argument atom is the assertion that explains x in r, which is the
   * normalized form of atom that may be modified using a substitution whose
   * explanation is nf_exp.
   */
  bool checkPDerivative(Node x, Node r, Node atom, std::vector<Node>& nf_exp);
  cvc5::internal::String getHeadConst(Node x);
  bool deriveRegExp(Node x, Node r, Node atom, std::vector<Node>& ant);
  Node getNormalSymRegExp(Node r, std::vector<Node>& nf_exp);
  /** regular expression operation module */
  RegExpOpr d_regexp_opr;
  /** The regular expression entailment module, for computing length bounds */
  RegExpEntail d_rent;
  /** Asserted memberships, cached during a full effort check */
  std::map<Node, std::vector<Node>> d_assertedMems;
  /**
   * The set of membership atoms containing re.loop for which we have already
   * sent the abstraction lemma.
   *
   * Note that although the lemmas we send are valid independent of the current
   * assertions, these caches must be SAT-context dependent and *not*
   * user-context dependent. This is because a pending lemma is discarded if a
   * conflict is discovered while processing pending facts in the same round
   * (see InferenceManagerBuffered::doPending). Making the cache SAT-context
   * dependent ensures that such a lemma is sent again after backtracking,
   * which is essential for the elimination lemma below, since otherwise the
   * membership would be left with no semantics at all.
   */
  NodeSet d_loopAbstract;
  /**
   * The set of membership assertions containing re.loop for which we have
   * already sent the elimination lemma. Note this contains polarized
   * assertions, since the elimination lemma we send depends on the polarity of
   * the assertion. See note above regarding the choice of context.
   */
  NodeSet d_loopElim;
}; /* class TheoryStrings */

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__THEORY_STRINGS_H */

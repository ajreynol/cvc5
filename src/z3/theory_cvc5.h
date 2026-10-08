/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bridges from cvc5's own theory solvers into the ported Z3 core.
 *
 * Unlike the rest of src/z3, nothing here is ported from Z3: these are
 * adapters that let cvc5's arithmetic and bit-vector solvers decide the
 * fragments of a query the ported core does not reason about itself, so that
 * only the parts of Z3 that matter for quantifier performance -- the CDCL
 * core, relevancy, congruence closure and E-matching -- are duplicated.
 *
 * The bridge works like a theory solver that answers only at final check: the
 * ported core owns the Boolean structure, the equalities and the
 * instantiation, and hands the conjunction of the assigned arithmetic and
 * bit-vector literals to a cvc5 subsolver as *assumptions*. If the subsolver
 * reports unsat, the unsat assumptions become the conflict, so the core
 * learns a clause over literals it already has. If it reports anything else,
 * the search is marked model-unsound: a satisfying assignment of the two
 * solvers together would additionally require interface equality propagation
 * between them, which is not implemented, so "sat" is reported as "unknown".
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__THEORY_CVC5_H
#define CVC5__Z3__THEORY_CVC5_H

#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "z3/theory.h"

namespace cvc5::internal {

class SolverEngine;

namespace z3 {

class TheoryCvc5;

/**
 * The state the per-theory bridges share: one cvc5 subsolver and the set of
 * atoms and terms the bridged theories own.
 */
class Cvc5Bridge
{
 public:
  Cvc5Bridge(SmtContext& ctx);
  ~Cvc5Bridge();

  /** Note that th is one of the bridged theories. */
  void addTheory(TheoryCvc5* th);

  /** True if th is the bridge that runs the subsolver. */
  bool isOwner(const TheoryCvc5* th) const;

  /** Register an atom one of the bridges owns. */
  void registerAtom(TNode atom, BoolVar v);

  /** Register a term whose enode takes part in the interface. */
  void registerTerm(TNode term);

  /**
   * Run the subsolver on the currently assigned literals of the bridged
   * theories. Returns FC_CONTINUE if a conflict was signalled.
   */
  FinalCheckStatus check();

  void reset();

 private:
  /** What an assumption of the subsolver stands for in the core. */
  struct Antecedent
  {
    /** the literal of the core that is assigned true, if this is a literal */
    Literal d_lit = s_nullLiteral;
    /** the pair of enodes that are equal, if this is an equality */
    ENodePair d_eq{nullptr, nullptr};
  };

  bool initSubsolver();

  /** True if the subsolver owns the theory tid. */
  static bool isBridged(TheoryId tid);

  /** True if the class of the root r is shared with a non-bridged theory. */
  static bool isSharedClass(ENode* r);

  /**
   * Reconcile the subsolver's model with the core's classes on the shared
   * terms, propagating or splitting on an interface equality as needed.
   */
  FinalCheckStatus checkInterface(std::vector<Node>& assumps);

  /** The shared class pairs the subsolver's model gives the same value. */
  void collectCandidates(std::vector<std::pair<ENode*, ENode*>>& candidates);

  /** Ask the search to decide the equality of n1 and n2. */
  FinalCheckStatus mkInterfaceSplit(ENode* n1, ENode* n2);

  /** How many entailment checks one final check may make. */
  static constexpr size_t s_maxInterfaceChecks = 16;

  /** Collect the assumptions; false if the subsolver cannot be used. */
  bool mkAssumptions(std::vector<Node>& assumps);

  /** Record the terms the assumptions mention. */
  void collectKnown(const std::vector<Node>& assumps);

  SmtContext& d_ctx;
  std::unique_ptr<SolverEngine> d_sub;
  bool d_subFailed;
  std::vector<TheoryCvc5*> d_theories;
  /** the atoms the bridges own, with the Boolean variable of each */
  std::vector<std::pair<Node, BoolVar>> d_atoms;
  /** the terms of a bridged sort that the core has internalized */
  std::vector<Node> d_terms;
  /** what each assumption of the last check stands for */
  std::unordered_map<Node, Antecedent> d_antecedents;
  /** the terms the last set of assumptions mentions */
  std::unordered_set<Node> d_known;
};

/**
 * The bridge for one theory of cvc5. There is one of these per theory id,
 * since the core dispatches internalization by theory id, and they all share
 * a single Cvc5Bridge.
 */
class TheoryCvc5 : public Theory
{
 public:
  TheoryCvc5(SmtContext& ctx, TheoryId tid, Cvc5Bridge& bridge);

  const char* getName() const override { return "cvc5-bridge"; }

  void print(std::ostream& /*out*/) const override {}

  /** The representative enode of v's class; null if there is none. */
  ENode* getRepENode(TheoryVar v);

 protected:
  TheoryVar mkVar(ENode* n) override;
  bool internalizeAtom(TNode atom, bool gateCtx) override;
  bool internalizeTerm(TNode term) override;
  void internalizeEqEh(TNode atom, BoolVar v) override;
  void applySortCnstr(ENode* n, const TypeNode& s) override;
  void newEqEh(TheoryVar /*v1*/, TheoryVar /*v2*/) override {}
  bool useDiseqs() const override { return false; }
  void newDiseqEh(TheoryVar /*v1*/, TheoryVar /*v2*/) override {}
  FinalCheckStatus finalCheckEh(size_t level) override;
  void resetEh() override;

 private:
  Cvc5Bridge& d_bridge;
};

/**
 * Create the bridge to cvc5's arithmetic solver, or null if the bridge is
 * unavailable.
 */
Theory* mkTheoryArithBridge(SmtContext& ctx);

/**
 * Create the bridge to cvc5's bit-vector solver, or null if the bridge is
 * unavailable.
 */
Theory* mkTheoryBvBridge(SmtContext& ctx);

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__THEORY_CVC5_H */

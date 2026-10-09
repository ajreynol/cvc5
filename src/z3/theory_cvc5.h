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
   *
   * @param finalCheck Whether this is a final check, where the models of the
   * two solvers additionally have to be reconciled. Outside a final check
   * only conflicts and entailed equalities are looked for -- the point of
   * running there is that Z3's arithmetic solver propagates its equalities
   * eagerly, and the congruence merges they cause are what E-matching needs
   * to make progress.
   */
  FinalCheckStatus check(bool finalCheck);

  /** Run assume_eqs for every bridged theory. */
  FinalCheckStatus assumeInterfaceEqs();

  /**
   * Propagate the equalities between the bridged terms the subsolver pins to
   * the same value, which is what Z3's arithmetic solver does for free every
   * time a variable becomes fixed (its arith-fixed-eqs statistic). Unlike
   * assume_eqs these are entailed, so they are propagated rather than split
   * on, and unlike assume_eqs they do not require the term to be shared --
   * the point is the congruence merge, which E-matching then sees.
   *
   * Returns true if an equality was propagated.
   */
  bool propagateFixedEqs(std::vector<Node>& assumps);

  /** Put the subsolver back on a model of assumps, if it has lost one. */
  void restoreModel(std::vector<Node>& assumps);

  /**
   * Propagate val for every member of one group of bridged terms the model
   * gives that value, if the assumptions entail it. True if a merge happened.
   */
  bool propagateFixedGroup(std::vector<Node>& assumps,
                           const std::vector<ENode*>& members,
                           TNode val);

  /** True if enough has been assigned to be worth running the subsolver. */
  bool shouldCheckEagerly() const;

  /**
   * Ask the subsolver for a model that keeps the shared terms apart wherever
   * the constraints allow it, which is what Z3's arithmetic solver does with
   * random_update before it assumes a single interface equality: two shared
   * terms whose values merely happen to coincide, while nothing forces them
   * to, need no case split at all -- the arithmetic model can simply be
   * adjusted to the arrangement the congruence closure already has. Without
   * this step every coincidence becomes an equality for the core to decide,
   * which on these benchmarks meant tens of thousands of them where Z3
   * assumes thirty.
   *
   * Whether or not the separation succeeds, the subsolver is left with a
   * model of assumps if it had one on entry. True if it succeeded.
   */
  bool separateSharedValues(std::vector<Node>& assumps);

  /**
   * Ask the subsolver whether the assumptions, cut back to base, together
   * with every constraint in wanted, are satisfiable. The assumptions are
   * restored to base either way; d_haveModel says whether a model is left.
   */
  bool trySeparate(std::vector<Node>& assumps,
                   size_t base,
                   const std::vector<Node>& wanted);

  /** The relevant shared bridged enode roots that have a model value. */
  void collectSharedRoots(std::vector<std::pair<ENode*, Node>>& out);

  /**
   * The value the subsolver's last model gives t, or null if the subsolver
   * does not constrain it.
   */
  Node getModelValue(TNode t);

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

  /** Signal the conflict the given assumptions stand for. */
  void mkConflict(const std::vector<Node>& core);

  /** How many queries one separation step may make. */
  static constexpr size_t s_maxSeparateCalls = 8;
  /** How many queries one round of fixed-value propagation may make. */
  static constexpr size_t s_maxFixedCalls = 8;
  /** How many unsat cores are remembered. */
  static constexpr size_t s_maxCachedCores = 1024;
  /** How many satisfiable literal sets are remembered. */
  static constexpr size_t s_maxCachedSatSets = 4096;

  /** The smallest and largest number of assignments between eager checks. */
  static constexpr uint64_t s_minEagerGap = 200;
  static constexpr uint64_t s_maxEagerGap = 100000;

  /** Collect the assumptions; false if the subsolver cannot be used. */
  bool mkAssumptions(std::vector<Node>& assumps);

  /** Record the terms the assumptions mention. */
  void collectKnown(const std::vector<Node>& assumps);

  /**
   * The abstraction of t that the subsolver works on: the arithmetic and
   * bit-vector structure of t is kept, and every other subterm is replaced by
   * a fresh constant of the same sort. This is the half of a Nelson-Oppen
   * combination the bridged theories are responsible for -- Z3's arithmetic
   * solver likewise only ever sees arithmetic terms over opaque leaves, with
   * the congruence closure relating the leaves. Without it the subsolver
   * re-solves the whole uninterpreted and datatype part of the query on every
   * call, which dominates the running time.
   */
  Node abstract(TNode t);

  /** True if applications of k belong to a bridged theory. */
  static bool isBridgedOp(Kind k);

  /** True if terms of type tn are bridged. */
  static bool isBridgedType(const TypeNode& tn);

  /** A fresh constant standing for the opaque term t. */
  Node mkAbsConst(TNode t);

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
  /** the abstraction of each term, which is stable across the search */
  std::unordered_map<Node, Node> d_abs;
  /** whether the subsolver's last check left a model to read values from */
  bool d_haveModel = false;
  /**
   * The literals already asserted to the subsolver permanently, which are
   * the ones the core assigned at or below its base level.
   */
  std::unordered_set<Node> d_asserted;
  /** the base level the permanent assertions were collected at */
  uint32_t d_assertedBaseLvl;
  /** Hashes a sorted list of assumptions. */
  struct NodeVecHash
  {
    size_t operator()(const std::vector<Node>& v) const
    {
      size_t h = v.size();
      for (const Node& n : v)
      {
        h = h * 1000003 + n.getId();
      }
      return h;
    }
  };

  /**
   * The literal sets the subsolver already found satisfiable. Satisfiability
   * of a set of literals does not depend on the scope it was found in, so
   * these stay valid for the whole search.
   */
  std::unordered_set<std::vector<Node>, NodeVecHash> d_satSets;
  /** the number of bridged terms the cached sets were judged at */
  size_t d_satSetsTermsLim = 0;
  /** the assignment count the subsolver was last run at */
  uint64_t d_lastCheckAssignments = 0;
  /** how many assignments to wait for before running the subsolver again */
  uint64_t d_eagerGap = s_minEagerGap;
  /** The unsat cores the subsolver already found, for the same reason. */
  std::vector<std::vector<Node>> d_unsatCores;
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

  /**
   * Assume the equality of every pair of relevant shared terms the
   * subsolver's model gives the same value, which is the half of a
   * Nelson-Oppen combination this side is responsible for. True if anything
   * changed, in which case the search is not done.
   */
  bool assumeInterfaceEqs();

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
  bool canPropagate() override;
  void propagate() override;
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

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory plugin interface of the ported Z3 SMT core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_theory.h, and recast in cvc5 style.
 *
 * This is the interface a theory solver must implement to participate in the
 * ported core's search. It is also the seam at which cvc5's own bit-vector and
 * arithmetic solvers are attached, by a plugin that forwards these callbacks.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__THEORY_H
#define CVC5__Z3__THEORY_H

#include <ostream>
#include <vector>

#include "expr/node.h"
#include "z3/enode.h"
#include "z3/types.h"
#include "z3/util/literal.h"

namespace cvc5::internal {
namespace z3 {

class Justification;
class Params;
class SmtContext;

/**
 * A theory plugin.
 *
 * Expressions are "internalized" by the core, which builds the auxiliary data
 * structures (enodes, Boolean variables) that the search works over. The core
 * does not know the internals of any theory, so during internalization it
 * notifies the theory whenever it meets an application of one of the theory's
 * function symbols.
 *
 * A theory variable created at scope level n must be deleted when level n is
 * backtracked. The core uses isAttachedToVar to decide whether an enode
 * already has a theory variable.
 */
class Theory
{
 public:
  Theory(SmtContext& ctx, TheoryId fid);
  virtual ~Theory() = default;

  virtual void setup() {}

  virtual void init() {}

  TheoryId getId() const { return d_id; }

  TheoryId getFamilyId() const { return d_id; }

  SmtContext& getContext() const { return d_ctx; }

  const Params& getParams() const;

  virtual void updtParams() {}

  /**
   * True if the given enode is attached to a variable of this theory.
   *
   * Note this is not equivalent to n->getThVar(getId()) != s_nullTheoryVar: a
   * theory variable v may appear in the list of n but have been inherited from
   * another enode during an equivalence class merge, in which case
   * getENode(v) != n.
   */
  bool isAttachedToVar(const ENode* n) const
  {
    TheoryVar v = n->getThVar(getId());
    return v != s_nullTheoryVar && getENode(v) == n;
  }

  ENode* getENode(TheoryVar v) const
  {
    Assert(v < static_cast<TheoryVar>(d_var2ENode.size()));
    return d_var2ENode[v];
  }

  TNode getExpr(TheoryVar v) const { return getENode(v)->getExpr(); }

  /** The representative of the equivalence class of v. */
  TheoryVar getRepresentative(TheoryVar v) const
  {
    Assert(v != s_nullTheoryVar);
    TheoryVar r = getENode(v)->getRoot()->getThVar(getId());
    Assert(r != s_nullTheoryVar);
    return r;
  }

  bool isRepresentative(TheoryVar v) const { return getRepresentative(v) == v; }

  size_t getNumVars() const { return d_var2ENode.size(); }

  size_t getOldNumVars(size_t numScopes) const
  {
    return d_var2ENodeLim[d_var2ENodeLim.size() - numScopes];
  }

  virtual void print(std::ostream& out) const = 0;

  virtual void printVar2ENode(std::ostream& out) const;

  virtual const char* getName() const { return "unknown"; }

  // ----------------------------------------------- conflict resolution
  /**
   * Invoked when a theory atom is used during conflict resolution, which lets
   * the theory bump the activity of the enodes in the atom.
   */
  virtual void conflictResolutionEh(TNode /*atom*/, BoolVar /*v*/) {}

  // ----------------------------------------------- model generation
  /** True if the theory supports model construction. */
  virtual bool buildModels() const { return true; }

  /** The value of n in the current model, if the theory can produce one. */
  virtual bool getValue(ENode* /*n*/, Node& /*r*/) { return false; }

 protected:
  virtual TheoryVar mkVar(ENode* n)
  {
    Assert(!isAttachedToVar(n));
    TheoryVar v = static_cast<TheoryVar>(d_var2ENode.size());
    d_var2ENode.push_back(n);
    return v;
  }

  TheoryVar getThVar(TNode e) const;

  TheoryVar getThVar(ENode* n) const { return n->getThVar(getId()); }

  bool lazyPush();
  bool lazyPop(size_t& numScopes);
  void forcePush();

  /**
   * True if the theory uses default internalization, i.e. internalizing an
   * application internalizes all of its arguments. Theories like arithmetic
   * do not: in (+ a (+ b c)) no enode is created for (+ b c).
   */
  virtual bool defaultInternalizer() const { return true; }

  /**
   * Invoked by the core when an atom is being internalized. The theory may
   * return false if it does not implement the given predicate symbol.
   *
   * After this method runs, the atom must be associated with a new Boolean
   * variable.
   */
  virtual bool internalizeAtom(TNode atom, bool gateCtx) = 0;

  /** Invoked after the given equality atom is internalized. */
  virtual void internalizeEqEh(TNode /*atom*/, BoolVar /*v*/) {}

  /**
   * Invoked by the core when a term is being internalized. The theory may
   * return false if it does not implement the given function symbol.
   *
   * After this method runs, the term must be associated with a new enode.
   */
  virtual bool internalizeTerm(TNode term) = 0;

  /** Apply the (interpreted) sort constraints of s to the given enode. */
  virtual void applySortCnstr(ENode* /*n*/, const TypeNode& /*s*/) {}

  /** Invoked when a truth value is assigned to the given Boolean variable. */
  virtual void assignEh(BoolVar /*v*/, bool /*isTrue*/) {}

  /** Let the theory determine the phase of a variable. */
  virtual LBool getPhase(BoolVar /*v*/) { return L_UNDEF; }

  /** Equality propagation (v1 = v2): core to theory. */
  virtual void newEqEh(TheoryVar v1, TheoryVar v2) = 0;

  /** True if the theory does anything with the disequalities from the core. */
  virtual bool useDiseqs() const { return true; }

  /** Disequality propagation (v1 /= v2): core to theory. */
  virtual void newDiseqEh(TheoryVar v1, TheoryVar v2) = 0;

  /** Invoked when the theory application n is marked as relevant. */
  virtual void relevantEh(TNode /*n*/) {}

  /** Invoked when a new backtracking point is created. */
  virtual void pushScopeEh();

  /** Invoked during backtracking. */
  virtual void popScopeEh(size_t numScopes);

  /** Invoked when the core is restarted. */
  virtual void restartEh() {}

  /** Invoked before the search starts. */
  virtual void initSearchEh() {}

  /**
   * Invoked when the core has assigned a truth value to every Boolean
   * variable without detecting an inconsistency.
   */
  virtual FinalCheckStatus finalCheckEh(size_t /*level*/) { return FC_DONE; }

  /**
   * The number of priority levels this theory supports for final checks. The
   * first level is for the cheapest invocations and later levels for more
   * expensive ones, which emulates a priority queue of final-check actions.
   */
  virtual size_t numFinalCheckLevels() const { return 1; }

  /**
   * Parametric theories (e.g. arrays) should implement this; see
   * SmtContext::isShared.
   */
  virtual bool isShared(TheoryVar /*v*/) const { return false; }

  /** True if n under parent p is in a beta redex position. */
  virtual bool isBetaRedex(ENode* /*p*/, ENode* /*n*/) const { return false; }

  /** True if the theory has something to propagate. */
  virtual bool canPropagate() { return false; }

  /** Give the theory a chance to perform theory propagation. */
  virtual void propagate() {}

  /** Let a theory contribute to disequality propagation. */
  virtual Justification* whyIsDiseq(TheoryVar /*v1*/, TheoryVar /*v2*/)
  {
    return nullptr;
  }

  /** Release memory. */
  virtual void flushEh() {}

  /** Invoked when the core is being reset. */
  virtual void resetEh();

  /**
   * When an equality atom is created during the search, the default behavior
   * is to orient it so that the left argument has the smaller id. Some
   * theories use a different convention (arithmetic always puts a numeral on
   * the right), and should override this.
   */
  virtual Node mkEqAtom(TNode lhs, TNode rhs);

  Literal mkEq(TNode a, TNode b, bool gateCtx);

  Literal mkPreferredEq(TNode a, TNode b);

  Literal mkLiteral(TNode e);

  ENode* ensureENode(TNode e);

  ENode* getRoot(TNode e) { return ensureENode(e)->getRoot(); }

  /**
   * Assume equalities between variables that have equal values according to
   * the given table, which is indexed by the variable's value. The table type
   * must provide reset() and insertIfNotThere(TheoryVar).
   */
  template <typename VarValueTable>
  bool assumeEqs(VarValueTable& table)
  {
    table.reset();
    bool result = false;
    TheoryVar num = static_cast<TheoryVar>(getNumVars());
    for (TheoryVar v = 0; v < num; ++v)
    {
      ENode* n = getENode(v);
      if (n != nullptr && isRelevantAndShared(n))
      {
        TheoryVar other = table.insertIfNotThere(v);
        if (other != v)
        {
          ENode* n2 = getENode(other);
          if (assumeEq(n, n2))
          {
            result = true;
          }
        }
      }
    }
    return result;
  }

  bool isRelevantAndShared(ENode* n) const;

  bool assumeEq(ENode* n1, ENode* n2);

  TheoryId d_id;
  SmtContext& d_ctx;
  ENodeVector d_var2ENode;
  std::vector<size_t> d_var2ENodeLim;
  size_t d_lazyScopes;
  bool d_lazy;

  friend class SmtContext;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__THEORY_H */

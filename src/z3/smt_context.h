/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The logical context: the ported Z3 SMT core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_context.h, and recast in cvc5 style.
 *
 * The theory side of the core: the E-graph (congruence closure over
 * enodes), the internalizer, and the quantifier manager. Its propositional
 * side, PropCore, mirrors cvc5's assignment (see HostCore); the ground
 * reasoning is cvc5's theories', whose equalities reach the E-graph through
 * the ShadowFeed.
 *
 * Of Z3's context, only what E-matching and quantifier instantiation need
 * is ported: not its search (decisions, conflict resolution, restarts, lemma
 * garbage collection), its theory plugins, proof production, or Z3's
 * asserted_formulas preprocessing pipeline (cvc5's Preprocessor is used
 * instead).
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__SMT_CONTEXT_H
#define CVC5__Z3__SMT_CONTEXT_H

#include <deque>
#include <functional>
#include <memory>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "util/statistics_stats.h"
#include "z3/ast.h"
#include "z3/b_justification.h"
#include "z3/bool_var_data.h"
#include "z3/cg_table.h"
#include "z3/clause.h"
#include "z3/enode.h"
#include "z3/eq_justification.h"
#include "z3/justification.h"
#include "z3/nnf.h"
#include "z3/params.h"
#include "z3/prop_core.h"
#include "z3/quantifier_manager.h"
#include "z3/quantifier_services.h"
#include "z3/relevancy.h"
#include "z3/statistics.h"
#include "z3/types.h"
#include "z3/util/literal.h"
#include "z3/util/trail.h"
#include "z3/util/uint_set.h"
#include "z3/util/util.h"
#include "z3/watch_list.h"

namespace cvc5::internal {
namespace z3 {

class QuantifierManager;

/**
 * The theory side of the ported core; PropCore is the propositional side.
 * The quantifier stack reaches it only through QuantifierServices.
 */
class SmtContext final : protected EnvObj, public QuantifierServices
{
 public:
  /** The search statistics. Public, as in Z3. */
  Statistics d_stats;
  /**
   * Handles keeping the counters above registered with cvc5. A deque is used
   * because a ReferenceStat detaches from its counter when a copy of it is
   * destroyed, so the stored handles must never be relocated.
   */
  std::deque<ReferenceStat<uint64_t>> d_regStats;

  SmtContext(Env& env, Params& p);
  virtual ~SmtContext();

  SmtContext(const SmtContext&) = delete;
  SmtContext& operator=(const SmtContext&) = delete;

  // ---------------------------------------------------------- assertions
  //
  // The asserted formulas and the checks are driven by the propositional
  // side, PropCore. The methods below forward to it for the theory side.

  size_t getNumAssertedFormulas() const
  {
    return d_prop.getNumAssertedFormulas();
  }

  TNode getAssertedFormula(size_t idx) const
  {
    return d_prop.getAssertedFormula(idx);
  }

  /**
   * Internalize the asserted formula n, of the given generation: its subterms,
   * then its Boolean structure through PropCore::assertRoot.
   */
  void internalizeAssertion(TNode n, uint32_t generation);

  // ------------------------------------- the scheduling and backtracking
  //                                       contract, called by PropCore
  /**
   * Propagate on the theory side, after Boolean propagation and relevancy
   * have saturated: the assigned atoms, the equalities, the theories and the
   * quantifiers, in that order. Returns false on a conflict.
   */
  bool theoryPropagate();

  /** Whether the theory side has propagation work pending. */
  bool hasPendingTheoryWork() const;

  /** Called at the start of a search. */
  void initSearchEh();

  /** The final check, when every relevant Boolean variable is assigned. */
  FinalCheckStatus finalCheck();

  /** Push a scope of the theory side, after the propositional side's. */
  void pushTheoryScope();

  /**
   * Pop numScopes scopes of the quantifier manager, before the Boolean
   * variables are unassigned.
   */
  void popTheoryScopeBegin(size_t numScopes);

  /**
   * Pop numScopes scopes of the rest of the theory side, after the Boolean
   * variables are unassigned: the trail, the propagation queues and the
   * region, where the justifications live.
   */
  void popTheoryScopeEnd(size_t numScopes);

  void resetCacheGeneration();

  // ----------------------------------------------------------- accessors
  Params& getParams() override { return d_params; }

  Statistics& getStats() override { return d_stats; }

  Region& getRegion() override { return d_region; }

  ENode* getENode(TNode n) const override
  {
    Assert(eInternalized(n));
    return d_app2ENode[n.getId()];
  }

  /** Like getENode, but returns null if n is not internalized. */
  ENode* findENode(TNode n) const
  {
    return getx(d_app2ENode, n.getId(), static_cast<ENode*>(nullptr));
  }

  // ------------------------------------- the Boolean search, see PropCore
  //
  // The methods below forward to the propositional side, d_prop. They are
  // the Boolean API that the theory side and the quantifier engine use.

  /** The propositional side. */
  PropCore& getPropCore() { return d_prop; }

  const PropCore& getPropCore() const { return d_prop; }

  BoolVar getBoolVar(TNode n) const { return d_prop.getBoolVar(n); }

  BoolVar getBoolVar(const ENode* n) const { return getBoolVar(n->getExpr()); }

  BoolVar getBoolVarOfId(size_t id) const { return d_prop.getBoolVarOfId(id); }

  Literal getLiteral(TNode n) const { return d_prop.getLiteral(n); }

  ENode* boolVar2ENode(BoolVar v) const
  {
    Assert(getBdata(v).isENode());
    return d_app2ENode[boolVar2Expr(v).getId()];
  }

  BoolVar enode2BoolVar(const ENode* n) const
  {
    Assert(n->isBool());
    Assert(n != d_falseENode);
    return getBoolVarOfId(n->getOwnerId());
  }

  Literal enode2Literal(const ENode* n) const
  {
    Assert(n->isBool());
    return n == d_falseENode ? s_falseLiteral : Literal(enode2BoolVar(n));
  }

  BoolVarData& getBdata(BoolVar v) { return d_prop.getBdata(v); }

  const BoolVarData& getBdata(BoolVar v) const { return d_prop.getBdata(v); }

  bool hasENode(BoolVar v) const { return getBdata(v).isENode(); }

  LBool getAssignment(Literal l) const { return d_prop.getAssignment(l); }

  LBool getAssignment(BoolVar v) const { return d_prop.getAssignment(v); }

  LBool getAssignment(TNode n) const override
  {
    return d_prop.getAssignment(n);
  }

  LBool getAssignment(ENode* n) const;

  uint32_t getScopeLevel() const override { return d_prop.getScopeLevel(); }

  TNode boolVar2Expr(BoolVar v) const { return d_prop.boolVar2Expr(v); }

  bool isTrue(const ENode* n) const { return n == d_trueENode; }

  size_t getNumENodesOf(TNode decl) const override
  {
    uint32_t id = getDeclIdOption(decl);
    return id < d_decl2ENodes.size() ? d_decl2ENodes[id].size() : 0;
  }

  const ENodeVector& enodesOf(TNode decl) const override
  {
    uint32_t id = getDeclIdOption(decl);
    return id < d_decl2ENodes.size() ? d_decl2ENodes[id] : d_emptyVector;
  }

  uint32_t getGeneration(ENode* e) const override
  {
    // Patterns with equalities are not supported, so there is no need to
    // track the generation of equality nodes.
    if (e->isEq())
    {
      return 0;
    }
    return getCgRoot(e)->d_generation;
  }

  uint32_t getMaxGeneration(size_t numENodes, ENode* const* enodes) override
  {
    uint32_t max = 0;
    for (size_t i = 0; i < numENodes; ++i)
    {
      uint32_t curr = getGeneration(enodes[i]);
      if (curr > max)
      {
        max = curr;
      }
    }
    return max;
  }

  void setGeneration(ENode* e, uint32_t generation);

  /** True if the input contains universal quantifiers. */
  bool hasQuantifiers() const { return d_prop.hasQuantifiers(); }

  // ----------------------------------------------- backtracking support
  template <typename TrailObject>
  void pushTrail(const TrailObject& obj)
  {
    d_trailStack.push(obj);
  }

  void pushTrailPtr(Trail* ptr) { d_trailStack.pushPtr(ptr); }

  TrailStack& getTrailStack() override { return d_trailStack; }

  // ------------------------------------------------------ internalization
  bool bInternalized(TNode n) const override { return d_prop.bInternalized(n); }

  bool litInternalized(TNode n) const override
  {
    return d_prop.litInternalized(n);
  }

  bool eInternalized(TNode n) const override
  {
    return getx(d_app2ENode, n.getId(), static_cast<ENode*>(nullptr))
           != nullptr;
  }

  size_t getNumEInternalized() const { return d_eInternalizedStack.size(); }

  TNode getEInternalized(size_t idx) const { return d_eInternalizedStack[idx]; }

  /** The canonicalizer for quantifiers; see z3/ast.h. */
  QuantifierNormalizer& getNormalizer() { return d_normalizer; }

  ConnectiveNormalizer& getConnectiveNormalizer() { return d_connNormalizer; }

  AssertionRewriter& getAssertionRewriter() { return d_assertionRewriter; }

  Nnf& getNnf() { return d_nnf; }

  /**
   * The preprocessing of cvc5's own theories: it maps a formula to the form
   * cvc5's theories take, adding to defs the definitions of the skolems
   * it introduces. The input (AssertionPreparation) and the instances
   * (internalizeInstance) go through it before the core asserts them and
   * hands them to cvc5, so that both see the same atoms.
   */
  using Cvc5Preprocessor = std::function<Node(TNode, std::vector<Node>&)>;
  void setCvc5Preprocessor(Cvc5Preprocessor p)
  {
    d_cvc5Preprocessor = std::move(p);
  }
  /** The preprocessing of cvc5's theories. */
  const Cvc5Preprocessor& getCvc5Preprocessor() const
  {
    return d_cvc5Preprocessor;
  }
  /**
   * The skolemization of cvc5's quantifiers engine: it maps a quantified
   * formula q to the lemma that skolemizes it, which holds globally and
   * which the core asserts when q is assigned false (see skolemize).
   */
  using Skolemizer = std::function<Node(TNode)>;
  void setSkolemizer(Skolemizer s) { d_skolemizer = std::move(s); }

  /**
   * Merge the classes of a and b, which must be internalized as terms, since
   * cvc5's theories made them equal. The merge is queued for the next
   * propagation.
   */
  void assumeExternalEq(TNode a, TNode b)
  {
    pushEq(getENode(a), getENode(b), EqJustification(&d_externalJustification));
  }
  /** The environment of the enclosing cvc5 solver. */
  const Env& getEnv() const override { return d_env; }

  /**
   * Internalize the body of a quantifier instance, in the form cvc5's
   * theories take, after renormalizing its variables. The instance is
   * asserted at the current scope.
   */
  void internalizeInstance(TNode body, uint32_t generation) override;

  /**
   * Skolemize the quantified formula q, which is assigned false: assert the
   * lemma of the skolemizer (see setSkolemizer).
   */
  void skolemize(TNode q);

  void internalize(TNode n, bool gateCtx);
  void internalize(const Node* exprs, size_t numExprs, bool gateCtx);
  void internalize(TNode n, bool gateCtx, uint32_t generation) override;

  // ---------------------------------------------------- trail callbacks
  /** Undo an addEq; invoked from the trail. */
  void undoAddEq(ENode* r1, ENode* n1, size_t r2NumParents);

  /** Undo a congruence class generation merge; invoked from the trail. */
  void undoMergeCgcGenerations(ENode* e1,
                               uint32_t e1Generation,
                               ENode* e2,
                               uint32_t e2Generation);

  BoolVar mkBoolVar(TNode n) { return d_prop.mkBoolVar(n); }

  ENode* mkENode(TNode n, bool suppressArgs, bool mergeTf, bool cgcEnabled);

  template <typename JustificationT>
  Justification* mkJustification(const JustificationT& j)
  {
    return new (getRegion()) JustificationT(j);
  }

  /** Hand an assigned atom to the theory side; see propagateAtoms. */
  void enqueueAtom(Literal l) { d_atomPropagationQueue.push_back(l); }

  /** Called when the Boolean variable of n is deleted on backtracking. */
  void notifyBoolVarDeleted(TNode n);

  /**
   * Cache the generation of the enodes and quantifiers in n that backtracking
   * to newScopeLvl deletes, so that they are recreated with it.
   */
  void cacheGeneration(TNode n, uint32_t newScopeLvl);

  void mkGateClause(Literal l1, Literal l2) { d_prop.mkGateClause(l1, l2); }

  /**
   * Internalize n, a subterm of an assertion, in the given context; see
   * PropCore::assertRoot.
   */
  void internalizeRec(TNode n, bool gateCtx);

  void setEnodeFlag(BoolVar v, bool isNewVar);

  // ------------------------------------------------------------- engine
  void assign(Literal l, const BJustification& j) { d_prop.assign(l, j); }

  void assign(Literal l, Justification* j) { d_prop.assign(l, j); }

  void addEq(ENode* n1, ENode* n2, EqJustification js);

  void setConflict(Justification* js) { d_prop.setConflict(js); }

  bool inconsistent() const override { return d_prop.inconsistent(); }

  static bool isEq(const ENode* n1, const ENode* n2)
  {
    return n1->getRoot() == n2->getRoot();
  }

  ENode* getCgRoot(ENode* n) const
  {
    if (!n->usesCgTable())
    {
      return n;
    }
    // Fast path: if n is already the congruence root, avoid the table lookup.
    // This matters because getCgRoot is on every generation lookup.
    if (n->isCgr())
    {
      return n;
    }
    ENode* r = d_cgTable.find(n);
    return r != nullptr ? r : n;
  }

  bool isDiseq(ENode* n1, ENode* n2) const override;

  /** An enode congruent to decl(args), or null if there is none. */
  ENode* getENodeEqTo(TNode decl,
                      bool commutative,
                      size_t numArgs,
                      ENode* const* args) override;

  bool canPropagate() const override { return d_prop.canPropagate(); }

  // ------------------------------------------------------------ relevancy
  //
  // Relevancy belongs to the propositional side; see PropCore. The methods
  // below forward to it.

  /**
   * Notify the quantifier manager and the theories that n became relevant;
   * called by PropCore::relevantEh.
   */
  void relevantEh(TNode n);

  bool isRelevantCore(TNode n) const { return d_prop.isRelevantCore(n); }

  bool isRelevant(TNode n) const override { return d_prop.isRelevant(n); }

  bool isRelevant(ENode* n) const { return isRelevant(n->getExpr()); }

  bool isRelevant(Literal l) const { return d_prop.isRelevant(l); }

  /** Whether E-matching considers n. */
  bool isRelevantForMatching(ENode* n) const override { return isRelevant(n); }

  /** Whether the instance checkers consider n. */
  bool isRelevantForChecking(TNode n) const override { return isRelevant(n); }

  bool isRelevantForChecking(ENode* n) const override { return isRelevant(n); }

  void markAsRelevant(TNode n) { d_prop.markAsRelevant(n); }

  void markAsRelevant(ENode* n) override { markAsRelevant(n->getExpr()); }

  void addRelevancyDependency(TNode source, TNode target)
  {
    d_prop.addRelevancyDependency(source, target);
  }

  /**
   * Rewrite a quantifier instance before it is internalized. Z3 applies its
   * th_rewriter here; this port uses cvc5's rewriter.
   */
  Node rewriteInstance(TNode n) const override { return rewrite(n); }

  /**
   * A dense id for a declaration, created on demand. This is the counterpart
   * of Z3's func_decl::get_small_id, which the E-matching engine uses to index
   * its tables by function symbol.
   */
  uint32_t getDeclId(TNode decl) override;
  /** The dense id of decl, or UINT32_MAX if it has none yet. */
  uint32_t getDeclIdOption(TNode decl) const override;

  /**
   * Expose the core's counters through cvc5's --stats, so that the search
   * behavior can be compared against Z3's own -st output.
   */
  void registerStatistics();

  bool resourceLimitsExceeded() override
  {
    return d_prop.resourceLimitsExceeded();
  }

  bool getCancelFlag() override { return d_prop.getCancelFlag(); }

 protected:
  // --------------------------------------------- equality and congruence
  struct NewEq
  {
    ENode* d_lhs;
    ENode* d_rhs;
    EqJustification d_justification;
    NewEq(ENode* lhs, ENode* rhs, const EqJustification& js)
        : d_lhs(lhs), d_rhs(rhs), d_justification(js)
    {
    }
  };

  using ExprBoolPair = std::pair<Node, bool>;

  void removeParentsFromCgTable(ENode* r1);
  void reinsertParentsIntoCgTable(ENode* r1, ENode* r2);
  void mergeCgcGenerations(ENode* e1, uint32_t e1Generation, ENode* e2);
  void setGenerationSticky(ENode* e, uint32_t generation);
  void invertTrans(ENode* n);
  void propagateBoolENodeAssignment(ENode* r1, ENode* r2, ENode* n1, ENode* n2);
  void propagateBoolENodeAssignmentCore(ENode* source, ENode* target);
  void applyStickyUpdates(ENode* e1,
                          uint32_t e1Generation,
                          ENode* e2,
                          uint32_t e2Generation);

  void pushEq(ENode* lhs, ENode* rhs, const EqJustification& js)
  {
    if (lhs->getRoot() != rhs->getRoot())
    {
      d_eqPropagationQueue.push_back(NewEq(lhs, rhs, js));
    }
  }

  void pushNewCongruence(ENode* n1, ENode* n2, bool usedCommutativity)
  {
    Assert(n1->d_cg == n2);
    pushEq(n1, n2, EqJustification::mkCg(usedCommutativity));
  }

  bool addDiseq(ENode* n1, ENode* n2);
  bool isDiseqCore(ENode* n1, ENode* n2, bool checkDistinctRootValues) const;

  void assignQuantifier(TNode q);
  /**
   * Internalize body as internalizeInstance does, and record it for cvc5 as
   * an instance if instance is true, and otherwise as a lemma that holds
   * globally.
   */
  void internalizeLemma(TNode body, uint32_t generation, bool instance);

  void setConflict(const BJustification& js) { d_prop.setConflict(js); }

  void setConflict(const BJustification& js, Literal notL)
  {
    d_prop.setConflict(js, notL);
  }

  // ----------------------------------------------------------- the search
  bool propagateEqs();
  bool propagateAtoms();
  void propagateBoolVarENode(BoolVar v);

  // --------------------------------------------------------- backtracking

  // -------------------------------------------------------- internalization
  void updateGeneration(ENode* n);
  void updateGeneration(TNode e)
  {
    if (isApp(e) && eInternalized(e))
    {
      updateGeneration(getENode(e));
    }
  }
  void tsVisitChild(TNode n,
                    bool gateCtx,
                    std::vector<ExprBoolPair>& todo,
                    bool& visited);
  bool tsVisitChildren(TNode n, bool gateCtx, std::vector<ExprBoolPair>& todo);
  bool shouldInternalizeRec(TNode e) const;
  void topSortExpr(const Node* exprs,
                   size_t numExprs,
                   std::vector<ExprBoolPair>& sortedExprs);
  void internalizeDeep(TNode n);
  void internalizeDeep(const Node* exprs, size_t numExprs);
  void internalizeFormula(TNode n, bool gateCtx);
  void internalizeEq(TNode n, bool gateCtx);
  void internalizeDistinct(TNode n, bool gateCtx);
  void internalizeQuantifier(TNode q, bool gateCtx);
  void internalizeFormulaCore(TNode n, bool gateCtx);
  void setMergeTf(ENode* n, BoolVar v, bool isNewVar);
  void internalizeTerm(TNode n);
  void internalizeUninterpreted(TNode n);
  void undoMkENode();

  void init();
  void flush();

  // ------------------------------------------------------------- the fields
  Params& d_params;
  /**
   * The propositional side: the Boolean search state. It refers to d_params
   * and d_stats, so it is declared after them.
   */
  PropCore d_prop;
  Region d_region;
  QuantifierNormalizer d_normalizer;
  ConnectiveNormalizer d_connNormalizer;
  AssertionRewriter d_assertionRewriter;
  Nnf d_nnf;
  /** See setCvc5Preprocessor. */
  Cvc5Preprocessor d_cvc5Preprocessor;
  /** See setSkolemizer. */
  Skolemizer d_skolemizer;
  /** The justification of the equalities of cvc5's theories. */
  ExternalEqJustification d_externalJustification;
  std::unique_ptr<QuantifierManager> d_qmanager;

  /** The expressions already internalized as enodes. */
  std::vector<Node> d_eInternalizedStack;

  // ------------------------------------- equality and uninterpreted functions
  ENode* d_trueENode;
  ENode* d_falseENode;
  /** Maps the id of a term to its enode. */
  App2ENode d_app2ENode;
  ENodeVector d_enodes;
  /** Maps a declaration id to the enodes with that declaration. */
  std::vector<ENodeVector> d_decl2ENodes;
  std::unordered_map<TNode, uint32_t> d_declIds;
  ENodeVector d_emptyVector;
  CgTable d_cgTable;
  std::unordered_map<ENode*, uint32_t> d_stickyGenerationUpdates;
  /**
   * A temporary cache of parent generations, held between
   * removeParentsFromCgTable and reinsertParentsIntoCgTable.
   */
  std::vector<std::pair<ENode*, uint32_t>> d_r1ParentGenerations;
  std::vector<NewEq> d_eqPropagationQueue;
  /** An auxiliary enode used to find congruent equality atoms. */
  ENode* d_isDiseqTmp;
  Node d_isDiseqTmpExpr;
  TmpENode d_tmpENode;

  LiteralVector d_atomPropagationQueue;

  std::unordered_map<TNode, uint32_t> d_cachedGeneration;
  /**
   * Under cvc5's prop engine, the generation each term and quantifier had
   * when it was first internalized. cvc5 keeps the clauses whose atoms this
   * side deletes on backtracking, and asserts those atoms again later; they
   * are then internalized on demand, outside the reinitialization that
   * d_cachedGeneration serves, and take their generation from here.
   */
  std::unordered_map<Node, uint32_t> d_hostGeneration;
  /** The generation of n: cached, recorded under cvc5, or the current one. */
  uint32_t generationOf(TNode n);
  std::unordered_set<TNode> d_cacheGenerationVisited;

  // ------------------------------------------------------------ backtracking
  TrailStack d_trailStack;

  /** A temporary variable used during internalization. */
  uint32_t d_generation;

  /** Scratch space for the topological sort used by internalizeDeep. */
  std::vector<ExprBoolPair> d_tsTodo;
  std::vector<char> d_tcolors;
  std::vector<char> d_fcolors;

  /** The trail object that undoes mkENode. */
  class MkENodeTrail : public Trail
  {
   public:
    MkENodeTrail(SmtContext& ctx) : d_ctx(ctx) {}
    void undo() override { d_ctx.undoMkENode(); }

   private:
    SmtContext& d_ctx;
  };
  MkENodeTrail d_mkENodeTrail;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__SMT_CONTEXT_H */

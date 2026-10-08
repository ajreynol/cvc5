/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Internalization: turning formulas into the core's Boolean variables,
 * clauses and enodes.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_internalizer.cpp, and recast in cvc5 style.
 *
 * Note this is not a Tseitin CNF conversion in the usual sense: the Boolean
 * structure is internalized gate by gate, together with the relevancy watches
 * that decide which arguments of each gate the current assignment has to
 * justify. That coupling is why the core does its own internalization rather
 * than reusing cvc5's CnfStream.
 */

#include <algorithm>

#include "base/output.h"
#include "expr/node_algorithm.h"
#include "expr/node_manager.h"
#include "smt/env.h"
#include "theory/theory.h"
#include "z3/quantifier_manager.h"
#include "z3/smt_context.h"
#include "z3/util/util.h"

namespace cvc5::internal {
namespace z3 {

namespace {

/** True if the expression is viewed as a logical gate. */
bool isGate(TNode n)
{
  switch (n.getKind())
  {
    case Kind::AND:
    case Kind::OR:
    case Kind::ITE: return true;
    case Kind::EQUAL: return n[0].getType().isBoolean();
    default: return false;
  }
}

bool isTrueNode(TNode n)
{
  return n.getKind() == Kind::CONST_BOOLEAN && n.getConst<bool>();
}

bool isFalseNode(TNode n)
{
  return n.getKind() == Kind::CONST_BOOLEAN && !n.getConst<bool>();
}

/** An if-then-else over terms, rather than over formulas. */
bool isTermIte(TNode n)
{
  return n.getKind() == Kind::ITE && !n.getType().isBoolean();
}

constexpr char s_white = 0;
constexpr char s_grey = 1;
constexpr char s_black = 2;

char getColor(std::vector<char>& tcolors,
              std::vector<char>& fcolors,
              TNode n,
              bool gateCtx)
{
  std::vector<char>& colors = gateCtx ? tcolors : fcolors;
  if (colors.size() > n.getId())
  {
    return colors[n.getId()];
  }
  return s_white;
}

void setColor(std::vector<char>& tcolors,
              std::vector<char>& fcolors,
              TNode n,
              bool gateCtx,
              char color)
{
  std::vector<char>& colors = gateCtx ? tcolors : fcolors;
  if (colors.size() <= n.getId())
  {
    colors.resize(n.getId() + 1, s_white);
  }
  colors[n.getId()] = color;
}

/**
 * The foreign descendants of n: the descendants whose theory differs from
 * fid. For example the foreign descendants of (+ a (+ (f b) (* 2 (h (+ c
 * d))))) are a, (f b) and (h (+ c d)).
 */
void getForeignDescendants(TNode n,
                           TheoryId fid,
                           std::vector<Node>& descendants)
{
  std::vector<Node> todo{n};
  std::unordered_set<Node> visited;
  while (!todo.empty())
  {
    Node curr = todo.back();
    todo.pop_back();
    if (!visited.insert(curr).second)
    {
      continue;
    }
    if (!isApp(curr) || familyIdOf(curr) != fid)
    {
      descendants.push_back(curr);
      continue;
    }
    size_t j = curr.getNumChildren();
    while (j > 0)
    {
      --j;
      todo.push_back(curr[j]);
    }
  }
}

/** The threshold above which internalization switches to a topological sort. */
constexpr uint32_t s_deepExprThreshold = 1024;

/**
 * Above this many arguments, Z3 encodes a distinct with auxiliary values
 * instead of expanding it. cvc5's rewriter normally eliminates distinct
 * before the core sees it, so this path is not expected to be reached.
 */
constexpr size_t s_distinctSzThreshold = 32;

}  // namespace

void SmtContext::updateGeneration(ENode* e)
{
  // Patterns with equalities are not supported, so there is no need to track
  // the generation of equality nodes.
  if (e->isEq())
  {
    return;
  }

  if (0 < d_generation && d_generation < getGeneration(e))
  {
    if (e->usesCgTable())
    {
      setGenerationSticky(e, d_generation);
    }
    else
    {
      setGeneration(e, d_generation);
    }
  }
}

namespace {

/** Undoes a congruence class generation merge. */
class MergeCgcGenerationsTrail : public Trail
{
 public:
  MergeCgcGenerationsTrail(SmtContext& ctx,
                           ENode* e1,
                           uint32_t e1Generation,
                           ENode* e2,
                           uint32_t e2Generation)
      : d_ctx(ctx),
        d_e1(e1),
        d_e1Generation(e1Generation),
        d_e2(e2),
        d_e2Generation(e2Generation)
  {
  }

  void undo() override
  {
    d_ctx.undoMergeCgcGenerations(d_e1, d_e1Generation, d_e2, d_e2Generation);
  }

 private:
  SmtContext& d_ctx;
  ENode* d_e1;
  uint32_t d_e1Generation;
  ENode* d_e2;
  uint32_t d_e2Generation;
};

}  // namespace

void SmtContext::mergeCgcGenerations(ENode* e1,
                                     uint32_t e1Generation,
                                     ENode* e2)
{
  Assert(e2->isCgr());
  Assert(!d_cgTable.containsPtr(e1));
  Assert(d_cgTable.containsPtr(e2));

  // Push the trail even for a no-op, otherwise e1's generation could not be
  // restored when the merge is undone.
  pushTrail(
      MergeCgcGenerationsTrail(*this, e1, e1Generation, e2, e2->d_generation));

  if (e1Generation >= e2->d_generation)
  {
    return;  // a no-op
  }

  e2->d_generation = e1Generation;
}

void SmtContext::tsVisitChild(TNode n,
                              bool gateCtx,
                              std::vector<ExprBoolPair>& todo,
                              bool& visited)
{
  if (getColor(d_tcolors, d_fcolors, n, gateCtx) == s_white)
  {
    todo.push_back(ExprBoolPair(n, gateCtx));
    visited = false;
  }
}

bool SmtContext::tsVisitChildren(TNode n,
                                 bool /*gateCtx*/,
                                 std::vector<ExprBoolPair>& todo)
{
  if (isQuantifier(n))
  {
    return true;
  }
  if (!shouldInternalizeRec(n))
  {
    return true;
  }
  Assert(isApp(n));
  if (n.getType().isBoolean())
  {
    if (bInternalized(n))
    {
      updateGeneration(n);
      return true;
    }
  }
  else
  {
    updateGeneration(n);
    if (eInternalized(n))
    {
      return true;
    }
  }

  bool visited = true;
  TheoryId fid = familyIdOf(n);
  Theory* th = getTheory(fid);
  bool defInt = th == nullptr || th->defaultInternalizer();
  if (!defInt)
  {
    std::vector<Node> descendants;
    getForeignDescendants(n, fid, descendants);
    for (const Node& arg : descendants)
    {
      tsVisitChild(arg, false, todo, visited);
    }
    return visited;
  }

  if (isTermIte(n))
  {
    tsVisitChild(n[0], true, todo, visited);
    tsVisitChild(n[1], false, todo, visited);
    tsVisitChild(n[2], false, todo, visited);
    return visited;
  }
  bool newGateCtx =
      n.getType().isBoolean() && (isGate(n) || n.getKind() == Kind::NOT);
  size_t j = n.getNumChildren();
  while (j > 0)
  {
    --j;
    tsVisitChild(n[j], newGateCtx, todo, visited);
  }
  return visited;
}

void SmtContext::topSortExpr(const Node* exprs,
                             size_t numExprs,
                             std::vector<ExprBoolPair>& sortedExprs)
{
  d_tcolors.clear();
  d_fcolors.clear();
  while (!d_tsTodo.empty())
  {
    ExprBoolPair& p = d_tsTodo.back();
    Node curr = p.first;
    bool gateCtx = p.second;
    switch (getColor(d_tcolors, d_fcolors, curr, gateCtx))
    {
      case s_white:
        setColor(d_tcolors, d_fcolors, curr, gateCtx, s_grey);
        tsVisitChildren(curr, gateCtx, d_tsTodo);
        break;
      case s_grey:
      {
        setColor(d_tcolors, d_fcolors, curr, gateCtx, s_black);
        const Node* end = exprs + numExprs;
        if (std::find(exprs, end, curr) == end && curr.getKind() != Kind::NOT
            && shouldInternalizeRec(curr))
        {
          sortedExprs.push_back(ExprBoolPair(curr, gateCtx));
        }
        break;
      }
      case s_black: d_tsTodo.pop_back(); break;
      default: Unreachable();
    }
  }
}

bool SmtContext::shouldInternalizeRec(TNode e) const
{
  if (!isApp(e) || !e.getType().isBoolean())
  {
    return true;
  }
  TheoryId fid = familyIdOf(e);
  return fid == theory::THEORY_UF || fid == theory::THEORY_BOOL
         || fid == theory::THEORY_BUILTIN;
}

void SmtContext::internalizeDeep(const Node* exprs, size_t numExprs)
{
  d_tsTodo.clear();
  for (size_t i = 0; i < numExprs; ++i)
  {
    TNode n = exprs[i];
    if (!eInternalized(n) && getDepth(n) > s_deepExprThreshold
        && shouldInternalizeRec(n))
    {
      // A deep expression is internalized through a topological sort, to
      // avoid overflowing the stack. Note the theory internalizers do rely on
      // recursive descent, so internalization over them stays top-down.
      d_tsTodo.push_back(ExprBoolPair(n, true));
    }
  }

  std::vector<ExprBoolPair> sortedExprs;
  topSortExpr(exprs, numExprs, sortedExprs);
  for (const ExprBoolPair& eb : sortedExprs)
  {
    Assert(shouldInternalizeRec(eb.first));
    internalizeRec(eb.first, eb.second);
  }
}

void SmtContext::internalizeDeep(TNode n)
{
  Node v[1] = {n};
  internalizeDeep(v, 1);
}

void SmtContext::internalizeAssertion(TNode n, uint32_t generation)
{
  uint32_t oldGeneration = d_generation;
  d_generation = generation;
  d_stats.d_maxGeneration =
      std::max<uint64_t>(generation, d_stats.d_maxGeneration);
  internalizeDeep(n);
  Assert(n.getType().isBoolean());
  if (isGate(n))
  {
    switch (n.getKind())
    {
      case Kind::AND:
      {
        for (const Node& arg : n)
        {
          internalizeRec(arg, true);
          Literal lit = getLiteral(arg);
          mkRootClause(1, &lit);
        }
        break;
      }
      case Kind::OR:
      {
        LiteralVector lits;
        for (const Node& arg : n)
        {
          internalizeRec(arg, true);
          lits.push_back(getLiteral(arg));
        }
        mkRootClause(lits.size(), lits.data());
        addOrRelWatches(n);
        break;
      }
      case Kind::EQUAL:
      {
        TNode lhs = n[0];
        TNode rhs = n[1];
        internalizeRec(lhs, true);
        internalizeRec(rhs, true);
        Literal l1 = getLiteral(lhs);
        Literal l2 = getLiteral(rhs);
        mkRootClause(l1, ~l2);
        mkRootClause(~l1, l2);
        break;
      }
      case Kind::ITE:
      {
        TNode c = n[0];
        TNode t = n[1];
        TNode e = n[2];
        internalizeRec(c, true);
        internalizeRec(t, true);
        internalizeRec(e, true);
        Literal cl = getLiteral(c);
        Literal tl = getLiteral(t);
        Literal el = getLiteral(e);
        mkRootClause(~cl, tl);
        mkRootClause(cl, el);
        addIteRelWatches(n);
        break;
      }
      default: Unreachable();
    }
    markAsRelevant(n);
  }
  else if (n.getKind() == Kind::DISTINCT)
  {
    assertDistinct(n);
    markAsRelevant(n);
  }
  else
  {
    assertDefault(n);
  }
  d_generation = oldGeneration;
}

void SmtContext::assertDefault(TNode n)
{
  internalize(n, true);
  Literal l = getLiteral(n);
  if (l == s_falseLiteral)
  {
    setConflict(BJustification::mkAxiom());
  }
  else if (l == s_trueLiteral)
  {
    return;
  }
  else
  {
    assign(l, BJustification::mkAxiom());
    markAsRelevant(l);
  }
}

void SmtContext::assertDistinct(TNode n)
{
  // Z3 encodes a very large distinct with auxiliary values over a fresh sort.
  // cvc5's rewriter expands distinct during preprocessing, so the core is not
  // expected to meet one at all, let alone a large one; the plain encoding is
  // used in either case.
  assertDefault(n);
}

void SmtContext::internalize(TNode n, bool gateCtx, uint32_t generation)
{
  uint32_t oldGeneration = d_generation;
  d_generation = generation;
  d_stats.d_maxGeneration =
      std::max<uint64_t>(generation, d_stats.d_maxGeneration);
  internalizeRec(n, gateCtx);
  d_generation = oldGeneration;
}

void SmtContext::ensureInternalized(TNode e)
{
  if (!eInternalized(e))
  {
    internalize(e, false);
  }
  if (isApp(e) && !e.getType().isBoolean())
  {
    internalizeTerm(e);
  }
}

void SmtContext::internalize(TNode n, bool gateCtx)
{
  internalizeDeep(n);
  internalizeRec(n, gateCtx);
}

void SmtContext::internalize(const Node* exprs, size_t numExprs, bool gateCtx)
{
  internalizeDeep(exprs, numExprs);
  for (size_t i = 0; i < numExprs; ++i)
  {
    internalizeRec(exprs[i], gateCtx);
  }
}

ENode* SmtContext::nonGroundInternalize(TNode e)
{
  if (eInternalized(e))
  {
    return getENode(e);
  }
  if (!expr::hasBoundVar(e))
  {
    internalize(e, false);
    return getENode(e);
  }
  // The term has bound variables, so it cannot be given an enode directly.
  // Represent it by a fresh proxy constant constrained to be equal to it.
  Node fn = NodeManager::mkDummySkolem("z3proxy", e.getType());
  Node eq = nodeManager()->mkNode(Kind::EQUAL, fn, e);
  assertFormula(eq);
  internalizeAssertions();
  if (!eInternalized(fn))
  {
    internalize(fn, false);
  }
  return getENode(fn);
}

void SmtContext::internalizeRec(TNode n, bool gateCtx)
{
  if (isVar(n))
  {
    Unreachable() << "z3: formulas should not contain unbound variables";
  }
  if (n.getType().isBoolean())
  {
    Assert(isQuantifier(n) || isApp(n));
    internalizeFormula(n, gateCtx);
  }
  else
  {
    Assert(isApp(n));
    internalizeTerm(n);
  }
}

void SmtContext::internalizeFormula(TNode n, bool gateCtx)
{
  Assert(n.getType().isBoolean());
  if (isTrueNode(n) || isFalseNode(n))
  {
    return;
  }

  if (n.getKind() == Kind::NOT && gateCtx)
  {
    // A Boolean variable is not needed for a NOT gate inside a gate context.
    internalizeRec(n[0], true);
    return;
  }

  if (bInternalized(n))
  {
    // n was already internalized as a Boolean.
    BoolVar v = getBoolVar(n);

    updateGeneration(n);

    // An enode is still necessary if n is not in a gate context and is an
    // application.
    if (!gateCtx && isApp(n))
    {
      if (eInternalized(n))
      {
        ENode* e = getENode(n);
        setMergeTf(e, v, false);
      }
      else
      {
        mkENode(n,
                true, /* suppress the arguments: congruence is not used here */
                true, /* merge with true/false, since this is not a gate */
                false /* congruence closure is not enabled */);
        setEnodeFlag(v, false);
        if (getAssignment(v) != L_UNDEF)
        {
          propagateBoolVarENode(v);
        }
      }
      Assert(hasENode(v));
    }
    return;
  }

  if (n.getKind() == Kind::EQUAL && !n[0].getType().isBoolean())
  {
    internalizeEq(n, gateCtx);
  }
  else if (n.getKind() == Kind::DISTINCT)
  {
    internalizeDistinct(n, gateCtx);
  }
  else if (isApp(n) && internalizeTheoryAtom(n, gateCtx))
  {
    return;
  }
  else if (isQuantifier(n))
  {
    internalizeQuantifier(n, gateCtx);
  }
  else
  {
    internalizeFormulaCore(n, gateCtx);
  }
}

void SmtContext::internalizeEq(TNode n, bool gateCtx)
{
  Assert(!bInternalized(n));
  Assert(n.getKind() == Kind::EQUAL);
  internalizeFormulaCore(n, gateCtx);
  BoolVar v = getBoolVar(n);
  BoolVarData& d = getBdata(v);
  d.setEqFlag();

  Theory* th = getTheory(theory::Theory::theoryOf(n[0].getType()));
  if (th != nullptr)
  {
    th->internalizeEqEh(n, v);
  }
}

void SmtContext::internalizeDistinct(TNode n, bool gateCtx)
{
  Assert(!bInternalized(n));
  Assert(n.getKind() == Kind::DISTINCT);
  BoolVar v = mkBoolVar(n);
  Literal l(v);
  // the pairwise expansion of the distinct
  std::vector<Node> diseqs;
  size_t numArgs = n.getNumChildren();
  for (size_t i = 0; i < numArgs; ++i)
  {
    for (size_t j = i + 1; j < numArgs; ++j)
    {
      diseqs.push_back(nodeManager()->mkNode(
          Kind::NOT, nodeManager()->mkNode(Kind::EQUAL, n[i], n[j])));
    }
  }
  Node def =
      diseqs.size() == 1 ? diseqs[0] : nodeManager()->mkNode(Kind::AND, diseqs);
  internalizeRec(def, true);
  Literal lDef = getLiteral(def);
  mkGateClause(~l, lDef);
  mkGateClause(l, ~lDef);
  // Reference counts of negations are not tracked, so a relevancy dependency
  // on the equality is added instead.
  Node relDef = def.getKind() == Kind::NOT ? def[0] : def;
  addRelevancyDependency(n, relDef);
  if (!gateCtx)
  {
    mkENode(n, true, true, false);
    setEnodeFlag(v, true);
    // v may have been assigned by the definition clauses before the enode
    // was created.
    if (getAssignment(v) != L_UNDEF)
    {
      propagateBoolVarENode(v);
    }
  }
}

bool SmtContext::internalizeTheoryAtom(TNode n, bool gateCtx)
{
  Assert(!bInternalized(n));
  Theory* th = getTheory(familyIdOf(n));
  if (th == nullptr || !th->internalizeAtom(n, gateCtx))
  {
    return false;
  }
  Assert(bInternalized(n));
  BoolVar v = getBoolVar(n);
  if (!gateCtx)
  {
    // Outside a gate context the formula must be associated with an enode.
    if (!eInternalized(n))
    {
      mkENode(n,
              true, /* suppress the arguments: congruence is not used here */
              true, /* merge with true/false, since this is not a gate */
              false /* congruence closure is not enabled */);
    }
    else
    {
      ENode* e = getENode(n);
      setEnodeFlag(v, true);
      setMergeTf(e, v, true);
    }
  }
  if (eInternalized(n))
  {
    setEnodeFlag(v, true);
    if (getAssignment(v) != L_UNDEF)
    {
      propagateBoolVarENode(v);
    }
  }
  return true;
}

void SmtContext::internalizeQuantifier(TNode q, bool gateCtx)
{
  (void)gateCtx;
  Assert(gateCtx);  // a limitation of the current implementation
  Assert(!bInternalized(q));
  if (q.getKind() != Kind::FORALL)
  {
    Unreachable() << "z3: internalization of exists is not supported";
  }
  BoolVar v = mkBoolVar(q);
  uint32_t generation = d_generation;
  auto it = d_cachedGeneration.find(q);
  if (it != d_cachedGeneration.end())
  {
    generation = it->second;
  }
  BoolVarData& d = getBdata(v);
  d.setQuantifierFlag();
  d_qmanager->add(q, generation);
}

void SmtContext::internalizeFormulaCore(TNode n, bool gateCtx)
{
  // Internalize gates, and the (uninterpreted and equality) predicates.
  Assert(!bInternalized(n));
  Assert(!eInternalized(n));

  checkTheorySupported(n);
  bool isGateN = isGate(n) || n.getKind() == Kind::NOT;
  // process the arguments
  for (const Node& arg : n)
  {
    internalizeRec(arg, isGateN);
  }

  bool isNewVar = false;
  BoolVar v;
  // n may already be internalized once its children are, for example the
  // equality in (= (ite c 1 0) 1): internalizing the ite term forces both
  // (= (ite c 1 0) 1) and (= (ite c 1 0) 0).
  if (!bInternalized(n))
  {
    isNewVar = true;
    v = mkBoolVar(n);
  }
  else
  {
    v = getBoolVar(n);
  }

  // A formula needs an enode when it is not in a gate context, or when it has
  // arguments and is not a gate (i.e. an uninterpreted predicate or an
  // equality).
  if (!eInternalized(n) && (!gateCtx || (!isGateN && n.getNumChildren() > 0)))
  {
    bool suppressArgs = isGateN || n.getKind() == Kind::NOT;
    bool mergeTf = !gateCtx;
    mkENode(n, suppressArgs, mergeTf, true);
    setEnodeFlag(v, isNewVar);
    Assert(hasENode(v));
  }
  else if (!gateCtx && eInternalized(n))
  {
    // n was internalized in a gate context while its children were being
    // internalized (ite-term axioms, for example), but it now occurs outside
    // a gate and must be merged with true/false.
    setMergeTf(getENode(n), v, isNewVar);
  }

  // The constraints of n must be asserted after its Boolean variable and
  // enode exist. Otherwise completeness is lost: an assigned Boolean variable
  // only enters the atom propagation queue when isAtom() holds, and creating
  // the constraints may force v to be assigned.
  if (!isNewVar)
  {
    return;
  }
  switch (n.getKind())
  {
    case Kind::NOT:
      Assert(!gateCtx);
      mkNotCnstr(n);
      break;
    case Kind::AND:
      mkAndCnstr(n);
      addAndRelWatches(n);
      break;
    case Kind::OR:
      mkOrCnstr(n);
      addOrRelWatches(n);
      break;
    case Kind::IMPLIES:
      mkImpliesCnstr(n);
      addImpliesRelWatches(n);
      break;
    case Kind::EQUAL:
      if (n[0].getType().isBoolean())
      {
        mkIffCnstr(n, false);
      }
      break;
    case Kind::ITE:
      mkIteCnstr(n);
      addIteRelWatches(n);
      break;
    case Kind::XOR: mkIffCnstr(n, true); break;
    case Kind::CONST_BOOLEAN: break;
    case Kind::DISTINCT:
      Unreachable() << "z3: formula has not been simplified: " << n;
    default: break;
  }
}

namespace {

/** Clears the merge-with-true/false flag of an enode. */
class SetMergeTfTrail : public Trail
{
 public:
  SetMergeTfTrail(ENode* n) : d_node(n) {}
  void undo() override { d_node->resetMergeTf(); }

 private:
  ENode* d_node;
};

/** Clears the has-enode flag of a Boolean variable. */
class SetENodeFlagTrail : public Trail
{
 public:
  SetENodeFlagTrail(SmtContext& ctx, BoolVar v) : d_ctx(ctx), d_var(v) {}
  void undo() override { d_ctx.getBdata(d_var).resetENodeFlag(); }

 private:
  SmtContext& d_ctx;
  BoolVar d_var;
};

}  // namespace

void SmtContext::setMergeTf(ENode* n, BoolVar v, bool isNewVar)
{
  // With the merge-tf flag set, n is merged with the true (false) enode
  // whenever v is assigned true (false).
  Assert(boolVar2ENode(v) == n);
  if (n->d_mergeTf)
  {
    return;
  }
  if (!isNewVar)
  {
    pushTrail(SetMergeTfTrail(n));
  }
  n->d_mergeTf = true;
  switch (getAssignment(v))
  {
    case L_UNDEF: break;
    case L_TRUE:
      if (n->getRoot() != d_trueENode->getRoot())
      {
        pushEq(n, d_trueENode, EqJustification(Literal(v, false)));
      }
      break;
    case L_FALSE:
      if (n->getRoot() != d_falseENode->getRoot())
      {
        pushEq(n, d_falseENode, EqJustification(Literal(v, true)));
      }
      break;
  }
}

void SmtContext::setEnodeFlag(BoolVar v, bool isNewVar)
{
  Assert(eInternalized(boolVar2Expr(v)));
  BoolVarData& data = d_bdata[v];
  if (!data.isENode())
  {
    if (!isNewVar)
    {
      pushTrail(SetENodeFlagTrail(*this, v));
    }
    data.setENodeFlag();
  }
}

void SmtContext::internalizeTerm(TNode n)
{
  if (eInternalized(n))
  {
    ENode* e = getENode(n);
    updateGeneration(e);
    Theory* th = getTheory(familyIdOf(n));
    if (th != nullptr)
    {
      // Some theories decide not to create theory variables for a nested
      // application. For example, arithmetic internalizing (+ (* 2 x) y)
      // creates enodes for both applications but a theory variable only for
      // the +, keeping (* 2 x) internal to arithmetic. If the core later
      // internalizes (f (* 2 x)), the term is no longer internal and does
      // need a theory variable.
      if (!th->isAttachedToVar(e))
      {
        th->internalizeTerm(n);
      }
    }
    return;
  }

  if (isTermIte(n))
  {
    internalizeIteTerm(n);
    return;  // the sort constraint is applied by internalizeIteTerm
  }
  if (!internalizeTheoryTerm(n))
  {
    internalizeUninterpreted(n);
  }
  Assert(eInternalized(n));
  applySortCnstr(n, getENode(n));
}

void SmtContext::internalizeIteTerm(TNode n)
{
  Assert(!eInternalized(n));
  TNode c = n[0];
  TNode t = n[1];
  TNode e = n[2];
  Node eq1 = mkEqAtom(n, t);
  Node eq2 = mkEqAtom(n, e);
  mkENode(n,
          true,  /* suppress the arguments: congruence is not used on ites */
          false, /* a term, so it is not merged with true/false */
          false /* congruence closure is not enabled */);
  internalizeRec(c, true);
  internalizeRec(t, false);
  internalizeRec(e, false);
  internalizeRec(eq1, true);
  internalizeRec(eq2, true);
  Literal cLit = getLiteral(c);
  Literal eq1Lit = getLiteral(eq1);
  Literal eq2Lit = getLiteral(eq2);
  mkGateClause(~cLit, eq1Lit);
  mkGateClause(cLit, eq2Lit);
  if (relevancy())
  {
    RelevancyEh* eh = d_relevancyPropagator->mkTermIteRelevancyEh(n, eq1, eq2);
    addRelWatch(cLit, eh);
    addRelWatch(~cLit, eh);
    addRelevancyEh(n, eh);
  }
  Assert(eInternalized(n));
}

bool SmtContext::internalizeTheoryTerm(TNode n)
{
  Theory* th = getTheory(familyIdOf(n));
  return th != nullptr && th->internalizeTerm(n);
}

void SmtContext::checkTheorySupported(TNode n)
{
  TheoryId fid = familyIdOf(n);
  // The core reasons about these itself: Boolean structure, equality and
  // congruence over uninterpreted symbols.
  if (fid == theory::THEORY_BOOL || fid == theory::THEORY_BUILTIN
      || fid == theory::THEORY_UF || fid == s_nullTheoryId)
  {
    return;
  }
  if (getTheory(fid) == nullptr)
  {
    markModelUnsound(fid);
  }
}

void SmtContext::internalizeUninterpreted(TNode n)
{
  Assert(!eInternalized(n));
  checkTheorySupported(n);
  // process the arguments
  for (const Node& arg : n)
  {
    internalizeRec(arg, false);
    Assert(eInternalized(arg));
  }
  if (eInternalized(n))
  {
    return;
  }

  ENode* e = mkENode(n,
                     false, /* do not suppress the arguments */
                     false, /* a term, so it is not merged with true/false */
                     true);
  applySortCnstr(n, e);
}

BoolVar SmtContext::mkBoolVar(TNode n)
{
  Assert(!bInternalized(n));
  size_t id = n.getId();
  BoolVar v = static_cast<BoolVar>(d_bInternalizedStack.size());
  setBoolVar(id, v);
  reservex(d_bdata, v + 1, BoolVarData());
  reservex(d_activity, v + 1, 0.0);
  reservex(d_boolVar2Expr, v + 1, Node::null());
  d_boolVar2Expr[v] = n;
  reservex(d_litScores[0], v + 1, 0.0);
  reservex(d_litScores[1], v + 1, 0.0);
  d_litScores[0][v] = 0.0;
  d_litScores[1][v] = 0.0;
  reservex(d_birthdate, v + 1, static_cast<uint64_t>(0));
  d_birthdate[v] = 0;

  Literal l(v, false);
  Literal notL(v, true);
  size_t aux = std::max(l.index(), notL.index()) + 1;
  reservex(d_assignment, aux, static_cast<int8_t>(L_UNDEF));
  d_assignment[l.index()] = L_UNDEF;
  d_assignment[notL.index()] = L_UNDEF;
  if (d_watches.size() < aux)
  {
    d_watches.resize(aux);
  }
  Assert(d_assignment.size() == d_watches.size());
  d_watches[l.index()].reset();
  d_watches[notL.index()].reset();
  reservex(d_litOccs, aux, static_cast<uint32_t>(0));
  d_litOccs[l.index()] = 0;
  d_litOccs[notL.index()] = 0;
  BoolVarData& data = d_bdata[v];
  // record the level at which the variable was internalized
  data.init(d_scopeLvl);
  if (d_params.d_randomInitialActivity == IA_RANDOM
      || (d_params.d_randomInitialActivity == IA_RANDOM_WHEN_SEARCHING
          && d_searching))
  {
    d_activity[v] = -((d_random() % 1000) / 1000.0);
  }
  else
  {
    d_activity[v] = 0.0;
  }
  d_caseSplitQueue->mkVarEh(v);
  d_bInternalizedStack.push_back(n);
  d_trailStack.pushPtr(&d_mkBoolVarTrail);
  d_stats.d_numMkBoolVar++;
  return v;
}

void SmtContext::addScores(size_t n, const Literal* lits)
{
  for (size_t i = 0; i < n; ++i)
  {
    Literal lit = lits[i];
    d_litScores[lit.sign() ? 1 : 0][lit.var()] += 1.0 / n;
  }
}

void SmtContext::undoMkBoolVar()
{
  Assert(!d_bInternalizedStack.empty());
  d_stats.d_numDelBoolVar++;
  Node n = d_bInternalizedStack.back();
  size_t nId = n.getId();
  BoolVar v = getBoolVarOfId(nId);
  d_boolVar2Expr[v] = Node::null();
  d_caseSplitQueue->delVarEh(v);
  if (isQuantifier(n))
  {
    d_qmanager->del(n);
  }
  setBoolVar(nId, s_nullBoolVar);
  d_bInternalizedStack.pop_back();
}

ENode* SmtContext::mkENode(TNode n,
                           bool suppressArgs,
                           bool mergeTf,
                           bool cgcEnabled)
{
  Assert(!eInternalized(n));
  size_t id = n.getId();
  uint32_t generation = d_generation;
  auto itg = d_cachedGeneration.find(n);
  if (itg != d_cachedGeneration.end())
  {
    generation = itg->second;
  }
  ENode* e = ENode::mk(getRegion(),
                       d_app2ENode,
                       n,
                       generation,
                       suppressArgs,
                       mergeTf,
                       d_scopeLvl,
                       cgcEnabled,
                       true);
  if (n.isConst())
  {
    e->markAsInterpreted();
  }
  setx(d_app2ENode, id, e, static_cast<ENode*>(nullptr));
  d_eInternalizedStack.push_back(n);
  d_trailStack.pushPtr(&d_mkENodeTrail);
  d_enodes.push_back(e);
  if (e->getNumArgs() > 0)
  {
    if (e->isTrueEq())
    {
      BoolVar v = enode2BoolVar(e);
      assign(Literal(v),
             mkJustification(
                 EqPropagationJustification(e->getArg(0), e->getArg(1))));
      e->d_cg = e;
      pushEq(e, d_trueENode, EqJustification());
    }
    else if (cgcEnabled)
    {
      ENodeBoolPair r = d_cgTable.insert(e);
      if (e != r.first)
      {
        e->d_cg = r.first;
        // Patterns with equalities are not supported, so equality
        // generations are not tracked.
        if (!e->isEq())
        {
          mergeCgcGenerations(e, generation, r.first);
        }
        pushNewCongruence(e, r.first, r.second);
      }
      else
      {
        e->d_cg = e;
      }
    }
    else
    {
      e->d_cg = e;
    }
    if (!e->isEq())
    {
      uint32_t declId = getDeclId(e->getDecl());
      if (declId >= d_decl2ENodes.size())
      {
        d_decl2ENodes.resize(declId + 1);
      }
      d_decl2ENodes[declId].push_back(e);
    }
  }

  Assert(eInternalized(n));
  d_stats.d_numMkENode++;
  return e;
}

void SmtContext::undoMkENode()
{
  Assert(!d_eInternalizedStack.empty());
  d_stats.d_numDelENode++;
  Node n = d_eInternalizedStack.back();
  size_t nId = n.getId();
  ENode* e = d_app2ENode[nId];
  d_app2ENode[nId] = nullptr;
  if (e->isCgr() && e->usesCgTable())
  {
    Assert(d_cgTable.containsPtr(e));
    d_cgTable.erase(e);
  }
  if (e->getNumArgs() > 0 && !e->isEq())
  {
    uint32_t declId = getDeclId(e->getDecl());
    Assert(declId < d_decl2ENodes.size());
    Assert(d_decl2ENodes[declId].back() == e);
    d_decl2ENodes[declId].pop_back();
  }
  e->delEh();
  Assert(d_eInternalizedStack.size() == d_enodes.size());
  d_enodes.pop_back();
  d_eInternalizedStack.pop_back();
  d_stickyGenerationUpdates.erase(e);
}

void SmtContext::applySortCnstr(TNode term, ENode* e)
{
  TypeNode s = term.getType();
  Theory* th = getTheory(theory::Theory::theoryOf(s));
  if (th != nullptr)
  {
    th->applySortCnstr(e, s);
  }
}

bool SmtContext::simplifyAuxClauseLiterals(size_t& numLits,
                                           Literal* lits,
                                           LiteralVector& simpLits)
{
  // Simplify the literals of a transient (auxiliary) clause using the current
  // assignment, which is safe because such clauses are deleted on
  // backtracking. Duplicates and false literals are removed; the clause is
  // reported as equivalent to true (by returning false) if it contains a true
  // literal or both l and ~l.
  std::sort(lits, lits + numLits);
  Literal prev = s_nullLiteral;
  size_t j = 0;
  for (size_t i = 0; i < numLits; ++i)
  {
    Literal curr = lits[i];
    switch (getAssignment(curr))
    {
      case L_FALSE:
        if (curr != prev)
        {
          prev = curr;
          simpLits.push_back(~curr);
        }
        break;  // ignore the literal
      case L_UNDEF:
        if (curr == ~prev)
        {
          return false;  // the clause is equivalent to true
        }
        if (curr != prev)
        {
          prev = curr;
          if (i != j)
          {
            lits[j] = lits[i];
          }
          j++;
        }
        break;
      case L_TRUE: return false;  // the clause is equivalent to true
    }
  }
  numLits = j;
  return true;
}

bool SmtContext::simplifyAuxLemmaLiterals(size_t& numLits, Literal* lits)
{
  // An auxiliary lemma has the status of a learned clause but was not
  // produced by conflict resolution; a dynamic Ackermann clause is one
  // example. Literals assigned false at the base level are *not* removed,
  // because that would need a justification for the simplification.
  std::sort(lits, lits + numLits);
  Literal prev = s_nullLiteral;
  size_t i = 0;
  size_t j = 0;
  for (; i < numLits; ++i)
  {
    Literal curr = lits[i];
    BoolVar var = curr.var();
    LBool val = L_UNDEF;
    if (getAssignLevel(var) <= d_baseLvl)
    {
      val = getAssignment(curr);
    }
    if (val == L_TRUE)
    {
      return false;  // the clause is equivalent to true
    }
    if (curr == ~prev)
    {
      return false;  // the clause is equivalent to true
    }
    if (curr != prev)
    {
      prev = curr;
      if (i != j)
      {
        lits[j] = lits[i];
      }
      j++;
    }
  }
  numLits = j;
  return true;
}

void SmtContext::markForReinit(Clause* cls,
                               uint32_t scopeLvl,
                               bool reinternalizeAtoms)
{
  // A clause may need reinitialization for two reasons. First, it may contain
  // literals created during the search, whose maximum internalization level
  // is scopeLvl; since the clause can outlive that level it has to be rebuilt
  // (reinternalizeAtoms is true in that case). Second, an auxiliary lemma may
  // have been in conflict or propagating when it was created, which has to be
  // rechecked after backtracking.
  Assert(scopeLvl >= d_baseLvl);
  cls->d_reinit = true;
  cls->d_reinternalizeAtoms = reinternalizeAtoms;
  if (scopeLvl >= d_clausesToReinit.size())
  {
    d_clausesToReinit.resize(scopeLvl + 1);
  }
  d_clausesToReinit[scopeLvl].push_back(cls);
}

uint32_t SmtContext::getMaxIscopeLvl(size_t numLits, const Literal* lits) const
{
  uint32_t r = 0;
  for (size_t i = 0; i < numLits; ++i)
  {
    uint32_t ilvl = getInternLevel(lits[i].var());
    if (ilvl > r)
    {
      r = ilvl;
    }
  }
  return r;
}

bool SmtContext::useBinaryClauseOpt(Literal l1, Literal l2, bool lemma) const
{
  if (!binaryClauseOptEnabled())
  {
    return false;
  }
  // With relevancy enabled, binary clauses must not be used: when a learned
  // clause becomes unit it has to mark the unit literal relevant, and the
  // binary clause encoding cannot distinguish learned from non-learned
  // clauses.
  if (lemma && relevancyLvl() >= 2)
  {
    return false;
  }
  if (d_baseLvl > 0)
  {
    return false;
  }
  if (!lemma && d_scopeLvl > 0)
  {
    return false;
  }
  if (getInternLevel(l1.var()) > 0)
  {
    return false;
  }
  if (getInternLevel(l2.var()) > 0)
  {
    return false;
  }
  return true;
}

int SmtContext::selectLearnedWatchLit(const Clause* cls) const
{
  // The learned clauses produced by conflict resolution have the property
  // that the first literal is implied after backtracking, so it is always the
  // first watch. The second watch is the literal with the highest decision
  // level. An unassigned literal was re-created after backtracking, so its
  // level is taken to be the current scope level.
  Assert(cls->getNumLiterals() >= 2);
  int maxFalseIdx = -1;
  uint32_t maxLvl = 0;
  int numLits = static_cast<int>(cls->getNumLiterals());
  for (int i = 1; i < numLits; ++i)
  {
    Literal l = cls->getLiteral(i);
    LBool val = getAssignment(l);
    Assert(val == L_FALSE || val == L_UNDEF);
    uint32_t lvl = val == L_FALSE ? getAssignLevel(l) : d_scopeLvl;
    if (maxFalseIdx == -1 || lvl > maxLvl)
    {
      maxFalseIdx = i;
      maxLvl = lvl;
    }
  }
  return maxFalseIdx;
}

int SmtContext::selectWatchLit(const Clause* cls, int startingAt) const
{
  // Pick a watch literal from the positions at or after startingAt:
  //
  //  1. a true literal with the smallest assignment level, which keeps the
  //     clause inactive for as long as possible;
  //  2. otherwise an unassigned literal;
  //  3. otherwise the false literal with the largest assignment level.
  //
  // Rule 3 is what keeps Boolean propagation complete.
  Assert(cls->getNumLiterals() >= 2);
  int minTrueIdx = -1;
  int maxFalseIdx = -1;
  int unknownIdx = -1;
  int n = static_cast<int>(cls->getNumLiterals());
  for (int i = startingAt; i < n; ++i)
  {
    Literal l = cls->getLiteral(i);
    switch (getAssignment(l))
    {
      case L_FALSE:
        if (maxFalseIdx == -1
            || getAssignLevel(l.var())
                   > getAssignLevel(cls->getLiteral(maxFalseIdx).var()))
        {
          maxFalseIdx = i;
        }
        break;
      case L_UNDEF: unknownIdx = i; break;
      case L_TRUE:
        if (minTrueIdx == -1
            || getAssignLevel(l.var())
                   < getAssignLevel(cls->getLiteral(minTrueIdx).var()))
        {
          minTrueIdx = i;
        }
        break;
    }
  }
  if (minTrueIdx != -1)
  {
    return minTrueIdx;
  }
  if (unknownIdx != -1)
  {
    return unknownIdx;
  }
  Assert(maxFalseIdx != -1);
  return maxFalseIdx;
}

void SmtContext::addWatchLiteral(Clause* cls, size_t idx)
{
  Assert(idx == 0 || idx == 1);
  Literal l = cls->getLiteral(idx);
  d_watches[(~l).index()].insertClause(cls);
}

Clause* SmtContext::mkClause(size_t numLits,
                             Literal* lits,
                             Justification* j,
                             ClauseKind k,
                             ClauseDelEh* delEh)
{
  LiteralVector simpLits;
  switch (k)
  {
    case CLS_TH_AXIOM:
    case CLS_AUX:
    {
      if (!simplifyAuxClauseLiterals(numLits, lits, simpLits))
      {
        if (j != nullptr && !j->inRegion())
        {
          j->delEh();
          delete j;
        }
        return nullptr;  // the clause is equivalent to true
      }
      if (!simpLits.empty())
      {
        j = mkJustification(UnitResolutionJustification(
            *this, j, simpLits.size(), simpLits.data()));
      }
      break;
    }
    case CLS_TH_LEMMA:
      if (!simplifyAuxLemmaLiterals(numLits, lits))
      {
        if (j != nullptr && !j->inRegion())
        {
          j->delEh();
          delete j;
        }
        return nullptr;  // the clause is equivalent to true
      }
      // simplifyAuxLemmaLiterals does not delete literals assigned to false,
      // so no unit resolution justification is needed.
      break;
    case CLS_LEARNED: addScores(numLits, lits); break;
  }

  uint32_t activity = 1;
  bool lemma = isLemma(k);
  d_stats.d_numMkLits += numLits;

  switch (numLits)
  {
    case 0:
      if (j != nullptr && !j->inRegion())
      {
        d_justifications.push_back(j);
      }
      setConflict(j == nullptr ? BJustification::mkAxiom() : BJustification(j));
      Assert(inconsistent());
      return nullptr;
    case 1:
    {
      Literal unit = lits[0];
      if (j != nullptr && !j->inRegion())
      {
        d_justifications.push_back(j);
      }
      assign(unit, j);
      incRef(unit);
      return nullptr;
    }
    case 2:
      if (useBinaryClauseOpt(lits[0], lits[1], lemma))
      {
        Literal l1 = lits[0];
        Literal l2 = lits[1];
        incRef(l1);
        incRef(l2);
        d_watches[(~l1).index()].insertLiteral(l2);
        d_watches[(~l2).index()].insertLiteral(l1);
        if (getAssignment(l1) == L_FALSE)
        {
          assign(l2, BJustification(~l1));
        }
        else if (getAssignment(l2) == L_FALSE)
        {
          assign(l1, BJustification(~l2));
        }
        d_stats.d_numMkBinClause++;
        return nullptr;
      }
      CVC5_FALLTHROUGH;
    default:
    {
      d_stats.d_numMkClause++;
      uint32_t iscopeLvl = lemma ? getMaxIscopeLvl(numLits, lits) : 0;
      Assert(d_scopeLvl >= iscopeLvl);
      bool saveAtoms = lemma && iscopeLvl > d_baseLvl;
      bool reinit = saveAtoms;
      Assert(!lemma || j == nullptr || !j->inRegion());
      Clause* cls =
          Clause::mk(numLits, lits, k, j, delEh, saveAtoms, &d_boolVar2Expr);
      if (lemma)
      {
        cls->setActivity(activity);
        if (k == CLS_LEARNED)
        {
          int w2Idx = selectLearnedWatchLit(cls);
          cls->swapLits(1, w2Idx);
        }
        else
        {
          Assert(k == CLS_TH_LEMMA);
          int w1Idx = selectWatchLit(cls, 0);
          cls->swapLits(0, w1Idx);
          int w2Idx = selectWatchLit(cls, 1);
          cls->swapLits(1, w2Idx);
        }
        d_lemmas.push_back(cls);
        addWatchLiteral(cls, 0);
        addWatchLiteral(cls, 1);
        if (getAssignment(cls->getLiteral(0)) == L_FALSE)
        {
          setConflict(BJustification(cls));
          if (k == CLS_TH_LEMMA && d_scopeLvl > d_baseLvl)
          {
            reinit = true;
            iscopeLvl = d_scopeLvl;
          }
        }
        else if (getAssignment(cls->getLiteral(1)) == L_FALSE)
        {
          assign(cls->getLiteral(0), BJustification(cls));
          if (k == CLS_TH_LEMMA && d_scopeLvl > d_baseLvl)
          {
            reinit = true;
            iscopeLvl = d_scopeLvl;
          }
        }
        if (reinit)
        {
          markForReinit(cls, iscopeLvl, saveAtoms);
        }
      }
      else
      {
        d_auxClauses.push_back(cls);
        addWatchLiteral(cls, 0);
        addWatchLiteral(cls, 1);
        if (getAssignment(cls->getLiteral(0)) == L_FALSE)
        {
          setConflict(BJustification(cls));
        }
        else if (getAssignment(cls->getLiteral(1)) == L_FALSE)
        {
          assign(cls->getLiteral(0), BJustification(cls));
        }
      }

      addLitOccs(*cls);
      return cls;
    }
  }
}

void SmtContext::mkClause(Literal l1, Literal l2, Justification* j)
{
  Literal ls[2] = {l1, l2};
  mkClause(2, ls, j);
}

void SmtContext::mkClause(Literal l1, Literal l2, Literal l3, Justification* j)
{
  Literal ls[3] = {l1, l2, l3};
  mkClause(3, ls, j);
}

void SmtContext::mkThClause(TheoryId /*tid*/,
                            size_t numLits,
                            Literal* lits,
                            ClauseKind k)
{
  mkClause(numLits, lits, nullptr, k);
}

void SmtContext::mkThAxiom(TheoryId tid, Literal l1) { mkThAxiom(tid, 1, &l1); }

void SmtContext::mkThAxiom(TheoryId tid, Literal l1, Literal l2)
{
  Literal ls[2] = {l1, l2};
  mkThAxiom(tid, 2, ls);
}

void SmtContext::mkThAxiom(TheoryId tid, Literal l1, Literal l2, Literal l3)
{
  Literal ls[3] = {l1, l2, l3};
  mkThAxiom(tid, 3, ls);
}

void SmtContext::mkGateClause(size_t numLits, Literal* lits)
{
  mkClause(numLits, lits, nullptr);
}

void SmtContext::mkGateClause(Literal l1, Literal l2)
{
  Literal ls[2] = {l1, l2};
  mkGateClause(2, ls);
}

void SmtContext::mkGateClause(Literal l1, Literal l2, Literal l3)
{
  Literal ls[3] = {l1, l2, l3};
  mkGateClause(3, ls);
}

void SmtContext::mkGateClause(Literal l1, Literal l2, Literal l3, Literal l4)
{
  Literal ls[4] = {l1, l2, l3, l4};
  mkGateClause(4, ls);
}

void SmtContext::mkRootClause(size_t numLits, Literal* lits)
{
  mkClause(numLits, lits, nullptr);
}

void SmtContext::mkRootClause(Literal l1, Literal l2)
{
  Literal ls[2] = {l1, l2};
  mkRootClause(2, ls);
}

void SmtContext::mkRootClause(Literal l1, Literal l2, Literal l3)
{
  Literal ls[3] = {l1, l2, l3};
  mkRootClause(3, ls);
}

void SmtContext::addAndRelWatches(TNode n)
{
  if (relevancy())
  {
    RelevancyEh* eh = d_relevancyPropagator->mkAndRelevancyEh(n);
    for (const Node& arg : n)
    {
      // if one child is assigned false, the and-parent must be notified
      addRelWatch(~getLiteral(arg), eh);
    }
  }
}

void SmtContext::addOrRelWatches(TNode n)
{
  if (relevancy())
  {
    RelevancyEh* eh = d_relevancyPropagator->mkOrRelevancyEh(n);
    for (const Node& arg : n)
    {
      // if one child is assigned true, the or-parent must be notified
      addRelWatch(getLiteral(arg), eh);
    }
  }
}

void SmtContext::addImpliesRelWatches(TNode n)
{
  if (relevancy())
  {
    RelevancyEh* eh = d_relevancyPropagator->mkImpliesRelevancyEh(n);
    addRelWatch(~getLiteral(n[0]), eh);
    addRelWatch(getLiteral(n[1]), eh);
  }
}

void SmtContext::addIteRelWatches(TNode n)
{
  if (relevancy())
  {
    RelevancyEh* eh = d_relevancyPropagator->mkIteRelevancyEh(n);
    Literal l = getLiteral(n[0]);
    // when the condition of an ite is assigned, the ite-parent is notified
    addRelWatch(l, eh);
    addRelWatch(~l, eh);
  }
}

void SmtContext::mkNotCnstr(TNode n)
{
  Assert(bInternalized(n));
  BoolVar v = getBoolVar(n);
  Literal l(v, false);
  Literal c = getLiteral(n[0]);
  mkGateClause(~l, ~c);
  mkGateClause(l, c);
}

void SmtContext::mkAndCnstr(TNode n)
{
  Literal l = getLiteral(n);
  LiteralVector buffer;
  buffer.push_back(l);
  for (const Node& arg : n)
  {
    Literal lArg = getLiteral(arg);
    mkGateClause(~l, lArg);
    buffer.push_back(~lArg);
  }
  mkGateClause(buffer.size(), buffer.data());
}

void SmtContext::mkOrCnstr(TNode n)
{
  Literal l = getLiteral(n);
  LiteralVector buffer;
  buffer.push_back(~l);
  for (const Node& arg : n)
  {
    Literal lArg = getLiteral(arg);
    mkGateClause(l, ~lArg);
    buffer.push_back(lArg);
  }
  mkGateClause(buffer.size(), buffer.data());
}

void SmtContext::mkImpliesCnstr(TNode n)
{
  Literal l = getLiteral(n);
  LiteralVector buffer;
  buffer.push_back(~l);
  Literal lArg1 = getLiteral(n[0]);
  mkGateClause(l, lArg1);
  buffer.push_back(~lArg1);
  Literal lArg2 = getLiteral(n[1]);
  mkGateClause(l, ~lArg2);
  buffer.push_back(lArg2);
  mkGateClause(buffer.size(), buffer.data());
}

void SmtContext::mkIffCnstr(TNode n, bool sign)
{
  if (n.getNumChildren() != 2)
  {
    Unreachable() << "z3: formula has not been simplified: " << n;
  }
  Literal l = getLiteral(n);
  Literal l1 = getLiteral(n[0]);
  Literal l2 = getLiteral(n[1]);
  if (sign)
  {
    l.neg();
  }
  mkGateClause(~l, l1, ~l2);
  mkGateClause(~l, ~l1, l2);
  mkGateClause(l, l1, l2);
  mkGateClause(l, ~l1, ~l2);
}

void SmtContext::mkIteCnstr(TNode n)
{
  Literal l = getLiteral(n);
  Literal l1 = getLiteral(n[0]);
  Literal l2 = getLiteral(n[1]);
  Literal l3 = getLiteral(n[2]);
  mkGateClause(~l, ~l1, l2);
  mkGateClause(~l, l1, l3);
  mkGateClause(l, ~l1, ~l2);
  mkGateClause(l, l1, ~l3);
}

namespace {

/** Undoes addThVar. */
class AddThVarTrail : public Trail
{
 public:
  AddThVarTrail(ENode* n, TheoryId thId) : d_enode(n), d_thId(thId) {}

  void undo() override
  {
    TheoryVar v = d_enode->getThVar(d_thId);
    Assert(v != s_nullTheoryVar);
    d_enode->delThVar(d_thId);
    ENode* root = d_enode->getRoot();
    if (root != d_enode && root->getThVar(d_thId) == v)
    {
      root->delThVar(d_thId);
    }
  }

 private:
  ENode* d_enode;
  TheoryId d_thId;
};

/** Undoes replaceThVar. */
class ReplaceThVarTrail : public Trail
{
 public:
  ReplaceThVarTrail(ENode* n, TheoryId thId, TheoryVar oldVar)
      : d_enode(n), d_thId(thId), d_oldThVar(oldVar)
  {
  }

  void undo() override
  {
    Assert(d_enode->getThVar(d_thId) != s_nullTheoryVar);
    d_enode->replaceThVar(d_oldThVar, d_thId);
  }

 private:
  ENode* d_enode;
  TheoryId d_thId;
  TheoryVar d_oldThVar;
};

}  // namespace

void SmtContext::attachThVar(ENode* n, Theory* th, TheoryVar v)
{
  // Attach the theory variable v of th to n. This must be invoked whenever a
  // theory creates a new theory variable. Note that newEqEh and newDiseqEh of
  // th may be invoked before this returns.
  Assert(!th->isAttachedToVar(n));
  TheoryId thId = th->getId();
  TheoryVar oldV = n->getThVar(thId);
  if (oldV == s_nullTheoryVar)
  {
    ENode* r = n->getRoot();
    TheoryVar v2 = r->getThVar(thId);
    n->addThVar(v, thId, getRegion());
    pushTrail(AddThVarTrail(n, thId));
    if (v2 == s_nullTheoryVar)
    {
      if (r != n)
      {
        r->addThVar(v, thId, getRegion());
      }
      pushNewThDiseqs(r, v, th);
    }
    else if (r != n)
    {
      pushNewThEq(thId, v2, v);
    }
  }
  else
  {
    // There is already a variable oldV in the variable list of n, moved there
    // by an earlier addEq.
    Assert(th->getENode(oldV) != n);
    Assert(n->getRoot()->getThVar(thId) != s_nullTheoryVar);
    n->replaceThVar(v, thId);
    pushTrail(ReplaceThVarTrail(n, thId, oldV));
    pushNewThEq(thId, v, oldV);
  }
  Assert(th->isAttachedToVar(n));
}

}  // namespace z3
}  // namespace cvc5::internal

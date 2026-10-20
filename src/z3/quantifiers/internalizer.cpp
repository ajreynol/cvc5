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
#include "z3/quantifiers/quantifier_manager.h"
#include "z3/quantifiers/smt_context.h"
#include "z3/util/util.h"

namespace cvc5::internal {
namespace z3 {

namespace {

bool isTrueNode(TNode n)
{
  return n.getKind() == Kind::CONST_BOOLEAN && n.getConst<bool>();
}

bool isFalseNode(TNode n)
{
  return n.getKind() == Kind::CONST_BOOLEAN && !n.getConst<bool>();
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

/** The threshold above which internalization switches to a topological sort. */
constexpr uint32_t s_deepExprThreshold = 1024;

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
      // avoid overflowing the stack.
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
  d_prop.assertRoot(n);
  d_generation = oldGeneration;
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

void SmtContext::internalize(TNode n, bool gateCtx)
{
  internalizeDeep(n);
  internalizeRec(n, gateCtx);
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
    // application. A quantifier is handled here as well: Z3 relies on its own
    // preprocessing to keep quantifiers out of term positions, which cvc5's
    // does not, so the enode has to be built rather than assumed away.
    if (!gateCtx && isQuantifier(n))
    {
      if (!eInternalized(n))
      {
        mkENode(n,
                true, /* suppress the arguments */
                true, /* merge with true/false, since this is not a gate */
                false /* congruence closure is not enabled */);
        setEnodeFlag(v, false);
        if (getAssignment(v) != L_UNDEF)
        {
          propagateBoolVarENode(v);
        }
      }
      return;
    }
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
  getBdata(v).setEqFlag();
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

void SmtContext::internalizeQuantifier(TNode q, bool gateCtx)
{
  Assert(!bInternalized(q));
  if (q.getKind() != Kind::FORALL)
  {
    // Z3's preprocessing puts every formula in a form where only universal
    // quantifiers survive, so its internalizer has no case for exists.
    mkBoolVar(q);
    return;
  }
  BoolVar v = mkBoolVar(q);
  if (!gateCtx)
  {
    // Z3 asserts gateCtx here: its rewriter guarantees a quantifier only ever
    // occurs as an argument of a gate. cvc5's preprocessor gives no such
    // guarantee -- a Boolean-sorted argument of an uninterpreted function is
    // enough to break it.
    Trace("z3") << "quantifier in a non-gate context: " << q << std::endl;
    mkENode(q,
            true, /* suppress the arguments */
            true, /* merge with true/false, since this is not a gate */
            false /* congruence closure is not enabled */);
    setEnodeFlag(v, false);
  }
  uint32_t generation = generationOf(q);
  BoolVarData& d = getBdata(v);
  d.setQuantifierFlag();
  d_qmanager->add(q, generation);
}

void SmtContext::internalizeFormulaCore(TNode n, bool gateCtx)
{
  // Internalize gates, and the (uninterpreted and equality) predicates.
  Assert(!bInternalized(n));
  Assert(!eInternalized(n));

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
  Assert(n.getKind() != Kind::NOT || !gateCtx);
  d_prop.mkGateConstraints(n);
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
        pushEq(n, d_trueENode);
      }
      break;
    case L_FALSE:
      if (n->getRoot() != d_falseENode->getRoot())
      {
        pushEq(n, d_falseENode);
      }
      break;
  }
}

void SmtContext::setEnodeFlag(BoolVar v, bool isNewVar)
{
  Assert(eInternalized(boolVar2Expr(v)));
  BoolVarData& data = getBdata(v);
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
    updateGeneration(getENode(n));
    return;
  }
  // A term if-then-else does not occur here: the formulas the core
  // internalizes are in the form cvc5's theories take, without them.
  internalizeUninterpreted(n);
  Assert(eInternalized(n));
}

void SmtContext::internalizeUninterpreted(TNode n)
{
  Assert(!eInternalized(n));
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

  // The arithmetic terms keep the congruence policy of Z3's arithmetic
  // plugin, which never enables congruence closure for (+ ...) and (* ...)
  // (theory_arith::enable_cgc_for).
  Kind k = n.getKind();
  bool cgc = k != Kind::ADD && k != Kind::MULT && k != Kind::NONLINEAR_MULT;
  mkENode(n,
          false, /* do not suppress the arguments */
          false, /* a term, so it is not merged with true/false */
          cgc);
}

uint32_t SmtContext::generationOf(TNode n)
{
  auto itg = d_cachedGeneration.find(n);
  if (itg != d_cachedGeneration.end())
  {
    return itg->second;
  }
  // the first internalization records the generation for later ones
  auto ith = d_hostGeneration.emplace(n, d_generation).first;
  return ith->second;
}

ENode* SmtContext::mkENode(TNode n,
                           bool suppressArgs,
                           bool mergeTf,
                           bool cgcEnabled)
{
  Assert(!eInternalized(n));
  size_t id = n.getId();
  uint32_t generation = generationOf(n);
  ENode* e = ENode::mk(getRegion(),
                       d_app2ENode,
                       n,
                       generation,
                       suppressArgs,
                       mergeTf,
                       getScopeLevel(),
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
      assign(Literal(v));
      e->d_cg = e;
      pushEq(e, d_trueENode);
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
        pushNewCongruence(e, r.first);
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

}  // namespace z3
}  // namespace cvc5::internal

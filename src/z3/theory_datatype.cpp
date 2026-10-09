/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The datatypes plugin of the ported Z3 SMT core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), file
 * src/smt/theory_datatype.cpp, and recast in cvc5 style.
 */

#include "z3/theory_datatype.h"

#include <algorithm>

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/node_algorithm.h"
#include "expr/node_manager.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "z3/ast.h"
#include "z3/justification.h"
#include "z3/params.h"
#include "z3/smt_context.h"

namespace cvc5::internal {
namespace z3 {

namespace {

namespace dtutils = theory::datatypes::utils;

/**
 * The justification of an equality the datatype theory propagated. Note the
 * assignment has to be propagated back to the datatype theory, hence the null
 * "from theory".
 */
class DtEqJustification : public ExtTheoryEqPropagationJustification
{
 public:
  DtEqJustification(
      TheoryId fid, SmtContext& ctx, Literal antecedent, ENode* lhs, ENode* rhs)
      : ExtTheoryEqPropagationJustification(
            fid, ctx, 1, &antecedent, 0, nullptr, lhs, rhs)
  {
  }

  TheoryId getFromTheory() const override { return s_nullTheoryId; }
};

/** True if t is a collection sort the ported occurs check does not follow. */
bool isCollection(const TypeNode& t)
{
  return t.isArray() || t.isSequence() || t.isSet() || t.isBag();
}

}  // namespace

TheoryDatatype::FinalCheckGuard::FinalCheckGuard(TheoryDatatype* th) : d_th(th)
{
  Assert(th->d_toUnmark.empty());
  Assert(th->d_toUnmark2.empty());
  th->d_usedEqs.clear();
  th->d_stack.clear();
  th->d_parent.clear();
}

TheoryDatatype::FinalCheckGuard::~FinalCheckGuard() { d_th->clearMark(); }

TheoryDatatype::TheoryDatatype(SmtContext& ctx)
    : Theory(ctx, theory::THEORY_DATATYPES), d_find(*this)
{
}

TheoryDatatype::~TheoryDatatype()
{
  for (VarData* d : d_varData)
  {
    delete d;
  }
  d_varData.clear();
}

void TheoryDatatype::clearMark()
{
  unmarkENodes(d_toUnmark.size(), d_toUnmark.data());
  unmarkENodes2(d_toUnmark2.size(), d_toUnmark2.data());
  d_toUnmark.clear();
  d_toUnmark2.clear();
}

void TheoryDatatype::ocMarkOnStack(ENode* n)
{
  n = n->getRoot();
  if (!n->isMarked())
  {
    n->setMark();
    d_toUnmark.push_back(n);
  }
}

void TheoryDatatype::ocMarkCycleFree(ENode* n)
{
  n = n->getRoot();
  if (!n->isMarked2())
  {
    n->setMark2();
    d_toUnmark2.push_back(n);
  }
}

void TheoryDatatype::ocPushStack(ENode* n)
{
  d_stack.push_back(std::make_pair(EXIT, n));
  d_stack.push_back(std::make_pair(ENTER, n));
}

size_t TheoryDatatype::constructorIdx(TNode n)
{
  Assert(isConstructor(n));
  return dtutils::indexOf(n.getOperator());
}

size_t TheoryDatatype::recognizerIdx(TNode n)
{
  Assert(isRecognizer(n));
  return dtutils::indexOf(n.getOperator());
}

bool TheoryDatatype::isInfinite(const TypeNode& s)
{
  Assert(s.isDatatype());
  return !s.getDType().isFinite(s);
}

bool TheoryDatatype::isRecursiveDatatype(const TypeNode& s)
{
  auto it = d_isRecursive.find(s);
  if (it != d_isRecursive.end())
  {
    return it->second;
  }
  // Z3 records recursiveness when the datatype is declared; here it is found
  // by looking for s in the component sorts reachable from s.
  bool recursive = false;
  std::unordered_set<TypeNode> visited;
  std::vector<TypeNode> visit{s};
  while (!visit.empty() && !recursive)
  {
    TypeNode cur = visit.back();
    visit.pop_back();
    if (!visited.insert(cur).second)
    {
      continue;
    }
    if (!cur.isDatatype())
    {
      // Follow the component sorts of a collection, since a datatype may
      // recur through one.
      for (size_t i = 0, nc = cur.getNumChildren(); i < nc; ++i)
      {
        visit.push_back(cur[i]);
      }
      continue;
    }
    const DType& dt = cur.getDType();
    for (size_t i = 0, nc = dt.getNumConstructors(); i < nc; ++i)
    {
      for (size_t j = 0, na = dt[i].getNumArgs(); j < na; ++j)
      {
        TypeNode at = dt[i][j].getRangeType();
        if (at == s)
        {
          recursive = true;
          break;
        }
        visit.push_back(at);
      }
      if (recursive)
      {
        break;
      }
    }
  }
  d_isRecursive[s] = recursive;
  return recursive;
}

size_t TheoryDatatype::nonRecConstructorIdx(const TypeNode& s)
{
  Assert(s.isDatatype());
  const DType& dt = s.getDType();
  // Prefer a constructor none of whose arguments can reach s, which is what
  // Z3's get_non_rec_constructor returns.
  for (size_t i = 0, nc = dt.getNumConstructors(); i < nc; ++i)
  {
    bool rec = false;
    for (size_t j = 0, na = dt[i].getNumArgs(); j < na; ++j)
    {
      TypeNode at = dt[i][j].getRangeType();
      if (at == s || (at.isDatatype() && isRecursiveDatatype(at)))
      {
        rec = true;
        break;
      }
    }
    if (!rec)
    {
      return i;
    }
  }
  return 0;
}

void TheoryDatatype::checkUnsupportedNesting(const TypeNode& s)
{
  if (!s.isDatatype() || !d_nestingChecked.insert(s).second)
  {
    return;
  }
  const DType& dt = s.getDType();
  for (size_t i = 0, nc = dt.getNumConstructors(); i < nc; ++i)
  {
    for (size_t j = 0, na = dt[i].getNumArgs(); j < na; ++j)
    {
      TypeNode at = dt[i][j].getRangeType();
      if (!isCollection(at))
      {
        continue;
      }
      for (size_t k = 0, nk = at.getNumChildren(); k < nk; ++k)
      {
        if (at[k].isDatatype())
        {
          // The occurs check would have to follow the collection to rule out
          // a cycle; since it does not, no model can be trusted.
          Trace("z3") << "unsupported: datatype nested under a collection in "
                      << s << std::endl;
          getContext().markModelUnsound(theory::THEORY_DATATYPES);
          return;
        }
      }
    }
  }
}

void TheoryDatatype::assertEqAxiom(ENode* lhs, TNode rhs, Literal antecedent)
{
  SmtContext& ctx = getContext();
  ctx.internalize(rhs, false);
  if (antecedent == s_nullLiteral)
  {
    ctx.assignEq(lhs, ctx.getENode(rhs), EqJustification::mkAxiom());
  }
  else if (ctx.getAssignment(antecedent) != L_TRUE)
  {
    Literal l = mkEq(lhs->getExpr(), rhs, true);
    ctx.markAsRelevant(l);
    ctx.markAsRelevant(antecedent);
    Literal lits[2] = {l, ~antecedent};
    ctx.mkThAxiom(getId(), 2, lits);
  }
  else
  {
    ENode* rhsE = ctx.getENode(rhs);
    Justification* js = ctx.mkJustification(
        DtEqJustification(getId(), ctx, antecedent, lhs, rhsE));
    ctx.assignEq(lhs, rhsE, EqJustification(js));
  }
}

void TheoryDatatype::assertIsConstructorAxiom(ENode* n,
                                              size_t cidx,
                                              Literal antecedent)
{
  d_dtStats.d_assertCnstr++;
  getContext().getStats().d_numDtConstructorAx++;
  TNode e = n->getExpr();
  TypeNode tn = e.getType();
  Assert(tn.isDatatype());
  const DType& dt = tn.getDType();
  std::vector<Node> args;
  for (size_t i = 0, na = dt[cidx].getNumArgs(); i < na; ++i)
  {
    args.push_back(dtutils::applySelector(dt[cidx], i, false, e));
  }
  Node mk = dtutils::mkApplyCons(tn, dt, cidx, args);
  assertEqAxiom(n, mk, antecedent);
}

void TheoryDatatype::assertAccessorAxioms(ENode* n)
{
  d_dtStats.d_assertAccessor++;
  getContext().getStats().d_numDtAccessorAx++;
  Assert(isConstructor(n));
  TNode e = n->getExpr();
  TypeNode tn = e.getType();
  const DType& dt = tn.getDType();
  size_t cidx = constructorIdx(e);
  Assert(n->getNumArgs() == dt[cidx].getNumArgs());
  for (size_t i = 0, na = n->getNumArgs(); i < na; ++i)
  {
    Node accApp = dtutils::applySelector(dt[cidx], i, false, e);
    assertEqAxiom(n->getArg(i), accApp, s_nullLiteral);
  }
}

void TheoryDatatype::signRecognizerConflict(ENode* c, ENode* r)
{
  SmtContext& ctx = getContext();
  Assert(isConstructor(c));
  Assert(isRecognizer(r));
  Assert(recognizerIdx(r->getExpr()) == constructorIdx(c->getExpr()));
  Assert(c->getRoot() == r->getArg(0)->getRoot());
  Literal l(ctx.enode2BoolVar(r));
  Assert(ctx.getAssignment(l) == L_FALSE);
  l = ~l;
  ENodePair p(c, r->getArg(0));
  clearMark();
  ctx.setConflict(ctx.mkJustification(
      ExtTheoryConflictJustification(getId(), ctx, 1, &l, 1, &p)));
}

void TheoryDatatype::assertUpdateFieldAxioms(ENode* n)
{
  d_dtStats.d_assertUpdateField++;
  getContext().getStats().d_numDtUpdateFieldAx++;
  SmtContext& ctx = getContext();
  Assert(isUpdateField(n));
  TNode own = n->getExpr();
  TNode arg1 = own[0];
  Node upd = own.getOperator();
  size_t cidx = dtutils::cindexOf(upd);
  size_t fidx = dtutils::indexOf(upd);
  TypeNode tn = arg1.getType();
  const DType& dt = tn.getDType();
  Node recApp = dtutils::mkTester(arg1, static_cast<int>(cidx), dt);
  ctx.internalize(recApp, false);
  Literal isCon(ctx.getBoolVar(recApp));
  for (size_t i = 0, na = dt[cidx].getNumArgs(); i < na; ++i)
  {
    ENode* arg;
    if (i == fidx)
    {
      arg = n->getArg(1);
    }
    else
    {
      Node accApp = dtutils::applySelector(dt[cidx], i, false, arg1);
      ctx.internalize(accApp, false);
      arg = ctx.getENode(accApp);
    }
    Node accOwn = dtutils::applySelector(dt[cidx], i, false, own);
    assertEqAxiom(arg, accOwn, isCon);
  }
  // the update is the identity if n was not created by a matching constructor
  assertEqAxiom(n, arg1, ~isCon);

  Node nIsCon = dtutils::mkTester(own, static_cast<int>(cidx), dt);
  ctx.internalize(nIsCon, false);
  Literal lits[2] = {~isCon, Literal(ctx.getBoolVar(nIsCon))};
  ctx.markAsRelevant(lits[0]);
  ctx.markAsRelevant(lits[1]);
  ctx.mkThAxiom(getId(), 2, lits);
}

TheoryVar TheoryDatatype::mkVar(ENode* n)
{
  SmtContext& ctx = getContext();
  TheoryVar r = Theory::mkVar(n);
  TheoryVar ufr = static_cast<TheoryVar>(d_find.mkVar());
  Assert(r == ufr);
  (void)ufr;
  Assert(r == static_cast<TheoryVar>(d_varData.size()));
  d_varData.push_back(new VarData());
  VarData* d = d_varData[r];
  ctx.attachThVar(n, this, r);

  TypeNode tn = n->getExpr().getType();
  if (tn.isDatatype())
  {
    checkUnsupportedNesting(tn);
  }

  if (isConstructor(n))
  {
    d->d_constructor = n;
    assertAccessorAxioms(n);
  }
  else if (isUpdateField(n))
  {
    assertUpdateFieldAxioms(n);
  }
  else if (tn.isDatatype())
  {
    if (tn.getDType().getNumConstructors() == 1)
    {
      assertIsConstructorAxiom(n, 0, s_nullLiteral);
    }
    else
    {
      uint32_t lazy = getParams().d_dtLazySplits;
      if (lazy == 0 || (lazy == 1 && !isInfinite(tn)))
      {
        mkSplit(r);
      }
    }
  }
  return r;
}

bool TheoryDatatype::internalizeAtom(TNode atom, bool /*gateCtx*/)
{
  return internalizeTerm(atom);
}

bool TheoryDatatype::internalizeTerm(TNode term)
{
  // Z3 routes a term to a theory by the family of its declaration, while cvc5
  // routes it by the theory of its sort, so a free constant or an
  // uninterpreted application of datatype sort arrives here as well. Such a
  // term is internalized by the core as uninterpreted; the theory variable is
  // then created by applySortCnstr, which is what Z3 does too.
  if (!isConstructor(term) && !isRecognizer(term) && !isAccessor(term)
      && !isUpdateField(term))
  {
    return false;
  }
  forcePush();
  SmtContext& ctx = getContext();
  size_t numArgs = term.getNumChildren();
  bool isBool = term.getType().isBoolean();
  for (size_t i = 0; i < numArgs; ++i)
  {
    ctx.internalize(term[i], isBool && expr::hasClosure(Node(term)));
  }
  // internalizing the arguments may have internalized term
  if (ctx.eInternalized(term))
  {
    return true;
  }
  ENode* e = ctx.mkENode(term, false, isBool, true);
  if (isBool)
  {
    BoolVar bv = ctx.mkBoolVar(term);
    ctx.setVarTheory(bv, getId());
    ctx.setEnodeFlag(bv, true);
  }
  if (isConstructor(term) || isUpdateField(term))
  {
    Assert(!isAttachedToVar(e));
    // A theory variable has to be created for every argument of datatype
    // sort. applySortCnstr does not create one when the sort has infinitely
    // many elements, which would break model construction: given
    //   x1 = cons(v1, x2)
    // over lists of integers, the interpretation of x1 needs the one of x2,
    // so x2 cannot be a fresh value (those can only be made after every
    // relevant expression of the sort has an interpretation).
    for (size_t i = 0; i < numArgs; ++i)
    {
      ENode* arg = e->getArg(i);
      if (!arg->getExpr().getType().isDatatype())
      {
        continue;
      }
      if (isAttachedToVar(arg))
      {
        continue;
      }
      mkVar(arg);
    }
    mkVar(e);
  }
  else
  {
    Assert(isAccessor(term) || isRecognizer(term));
    Assert(term.getNumChildren() == 1);
    ENode* arg = e->getArg(0);
    if (!isAttachedToVar(arg))
    {
      mkVar(arg);
    }
  }
  if (isRecognizer(term))
  {
    ENode* arg = e->getArg(0);
    TheoryVar v = arg->getThVar(getId());
    Assert(v != s_nullTheoryVar);
    // With relevancy propagation the recognizer is only added once it is
    // marked as relevant.
    if (!ctx.relevancy())
    {
      addRecognizer(v, e);
    }
  }
  return true;
}

void TheoryDatatype::applySortCnstr(ENode* n, const TypeNode& s)
{
  forcePush();
  // A theory variable is not needed when s is infinite, but it is better to
  // make one anyway once the problem has quantifiers. For example, given
  //   (forall ((l list) (a Int)) (= (len (cons a l)) (+ (len l) 1)))
  //   (assert (> (len a) 1))
  // omitting the variable for 'a' would produce a wrong model.
  if (!isAttachedToVar(n)
      && (getContext().hasQuantifiers() || (s.isDatatype() && !isInfinite(s))))
  {
    mkVar(n);
  }
}

void TheoryDatatype::newEqEh(TheoryVar v1, TheoryVar v2)
{
  forcePush();
  d_find.merge(v1, v2);
}

void TheoryDatatype::newDiseqEh(TheoryVar /*v1*/, TheoryVar /*v2*/)
{
  Unreachable();
}

void TheoryDatatype::assignEh(BoolVar v, bool isTrue)
{
  forcePush();
  SmtContext& ctx = getContext();
  ENode* n = ctx.boolVar2ENode(v);
  if (!isRecognizer(n))
  {
    return;
  }
  Assert(n->getNumArgs() == 1);
  ENode* arg = n->getArg(0);
  TheoryVar tv = arg->getThVar(getId());
  Assert(tv != s_nullTheoryVar);
  tv = static_cast<TheoryVar>(d_find.find(tv));
  VarData* d = d_varData[tv];
  size_t cidx = recognizerIdx(n->getExpr());
  if (isTrue)
  {
    if (d->d_constructor != nullptr
        && constructorIdx(d->d_constructor->getExpr()) == cidx)
    {
      return;  // nothing to do
    }
    assertIsConstructorAxiom(arg, cidx, Literal(v));
  }
  else
  {
    if (d->d_constructor != nullptr)
    {
      if (constructorIdx(d->d_constructor->getExpr()) == cidx)
      {
        signRecognizerConflict(d->d_constructor, n);
      }
    }
    else
    {
      propagateRecognizer(tv, n);
    }
  }
}

void TheoryDatatype::relevantEh(TNode n)
{
  forcePush();
  Assert(getContext().relevancy());
  if (!isRecognizer(n))
  {
    return;
  }
  SmtContext& ctx = getContext();
  Assert(ctx.eInternalized(n));
  ENode* e = ctx.getENode(n);
  TheoryVar v = e->getArg(0)->getThVar(getId());
  Assert(v != s_nullTheoryVar);
  addRecognizer(v, e);
}

void TheoryDatatype::pushScopeEh()
{
  if (lazyPush())
  {
    return;
  }
  Theory::pushScopeEh();
  d_trailStack.pushScope();
}

void TheoryDatatype::popScopeEh(size_t numScopes)
{
  if (lazyPop(numScopes))
  {
    return;
  }
  d_trailStack.popScope(numScopes);
  size_t numOldVars = getOldNumVars(numScopes);
  for (size_t i = numOldVars; i < d_varData.size(); ++i)
  {
    delete d_varData[i];
  }
  d_varData.resize(numOldVars);
  Theory::popScopeEh(numScopes);
  Assert(d_find.getNumVars() == d_varData.size());
  Assert(d_find.getNumVars() == getNumVars());
}

FinalCheckStatus TheoryDatatype::finalCheckEh(size_t /*level*/)
{
  forcePush();
  size_t numVars = getNumVars();
  FinalCheckStatus r = FC_DONE;
  FinalCheckGuard guard(this);
  for (size_t v = 0; v < numVars; ++v)
  {
    if (static_cast<uint32_t>(v) != d_find.find(static_cast<uint32_t>(v)))
    {
      continue;
    }
    ENode* node = getENode(static_cast<TheoryVar>(v));
    TypeNode s = node->getExpr().getType();
    if (!s.isDatatype())
    {
      continue;
    }
    if (isRecursiveDatatype(s) && !ocCycleFree(node) && occursCheck(node))
    {
      // a conflict was found
      return FC_CONTINUE;
    }
    if (getParams().d_dtLazySplits > 0)
    {
      VarData* d = d_varData[v];
      if (d->d_constructor == nullptr)
      {
        clearMark();
        mkSplit(static_cast<TheoryVar>(v));
        r = FC_CONTINUE;
      }
    }
  }
  return r;
}

ENode* TheoryDatatype::ocGetCstor(ENode* app)
{
  TheoryVar v = app->getRoot()->getThVar(getId());
  if (v == s_nullTheoryVar)
  {
    return nullptr;
  }
  v = static_cast<TheoryVar>(d_find.find(v));
  return d_varData[v]->d_constructor;
}

void TheoryDatatype::explainIsChild(ENode* parent, ENode* child)
{
  ENode* parentc = ocGetCstor(parent);
  Assert(parentc != nullptr);
  if (parent != parentc)
  {
    d_usedEqs.push_back(ENodePair(parent, parentc));
  }
  // Collect the equalities on every child that may have been used.
  bool found = false;
  for (ENode* arg : parentc->getConstArgs())
  {
    if (arg->getRoot() == child->getRoot())
    {
      if (arg != child)
      {
        d_usedEqs.push_back(ENodePair(arg, child));
      }
      found = true;
    }
  }
  Assert(found);
  (void)found;
}

void TheoryDatatype::occursCheckExplain(ENode* app, ENode* root)
{
  // First explain root = v given that app = cstor(..., v, ...).
  explainIsChild(app, root);
  // Then explain app = cstor(.., v, ..) where v = root, and recurse with the
  // parent of app.
  while (app->getRoot() != root->getRoot())
  {
    auto it = d_parent.find(app->getRoot());
    Assert(it != d_parent.end());
    ENode* parentApp = it->second;
    explainIsChild(parentApp, app);
    Assert(isConstructor(parentApp));
    app = parentApp;
  }
  Assert(app->getRoot() == root->getRoot());
  if (app != root)
  {
    d_usedEqs.push_back(ENodePair(app, root));
  }
}

bool TheoryDatatype::occursCheckEnter(ENode* app)
{
  app = app->getRoot();
  TheoryVar v = app->getThVar(getId());
  if (v == s_nullTheoryVar)
  {
    return false;
  }
  v = static_cast<TheoryVar>(d_find.find(v));
  VarData* d = d_varData[v];
  if (d->d_constructor == nullptr)
  {
    return false;
  }
  ENode* parent = d->d_constructor;
  ocMarkOnStack(parent);
  for (ENode* arg : parent->getConstArgs())
  {
    if (ocCycleFree(arg))
    {
      continue;
    }
    if (ocOnStack(arg))
    {
      // arg was explored before app and is still on the stack: a cycle
      occursCheckExplain(parent, arg);
      return true;
    }
    if (arg->getExpr().getType().isDatatype())
    {
      d_parent[arg->getRoot()] = parent;
      ocPushStack(arg);
    }
  }
  return false;
}

bool TheoryDatatype::occursCheck(ENode* n)
{
  d_dtStats.d_occursCheck++;
  getContext().getStats().d_numDtOccursCheck++;
  bool res = false;
  ocPushStack(n);
  // A DFS from n: look at the top element and explore it.
  while (!res && !d_stack.empty())
  {
    std::pair<StackOp, ENode*> top = d_stack.back();
    d_stack.pop_back();
    if (ocCycleFree(top.second))
    {
      continue;
    }
    switch (top.first)
    {
      case ENTER: res = occursCheckEnter(top.second); break;
      case EXIT: ocMarkCycleFree(top.second); break;
    }
  }
  if (res)
  {
    SmtContext& ctx = getContext();
    clearMark();
    ctx.setConflict(ctx.mkJustification(ExtTheoryConflictJustification(
        getId(), ctx, 0, nullptr, d_usedEqs.size(), d_usedEqs.data())));
  }
  return res;
}

void TheoryDatatype::resetEh()
{
  d_trailStack.reset();
  for (VarData* d : d_varData)
  {
    delete d;
  }
  d_varData.clear();
  Theory::resetEh();
}

void TheoryDatatype::mergeEh(TheoryVar v1, TheoryVar v2, TheoryVar, TheoryVar)
{
  // v1 is the new root
  SmtContext& ctx = getContext();
  Assert(v1 == static_cast<TheoryVar>(d_find.find(v1)));
  VarData* d1 = d_varData[v1];
  VarData* d2 = d_varData[v2];
  if (d2->d_constructor != nullptr)
  {
    if (d1->d_constructor != nullptr
        && constructorIdx(d1->d_constructor->getExpr())
               != constructorIdx(d2->d_constructor->getExpr()))
    {
      ENodePair p(d1->d_constructor, d2->d_constructor);
      Assert(d1->d_constructor->getRoot() == d2->d_constructor->getRoot());
      ctx.setConflict(ctx.mkJustification(
          ExtTheoryConflictJustification(getId(), ctx, 0, nullptr, 1, &p)));
    }
    if (d1->d_constructor == nullptr)
    {
      d_trailStack.push(SetPtrTrail<ENode>(d1->d_constructor));
      // Check whether a recognizer in d1 conflicts with d2's constructor.
      if (!d1->d_recognizers.empty())
      {
        size_t cIdx = constructorIdx(d2->d_constructor->getExpr());
        ENode* recognizer = d1->d_recognizers[cIdx];
        if (recognizer != nullptr && ctx.getAssignment(recognizer) == L_FALSE)
        {
          signRecognizerConflict(d2->d_constructor, recognizer);
          return;
        }
      }
      d1->d_constructor = d2->d_constructor;
    }
  }
  for (ENode* e : d2->d_recognizers)
  {
    if (e != nullptr)
    {
      addRecognizer(v1, e);
    }
  }
}

void TheoryDatatype::addRecognizer(TheoryVar v, ENode* recognizer)
{
  SmtContext& ctx = getContext();
  Assert(isRecognizer(recognizer));
  v = static_cast<TheoryVar>(d_find.find(v));
  VarData* d = d_varData[v];
  TypeNode s = recognizer->getExpr()[0].getType();
  if (d->d_recognizers.empty())
  {
    Assert(s.isDatatype());
    d->d_recognizers.resize(s.getDType().getNumConstructors(), nullptr);
  }
  Assert(d->d_recognizers.size() == s.getDType().getNumConstructors());
  size_t cIdx = recognizerIdx(recognizer->getExpr());
  if (d->d_recognizers[cIdx] != nullptr)
  {
    return;
  }
  LBool val = ctx.getAssignment(recognizer);
  if (val == L_TRUE)
  {
    // Nothing to do: if the assignment of the recognizer was already
    // processed then d->d_constructor is set, and otherwise it will be set
    // when assignEh runs.
    return;
  }
  if (val == L_FALSE && d->d_constructor != nullptr)
  {
    if (constructorIdx(d->d_constructor->getExpr()) == cIdx)
    {
      signRecognizerConflict(d->d_constructor, recognizer);
    }
    return;
  }
  Assert(val == L_UNDEF || (val == L_FALSE && d->d_constructor == nullptr));
  d->d_recognizers[cIdx] = recognizer;
  d_trailStack.push(
      SetVectorIdxTrail<std::vector<ENode*>>(d->d_recognizers, cIdx));
  if (val == L_FALSE)
  {
    propagateRecognizer(v, recognizer);
  }
}

void TheoryDatatype::propagateRecognizer(TheoryVar v, ENode* recognizer)
{
  SmtContext& ctx = getContext();
  Assert(isRecognizer(recognizer));
  Assert(static_cast<TheoryVar>(d_find.find(v)) == v);
  Assert(ctx.getAssignment(recognizer) == L_FALSE);
  size_t numUnassigned = 0;
  size_t unassignedIdx = 0;
  ENode* n = getENode(v);
  TypeNode dt = n->getExpr().getType();
  VarData* d = d_varData[v];
  if (d->d_recognizers.empty())
  {
    TheoryVar w = recognizer->getArg(0)->getThVar(getId());
    Assert(w != s_nullTheoryVar);
    addRecognizer(w, recognizer);
  }
  Assert(!d->d_recognizers.empty());
  LiteralVector lits;
  ENodePairVector eqs;
  for (size_t idx = 0, nr = d->d_recognizers.size(); idx < nr; ++idx)
  {
    ENode* r = d->d_recognizers[idx];
    if (r != nullptr && ctx.getAssignment(r) == L_TRUE)
    {
      return;  // nothing to propagate
    }
    if (r != nullptr && ctx.getAssignment(r) == L_FALSE)
    {
      Assert(r->getNumArgs() == 1);
      lits.push_back(Literal(ctx.enode2BoolVar(r), true));
      if (n != r->getArg(0))
      {
        // The argument of the recognizer is not necessarily n: the two may
        // only be in the same class, in which case the equality is part of
        // the conflict or the propagation.
        Assert(n->getRoot() == r->getArg(0)->getRoot());
        eqs.push_back(ENodePair(n, r->getArg(0)));
      }
      continue;
    }
    if (numUnassigned == 0)
    {
      unassignedIdx = idx;
    }
    numUnassigned++;
  }
  if (numUnassigned == 0)
  {
    Assert(!lits.empty());
    ctx.setConflict(ctx.mkJustification(ExtTheoryConflictJustification(
        getId(), ctx, lits.size(), lits.data(), eqs.size(), eqs.data())));
  }
  else if (numUnassigned == 1)
  {
    // propagate the remaining recognizer
    Assert(!lits.empty());
    ENode* r = d->d_recognizers[unassignedIdx];
    Literal consequent;
    if (r == nullptr)
    {
      Node recApp = dtutils::mkTester(
          n->getExpr(), static_cast<int>(unassignedIdx), dt.getDType());
      consequent = mkLiteral(recApp);
    }
    else
    {
      consequent = Literal(ctx.enode2BoolVar(r));
    }
    ctx.markAsRelevant(consequent);
    ctx.assign(
        consequent,
        ctx.mkJustification(ExtTheoryPropagationJustification(getId(),
                                                              ctx,
                                                              lits.size(),
                                                              lits.data(),
                                                              eqs.size(),
                                                              eqs.data(),
                                                              consequent)));
  }
  else
  {
    // There are more than two unassigned recognizers; create a case split if
    // eager splits are enabled.
    uint32_t lazy = getParams().d_dtLazySplits;
    if (lazy == 0 || (!isInfinite(dt) && lazy == 1))
    {
      mkSplit(v);
    }
  }
}

void TheoryDatatype::mkSplit(TheoryVar v)
{
  SmtContext& ctx = getContext();
  v = static_cast<TheoryVar>(d_find.find(v));
  ENode* n = getENode(v);
  TypeNode s = n->getExpr().getType();
  const DType& dt = s.getDType();
  size_t nonRecIdx = nonRecConstructorIdx(s);
  VarData* d = d_varData[v];
  Assert(d->d_constructor == nullptr);
  d_dtStats.d_splits++;
  getContext().getStats().d_numDtSplits++;

  // the index of the constructor to split on, or dt.getNumConstructors() if
  // there is nothing left to do
  size_t rIdx = dt.getNumConstructors();
  if (d->d_recognizers.empty())
  {
    rIdx = nonRecIdx;
  }
  else
  {
    ENode* recognizer = d->d_recognizers[nonRecIdx];
    if (recognizer == nullptr)
    {
      rIdx = nonRecIdx;
    }
    else if (!ctx.isRelevant(recognizer))
    {
      ctx.markAsRelevant(recognizer);
      return;
    }
    else if (ctx.getAssignment(recognizer) != L_FALSE)
    {
      // if it is true then there is nothing to do, and otherwise the
      // recognizer has yet to be assigned
      return;
    }
    else
    {
      // Look for a slot of d->d_recognizers that is null, or that is
      // unassigned and not marked as relevant.
      for (size_t idx = 0, nr = d->d_recognizers.size(); idx < nr; ++idx)
      {
        ENode* curr = d->d_recognizers[idx];
        if (curr == nullptr)
        {
          rIdx = idx;
          break;
        }
        if (!ctx.isRelevant(curr))
        {
          ctx.markAsRelevant(curr);
          return;
        }
        if (ctx.getAssignment(curr) != L_FALSE)
        {
          return;
        }
      }
      if (rIdx == dt.getNumConstructors())
      {
        // every recognizer is asserted to false, so a conflict will be found
        return;
      }
    }
  }
  Assert(rIdx < dt.getNumConstructors());
  Node rApp = dtutils::mkTester(n->getExpr(), static_cast<int>(rIdx), dt);
  ctx.internalize(rApp, false);
  BoolVar bv = ctx.getBoolVar(rApp);
  ctx.setTrueFirstFlag(bv);
  ctx.markAsRelevant(bv);
}

bool TheoryDatatype::getValue(ENode* n, Node& r)
{
  TheoryVar v = n->getThVar(getId());
  if (v == s_nullTheoryVar)
  {
    return false;
  }
  v = static_cast<TheoryVar>(d_find.find(v));
  if (static_cast<size_t>(v) >= d_varData.size() || d_varData[v] == nullptr)
  {
    return false;
  }
  ENode* c = d_varData[v]->d_constructor;
  if (c == nullptr)
  {
    return false;
  }
  r = c->getExpr();
  return true;
}

void TheoryDatatype::printVar(std::ostream& out, TheoryVar v) const
{
  VarData* d = d_varData[v];
  out << "v" << v << " #" << getENode(v)->getOwnerId() << " -> v"
      << d_find.find(v) << " ";
  if (d->d_constructor != nullptr)
  {
    out << d->d_constructor->getExpr();
  }
  else
  {
    out << "(null)";
  }
  out << "\n";
}

void TheoryDatatype::print(std::ostream& out) const
{
  size_t numVars = getNumVars();
  if (numVars == 0)
  {
    return;
  }
  out << "Theory datatype:\n";
  for (size_t v = 0; v < numVars; ++v)
  {
    printVar(out, static_cast<TheoryVar>(v));
  }
}

Theory* mkTheoryDatatype(SmtContext& ctx) { return new TheoryDatatype(ctx); }

}  // namespace z3
}  // namespace cvc5::internal

/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Caleb Donovick, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The rewrite preprocessing pass.
 *
 * Calls the rewriter on every assertion.
 */

#include "preprocessing/passes/dt_elim.h"

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/env.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/quantifiers/quant_split.h"
#include "theory/rewriter.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace cvc5::internal::theory;

bool isUnaryPolicy(DtElimPolicy policy)
{
  return policy == DtElimPolicy::UNIT || policy == DtElimPolicy::UNARY
         || policy == DtElimPolicy::UNIT_ENUM;
}

bool isBinaryTestPolicy(DtElimPolicy policy)
{
  return policy == DtElimPolicy::BINARY_ENUM || policy == DtElimPolicy::BINARY;
}

bool isAbstractPolicy(DtElimPolicy policy)
{
  return policy == DtElimPolicy::ABSTRACT_ENUM
         || policy == DtElimPolicy::ABSTRACT;
}

bool isEnumPolicy(DtElimPolicy policy)
{
  return policy == DtElimPolicy::UNIT_ENUM
         || policy == DtElimPolicy::BINARY_ENUM
         || policy == DtElimPolicy::ABSTRACT_ENUM;
}
const char* toString(DtElimPolicy policy)
{
  switch (policy)
  {
    case DtElimPolicy::NONE: return "NONE";
    case DtElimPolicy::UNIT: return "UNIT";
    case DtElimPolicy::UNIT_ENUM: return "UNIT_ENUM";
    case DtElimPolicy::UNARY: return "UNARY";
    case DtElimPolicy::BINARY_ENUM: return "BINARY_ENUM";
    case DtElimPolicy::BINARY: return "BINARY";
    case DtElimPolicy::ABSTRACT_ENUM: return "ABSTRACT_ENUM";
    case DtElimPolicy::ABSTRACT: return "ABSTRACT";
    default: return "?";
  }
}
std::ostream& operator<<(std::ostream& out, DtElimPolicy policy)
{
  out << toString(policy);
  return out;
}

DtElimConverter::DtElimConverter(Env& env, const std::vector<Node>& assertions)
    : EnvObj(env), NodeConverter(nodeManager())
{
  computePolicies(assertions);
  d_dtElimSc = nodeManager()->mkSortConstructor("@dt-elim-sort", 1);
}
DtElimConverter::~DtElimConverter() {}
/**
 * Compute the policies for each datatype
 */
void DtElimConverter::computePolicies(const std::vector<Node>& assertions)
{
  std::unordered_set<TypeNode> allDt;
  std::unordered_set<TypeNode> preserveTypes;
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit(assertions.begin(), assertions.end());
  TNode cur;
  do
  {
    cur = visit.back();
    Trace("dt-elim-debug2") << "- visit " << cur << std::endl;
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      TypeNode tn = cur.getType();
      if (tn.isDatatype())
      {
        allDt.insert(tn);
      }
      if (cur.isVar())
      {
        // all its component types must be preserved????
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());

  std::vector<TypeNode> noElimDt;
  for (const TypeNode& tn : allDt)
  {
    Trace("dt-elim-policy") << "Compute policy for " << tn << std::endl;
    if (preserveTypes.find(tn) != preserveTypes.end())
    {
      noElimDt.push_back(tn);
      continue;
    }
    Assert(tn.isDatatype());
    const DType& dt = tn.getDType();
    if (dt.isParametric())
    {
      // parameteric datatypes can't be eliminated currently?
      continue;
    }
    bool isEnum = true;
    size_t ncons = dt.getNumConstructors();
    for (size_t i = 0; i < ncons; i++)
    {
      if (dt[i].getNumArgs() > 0)
      {
        isEnum = false;
        break;
      }
    }
    // FIXME
    if (ncons >= 2)
    {
      noElimDt.push_back(tn);
      continue;
    }
    /*
    if (!isEnum)
    {
      continue;
    }
    */
    DtElimPolicy policy = DtElimPolicy::NONE;
    if (isEnum)
    {
      policy = (ncons == 1 ? DtElimPolicy::UNIT_ENUM
                           : (ncons == 2 ? DtElimPolicy::BINARY_ENUM
                                         : DtElimPolicy::ABSTRACT_ENUM));
    }
    else
    {
      // check if recursive
      if (!dt.isRecursive())
      {
        policy = (ncons == 1 ? DtElimPolicy::UNARY
                             : (ncons == 2 ? DtElimPolicy::BINARY
                                           : DtElimPolicy::ABSTRACT));
      }
    }
    Trace("dt-elim-policy")
        << "Policy for " << tn << " is " << policy << std::endl;
    if (policy != DtElimPolicy::NONE)
    {
      d_dtep[tn] = policy;
    }
    else
    {
      noElimDt.push_back(tn);
    }
  }
  // go back and erase subfield types
  size_t i = 0;
  std::unordered_set<TypeNode> noElimProcessed;
  while (i < noElimDt.size())
  {
    TypeNode tn = noElimDt[i];
    i++;
    if (!noElimProcessed.insert(tn).second)
    {
      continue;
    }
    Assert(tn.isDatatype());
    const DType& dt = tn.getDType();
    std::unordered_set<TypeNode> stns = dt.getSubfieldTypes();
    for (const TypeNode& stn : stns)
    {
      if (d_dtep.find(stn) != d_dtep.end())
      {
        Trace("dt-elim-policy") << "...due to not eliminating " << tn
                                << ", don't eliminate " << stn << std::endl;
        d_dtep.erase(stn);
        noElimDt.push_back(stn);
      }
    }
  }
}

Node DtElimConverter::preConvert(Node n)
{
  Kind k = n.getKind();
  if (k == Kind::FORALL)
  {
    // TODO: see if any variables need to be split??
    for (size_t i = 0, nvars = n[0].getNumChildren(); i < nvars; i++)
    {
      Node v = n[0][i];
      TypeNode tn = v.getType();
      std::map<TypeNode, DtElimPolicy>::iterator itd = d_dtep.find(tn);
      if (itd == d_dtep.end())
      {
        continue;
      }
      Node ns = quantifiers::QuantDSplit::split(nodeManager(), n, i);
      return convert(ns);
    }
  }
  return n;
}

Node DtElimConverter::postConvert(Node n)
{
  Kind k = n.getKind();
  Trace("dt-elim-debug") << "convert: " << n << " " << k << std::endl;
  if (k == Kind::APPLY_TESTER)
  {
    Node t = n[0];
    TypeNode tn = t.getType();
    if (d_dtep.find(tn) == d_dtep.end())
    {
      return n;
    }
    // eliminate the tester
    Assert(tn.isDatatype());
    const DType& dt = tn.getDType();
    size_t i = datatypes::utils::indexOf(n.getOperator());
    Node ticons = datatypes::utils::getInstCons(t, dt, i, false);
    Node eq = t.eqNode(ticons);
    return convert(eq);
  }
  else if (k == Kind::EQUAL)
  {
    Node t = n[0];
    TypeNode tn = t.getType();
    std::map<TypeNode, DtElimPolicy>::iterator itd = d_dtep.find(tn);
    if (itd == d_dtep.end())
    {
      return n;
    }
    Assert(tn.isDatatype());
    const DType& dt = tn.getDType();
    Node cur = d_nm->mkConst(false);
    for (size_t i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
    {
      size_t ii = ncons - i - 1;
      // their selectors are each equal
      const std::vector<Node>& sels1 = getSelectorVec(n[0], itd->second, ii);
      const std::vector<Node>& sels2 = getSelectorVec(n[1], itd->second, ii);
      Assert(sels1.size() == sels2.size());
      std::vector<Node> conj;
      for (size_t j = 0, nsels = sels1.size(); j < nsels; j++)
      {
        conj.push_back(sels1[j].eqNode(sels2[j]));
      }
      Node eq = d_nm->mkAnd(conj);
      if (ncons == 1)
      {
        cur = eq;
        break;
      }
      else
      {
        // if they are both this constructor, their selectors are equal
        Node tester1 = getTester(n[0], itd->second, ii);
        Node tester2 = getTester(n[1], itd->second, ii);
        Node cond = d_nm->mkNode(Kind::AND, tester1, tester2);
        cur = d_nm->mkNode(Kind::ITE, cond, eq, cur);
      }
    }
    return cur;
  }
  else if (k == Kind::APPLY_SELECTOR)
  {
    Node t = n[0];
    TypeNode tn = t.getType();
    std::map<TypeNode, DtElimPolicy>::iterator itd = d_dtep.find(tn);
    if (itd == d_dtep.end())
    {
      return n;
    }
    if (itd->second == DtElimPolicy::UNARY)
    {
      const std::vector<Node>& sels = getSelectorVec(t, itd->second, 0);
      size_t selectorIndex = datatypes::utils::indexOf(n.getOperator());
      Assert(selectorIndex < sels.size());
      return sels[selectorIndex];
    }
    else
    {
      // TODO: have to consider wrongly applied selectors, probably easy if
      // only one other constructor and is nullary.
      // size_t cindex = datatypes::utils::cindexOf(n.getOperator());
      Unhandled() << "Can't handle selector for non-unary datatype";
    }
  }
  else if (k != Kind::BOUND_VARIABLE && n.isVar())
  {
    // if a function variable, we may need to eliminate arguments
    TypeNode tn = n.getType();
    if (tn.isFunction())
    {
      Trace("dt-elim-debug") << "Process function " << n << std::endl;
      // check if any argument is a datatype, if so we replace by a lambda
      std::vector<TypeNode> argTypes = tn.getArgTypes();
      for (size_t i = 0, nargs = argTypes.size(); i < nargs; i++)
      {
        TypeNode tna = argTypes[i];
        std::map<TypeNode, DtElimPolicy>::iterator itd = d_dtep.find(tna);
        if (itd == d_dtep.end())
        {
          continue;
        }
        // otherwise we construct the appropriate lambda.
        std::vector<Node> vars;
        std::vector<Node> args;
        std::vector<Node> revVars;
        std::vector<Node> revArgs;
        for (size_t j = 0; j < nargs; j++)
        {
          tna = argTypes[j];
          if (j != i)
          {
            Node v = d_nm->mkBoundVar(tna);
            args.push_back(v);
            vars.push_back(v);
            revArgs.push_back(v);
            revVars.push_back(v);
            continue;
          }
          Assert(tna.isDatatype());
          const DType& dt = tna.getDType();
          // bool isInline = false;
          bool isInline = (dt.getNumConstructors() == 1);
          if (isInline)
          {
            Node dv = d_nm->mkBoundVar(tna);
            revVars.push_back(dv);
            std::vector<Node> consArg;
            consArg.push_back(dt[0].getConstructor());
            for (size_t s = 0, ndtargs = dt[0].getNumArgs(); s < ndtargs; s++)
            {
              Node sel =
                  d_nm->mkNode(Kind::APPLY_SELECTOR, dt[0].getSelector(s), dv);
              revArgs.push_back(sel);
              Node v = d_nm->mkBoundVar(dt[0].getArgType(s));
              vars.push_back(v);
              consArg.push_back(v);
            }
            Node cons = d_nm->mkNode(Kind::APPLY_CONSTRUCTOR, consArg);
            args.push_back(cons);
          }
          else if (isEnumPolicy(itd->second))
          {
            Node dv = d_nm->mkBoundVar(tna);
            TypeNode tnabs = getTypeAbstraction(tna);
            Node av = d_nm->mkBoundVar(tnabs);
            revVars.push_back(dv);
            revArgs.push_back(getDtAbstraction(dv));
            vars.push_back(av);
            args.push_back(getDtRevAbstraction(av, tna));
          }
          else
          {
            Unhandled()
                << "Can't handle function applied to 2+ constructor datatype "
                << tna;
          }
        }
        args.insert(args.begin(), n);
        Node lamBody = d_nm->mkNode(Kind::APPLY_UF, args);
        Node lam = vars.empty()
                       ? lamBody
                       : d_nm->mkNode(Kind::LAMBDA,
                                      d_nm->mkNode(Kind::BOUND_VAR_LIST, vars),
                                      lamBody);
        Node nnew = SkolemManager::mkPurifySkolem(lam);
        // recursively convert the operator
        Node revLamBody = convert(nnew);
        if (!revArgs.empty())
        {
          revArgs.insert(revArgs.begin(), nnew);
          revLamBody = d_nm->mkNode(Kind::APPLY_UF, revArgs);
        }
        Node revLam =
            revVars.empty()
                ? revLamBody
                : d_nm->mkNode(Kind::LAMBDA,
                               d_nm->mkNode(Kind::BOUND_VAR_LIST, revVars),
                               revLamBody);
        Trace("dt-elim") << "*** Replace " << n << " with " << revLam
                         << std::endl;
        Trace("dt-elim") << "  where " << nnew << " is " << lam << std::endl;
        d_modelSubs[n] = revLam;
        return revLam;
      }
    }
    // otherwise maybe its return is a datatype
    Node ret = getModelElimination(n);
    if (!ret.isNull())
    {
      Assert(ret.getType() == n.getType());
      return n;
    }
  }
  else if (k == Kind::APPLY_UF && n.getOperator().getKind() == Kind::LAMBDA)
  {
    // apply full rewriter, as this may induce selector collapses in
    // addition to beta reduction
    Node nc = rewrite(n);
    Trace("dt-elim") << "Beta reduce " << n << " to " << nc << std::endl;
    Assert(nc != n);
    return convert(nc);
  }
  return n;
}

Node DtElimConverter::getDtAbstraction(const Node& v)
{
  Assert(v.isVar() || v.getKind() == Kind::APPLY_UF);
  TypeNode vtn = v.getType();
  Assert(vtn.isDatatype());
  const std::vector<Node>& cvec = getConstructorVec(vtn);
  const DType& dt = vtn.getDType();
  Assert(cvec.size() == dt.getNumConstructors());
  Node cur = cvec[0];
  for (size_t i = 1, ncons = dt.getNumConstructors(); i < ncons; i++)
  {
    Node tester = datatypes::utils::mkTester(v, i, dt);
    cur = d_nm->mkNode(Kind::ITE, tester, cvec[i], cur);
  }
  return cur;
}

Node DtElimConverter::getDtRevAbstraction(const Node& v, const TypeNode& dtn)
{
  Assert(v.isVar() || v.getKind() == Kind::APPLY_UF);
  Assert(dtn.isDatatype());
  const std::vector<Node>& cvec = getConstructorVec(dtn);
  const DType& dt = dtn.getDType();
  Assert(cvec.size() == dt.getNumConstructors());
  Node cur = d_nm->mkNode(Kind::APPLY_CONSTRUCTOR, {dt[0].getConstructor()});
  for (size_t i = 1, ncons = dt.getNumConstructors(); i < ncons; i++)
  {
    Node tester = v.eqNode(cvec[i]);
    Node cons = d_nm->mkNode(Kind::APPLY_CONSTRUCTOR, {dt[i].getConstructor()});
    cur = d_nm->mkNode(Kind::ITE, tester, cons, cur);
  }
  return cur;
}

Node DtElimConverter::getTesterFunctionInternal(const Node& v,
                                                DtElimPolicy policy)
{
  Assert(v.getKind() == Kind::APPLY_UF);
  Node op = v.getOperator();
  std::map<Node, Node>::iterator it = d_tester.find(op);
  if (it != d_tester.end())
  {
    return it->second;
  }
  std::vector<Node> lamArgs;
  for (const Node& vc : v)
  {
    lamArgs.push_back(d_nm->mkBoundVar(vc.getType()));
  }
  Node lbvl = d_nm->mkNode(Kind::BOUND_VAR_LIST, lamArgs);
  lamArgs.insert(lamArgs.begin(), v.getOperator());
  Node lbody = d_nm->mkNode(Kind::APPLY_UF, lamArgs);
  if (isBinaryTestPolicy(policy))
  {
    TypeNode vtn = v.getType();
    Assert(vtn.isDatatype());
    const DType& dt = vtn.getDType();
    lbody = datatypes::utils::mkTester(lbody, 0, dt);
  }
  else if (isAbstractPolicy(policy))
  {
    lbody = getDtAbstraction(lbody);
  }
  else
  {
    Unhandled() << "getTesterFunctionInternal: Unknown policy " << policy;
  }
  Node lam = d_nm->mkNode(Kind::LAMBDA, lbvl, lbody);
  return SkolemManager::mkPurifySkolem(lam);
}

Node DtElimConverter::getTesterInternal(const Node& v, DtElimPolicy policy)
{
  Kind vk = v.getKind();
  if (vk == Kind::BOUND_VARIABLE || (!v.isVar() && vk != Kind::APPLY_UF))
  {
    Unhandled() << "Cannot get tester for " << v;
  }
  std::map<Node, Node>::iterator it = d_tester.find(v);
  if (it != d_tester.end())
  {
    return it->second;
  }
  Node tester;
  if (vk == Kind::APPLY_UF)
  {
    std::vector<Node> ufArgs;
    ufArgs.push_back(getTesterFunctionInternal(v, policy));
    ufArgs.insert(ufArgs.end(), v.begin(), v.end());
    tester = d_nm->mkNode(Kind::APPLY_UF, ufArgs);
  }
  else
  {
    // The tester for v : (Option-Bool), call it v-is-some, is equivalent
    // to ((_ is some) v). Analoguously if abstract, we use
    // v-get-cons which is equivalent to (ite ((_ is some) v) U_some U_none).
    Assert(v.isVar() && v.getKind() != Kind::BOUND_VARIABLE);
    if (isBinaryTestPolicy(policy))
    {
      TypeNode vtn = v.getType();
      Assert(vtn.isDatatype());
      const DType& dt = vtn.getDType();
      Node tpred = datatypes::utils::mkTester(v, 0, dt);
      tester = SkolemManager::mkPurifySkolem(tpred);
    }
    else if (isAbstractPolicy(policy))
    {
      Node consKind = getDtAbstraction(v);
      tester = SkolemManager::mkPurifySkolem(consKind);
    }
    else
    {
      Unhandled() << "getTesterInternal: Unknown policy " << policy;
    }
  }
  Assert(!isBinaryTestPolicy(policy) || tester.getType().isBoolean());
  Assert(!isAbstractPolicy(policy)
         || tester.getType() == getTypeAbstraction(v.getType()));
  d_tester[v] = tester;
  return tester;
}

Node DtElimConverter::getTester(const Node& v, DtElimPolicy policy, size_t i)
{
  Node tester = getTesterInternal(v, policy);
  if (isBinaryTestPolicy(policy))
  {
    return i == 0 ? tester : tester.notNode();
  }
  else if (isAbstractPolicy(policy))
  {
    TypeNode vtn = v.getType();
    const std::vector<Node>& cvec = getConstructorVec(vtn);
    Assert(i < cvec.size());
    return tester.eqNode(cvec[i]);
  }
  else
  {
    Unhandled() << "getTester: Unknown policy " << policy;
  }
  return Node::null();
}

const std::vector<Node>& DtElimConverter::getSelectorVecInternal(const Node& v,
                                                                 size_t i)
{
  Kind vk = v.getKind();
  if (vk == Kind::BOUND_VARIABLE || (!v.isVar() && vk != Kind::APPLY_UF))
  {
    Unhandled() << "Cannot get selector for " << v << " " << vk;
  }
  std::pair<Node, size_t> key(v, i);
  std::map<std::pair<Node, size_t>, std::vector<Node>>::iterator it =
      d_selectors.find(key);
  if (it != d_selectors.end())
  {
    return it->second;
  }
  std::vector<Node> sels;
  if (v.getKind() == Kind::APPLY_UF)
  {
    const std::vector<Node>& funSelVec =
        getSelectorVecInternal(v.getOperator(), i);
    std::vector<Node> appArgs;
    appArgs.push_back(Node::null());
    appArgs.insert(appArgs.end(), v.begin(), v.end());
    for (size_t j = 0, nsels = funSelVec.size(); j < nsels; j++)
    {
      appArgs[0] = funSelVec[j];
      Node selApp = d_nm->mkNode(Kind::APPLY_UF, appArgs);
      sels.push_back(selApp);
    }
  }
  else
  {
    TypeNode tn = v.getType();
    std::vector<Node> args;
    Node vi = v;
    if (tn.isFunction())
    {
      std::vector<Node> appArgs;
      appArgs.push_back(v);
      std::vector<TypeNode> argTypes = tn.getArgTypes();
      for (const TypeNode& tna : argTypes)
      {
        Node vv = d_nm->mkBoundVar(tna);
        appArgs.push_back(vv);
        args.push_back(vv);
      }
      tn = tn.getRangeType();
      vi = d_nm->mkNode(Kind::APPLY_UF, appArgs);
    }
    Assert(tn.isDatatype());
    const DType& dt = tn.getDType();
    Assert(i < dt.getNumConstructors());
    Trace("dt-elim") << "*** Replace " << v << " with selectors" << std::endl;
    std::vector<Node> consAppChildren;
    consAppChildren.push_back(dt[i].getConstructor());
    for (size_t s = 0, ndtargs = dt[i].getNumArgs(); s < ndtargs; s++)
    {
      Node sel = d_nm->mkNode(Kind::APPLY_SELECTOR, dt[0].getSelector(s), vi);
      if (!args.empty())
      {
        sel = d_nm->mkNode(
            Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, args), sel);
      }
      Node ksel = SkolemManager::mkPurifySkolem(sel);
      sels.push_back(ksel);
      Trace("dt-elim") << "- " << ksel << " which is " << sel << std::endl;
      if (!args.empty())
      {
        std::vector<Node> selApp;
        selApp.push_back(ksel);
        selApp.insert(selApp.end(), args.begin(), args.end());
        ksel = d_nm->mkNode(Kind::APPLY_UF, selApp);
      }
      consAppChildren.push_back(ksel);
    }
    Node consApp = d_nm->mkNode(Kind::APPLY_CONSTRUCTOR, consAppChildren);
    if (!args.empty())
    {
      consApp = d_nm->mkNode(
          Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, args), consApp);
    }
    Trace("dt-elim") << "-> " << v << " for constructor " << dt[i].getName()
                     << " is " << consApp << std::endl;
    d_selectorsElim[key] = consApp;
  }
  d_selectors[key] = sels;
  return d_selectors[key];
}

const std::vector<Node>& DtElimConverter::getSelectorVec(const Node& v,
                                                         DtElimPolicy policy,
                                                         size_t i)
{
  Kind vk = v.getKind();
  if (vk == Kind::APPLY_CONSTRUCTOR)
  {
    size_t constructorIndex = datatypes::utils::indexOf(v.getOperator());
    if (i == constructorIndex)
    {
      std::pair<Node, size_t> key(v, i);
      std::vector<Node>& ret = d_selectors[key];
      if (ret.empty() && v.getNumChildren() > 0)
      {
        ret.insert(ret.end(), v.begin(), v.end());
      }
      return ret;
    }
    // null if empty
    TypeNode tn = v.getType();
    Assert(tn.isDatatype());
    const DType& dt = tn.getDType();
    if (dt[i].getNumArgs() == 0)
    {
      std::pair<Node, size_t> key(v, i);
      Assert(d_selectors[key].empty());
      return d_selectors[key];
    }
  }
  else if (vk == Kind::ITE)
  {
    const std::vector<Node>& s1 = getSelectorVec(v[1], policy, i);
    const std::vector<Node>& s2 = getSelectorVec(v[2], policy, i);
    Assert(s1.size() == s2.size());
    std::pair<Node, size_t> key(v, i);
    std::vector<Node>& ret = d_selectors[key];
    if (ret.empty() && !s1.empty())
    {
      for (size_t j = 0, nsels = s1.size(); j < nsels; j++)
      {
        Node rs = d_nm->mkNode(Kind::ITE, v[0], s1[j], s2[j]);
        ret.push_back(rs);
      }
    }
    return ret;
  }
  const std::vector<Node>& ret = getSelectorVecInternal(v, i);
  Node ve = vk == Kind::APPLY_UF ? v.getOperator() : v;
  // ensure its model elimination has been processed
  getModelElimination(ve);
  return ret;
}
Node DtElimConverter::getModelElimination(const Node& v)
{
  std::map<Node, Node>::iterator itm = d_modelSubs.find(v);
  if (itm != d_modelSubs.end())
  {
    return itm->second;
  }
  Node vinst = v;
  std::vector<Node> vars;
  TypeNode tn = v.getType();
  if (tn.isFunction())
  {
    std::vector<TypeNode> argTypes = tn.getArgTypes();
    std::vector<Node> cons;
    cons.push_back(v);
    for (const TypeNode& tna : argTypes)
    {
      Node lv = d_nm->mkBoundVar(tna);
      vars.push_back(lv);
      cons.push_back(lv);
    }
    vinst = d_nm->mkNode(Kind::APPLY_UF, cons);
    tn = tn.getRangeType();
  }
  std::map<TypeNode, DtElimPolicy>::iterator itd = d_dtep.find(tn);
  if (itd == d_dtep.end())
  {
    d_modelSubs[v] = Node::null();
    return Node::null();
  }
  Assert(tn.isDatatype());
  const DType& dt = tn.getDType();
  Node cur;
  std::map<std::pair<Node, size_t>, Node>::iterator its;
  for (size_t j = 0, ncons = dt.getNumConstructors(); j < ncons; j++)
  {
    getSelectorVecInternal(vinst, j);
    std::pair<Node, size_t> key(v, j);
    its = d_selectorsElim.find(key);
    Assert(its != d_selectorsElim.end());
    if (cur.isNull())
    {
      cur = its->second;
    }
    else
    {
      Node tester = getTester(vinst, itd->second, j);
      cur = d_nm->mkNode(Kind::ITE, tester, its->second, cur);
    }
  }
  /*
  if (!vars.empty())
  {
    cur = d_nm->mkNode(Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, vars),
  cur);
  }
  */
  Trace("dt-elim") << "*** Overall elimination for " << v << " is " << cur
                   << std::endl;
  d_modelSubs[v] = cur;
  return cur;
}

TypeNode DtElimConverter::getTypeAbstraction(const TypeNode& dt)
{
  Assert(dt.isDatatype());
  std::map<TypeNode, TypeNode>::iterator it = d_typeAbs.find(dt);
  if (it != d_typeAbs.end())
  {
    return it->second;
  }
  TypeNode ret = nodeManager()->mkSort(d_dtElimSc, {dt});
  d_typeAbs[dt] = ret;
  return ret;
}

const std::vector<Node>& DtElimConverter::getConstructorVec(const TypeNode& tn)
{
  Assert(tn.isDatatype());
  std::map<TypeNode, std::vector<Node>>::iterator it = d_constructors.find(tn);
  if (it != d_constructors.end())
  {
    return it->second;
  }
  TypeNode u = getTypeAbstraction(tn);
  std::vector<Node>& cons = d_constructors[tn];
  const DType& dt = tn.getDType();
  SkolemManager* skm = d_nm->getSkolemManager();
  for (size_t i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
  {
    Node id = d_nm->mkConstInt(Rational(i));
    Node k = skm->mkInternalSkolemFunction(
        InternalSkolemId::DT_ELIM_CONS_ABSTRACTION, u, {id});
    cons.push_back(k);
  }
  // distinctness is a lemma
  if (cons.size() > 1)
  {
    Node distinct = d_nm->mkNode(Kind::DISTINCT, cons);
    d_newLemmas.push_back(distinct);
  }
  return cons;
}

DtElim::DtElim(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "dt-elim")
{
}

PreprocessingPassResult DtElim::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  DtElimConverter dec(d_env, assertionsToPreprocess->ref());
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node a = (*assertionsToPreprocess)[i];
    Node ac = dec.convert(a);
    if (a != ac)
    {
      Trace("dt-elim-assert")
          << "DtElim: Rewrite " << a << " to " << ac << std::endl;
      assertionsToPreprocess->replace(
          i, ac, nullptr, TrustId::PREPROCESS_DT_ELIM);
      Assert(!expr::hasFreeVar(ac));
    }
  }
  const std::vector<Node>& lems = dec.getNewLemmas();
  for (const Node& lem : lems)
  {
    assertionsToPreprocess->push_back(
        lem, false, nullptr, TrustId::PREPROCESS_DT_ELIM, true);
    Assert(!expr::hasFreeVar(lem)) << "Bad lemma " << lem;
  }
  const std::map<Node, Node>& msubs = dec.getModelSubstitutions();
  for (const std::pair<const Node, Node>& s : msubs)
  {
    if (s.second.isNull())
    {
      continue;
    }
    Assert(s.first.getType() == s.second.getType());
    d_preprocContext->addSubstitution(s.first, s.second);
    Assert(!expr::hasFreeVar(s.second));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

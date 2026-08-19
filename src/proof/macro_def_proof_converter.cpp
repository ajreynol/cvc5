/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the macro definition proof converter.
 */

#include "proof/macro_def_proof_converter.h"

#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_manager.h"
#include "proof/proof_rule_checker.h"
#include "smt/env.h"

namespace cvc5::internal {

MacroDefConverterCallback::MacroDefConverterCallback(
    Env& env, const std::vector<Node>& defs)
    : EnvObj(env), d_brc(nodeManager()), d_pc(nullptr)
{
  for (const Node& d : defs)
  {
    Assert(d.getKind() == Kind::EQUAL && d[0].isVar());
    if (!d_subs.hasSubstitution(d[0]))
    {
      d_subs.addSubstitution(d[0], d[1]);
    }
  }
  d_pc = d_env.getProofNodeManager()->getChecker();
}

Node MacroDefConverterCallback::expandTerm(const Node& n)
{
  std::unordered_map<Node, Node>::iterator it = d_ecache.find(n);
  if (it != d_ecache.end())
  {
    return it->second;
  }
  Node ns = d_subs.apply(n);
  d_ecache[n] = ns;
  return ns;
}

Node MacroDefConverterCallback::convertTerm(const Node& n)
{
  std::unordered_map<Node, Node>::iterator it = d_cache.find(n);
  if (it != d_cache.end())
  {
    return it->second;
  }
  // Note that we eliminate *all* beta redexes, not only the ones introduced
  // by the substitution. This is required since the applications of the
  // defined functions were expanded by preprocessing as well, where the redexes
  // this introduced occur in the proof of preprocessing. Note we do not rewrite
  // here, since the converted proof should remain as close as possible to the
  // original one.
  Node ns = d_brc.convert(expandTerm(n));
  d_cache[n] = ns;
  return ns;
}

bool MacroDefConverterCallback::isMacroExpansion(const Node& n) const
{
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  visit.push_back(n);
  do
  {
    TNode cur = visit.back();
    visit.pop_back();
    if (!visited.insert(cur).second)
    {
      continue;
    }
    if (cur.getKind() == Kind::APPLY_UF)
    {
      TNode op = cur.getOperator();
      if (op.getKind() == Kind::LAMBDA)
      {
        // A beta redex from the input, which is eliminated by the conversion,
        // whereas macro expansion would retain it.
        return false;
      }
      if (isMacroWithParams(op))
      {
        // An application of a definition with parameters, which is fully
        // applied by construction of APPLY_UF. Note we do not traverse the
        // operator, since it is expanded as a macro.
        visit.insert(visit.end(), cur.begin(), cur.end());
        continue;
      }
      visit.push_back(op);
    }
    else if (isMacroWithParams(cur))
    {
      // An occurrence of a definition with parameters that is not applied,
      // e.g. where it is passed as a higher-order argument. Expanding it
      // requires replacing it by a lambda term.
      return false;
    }
    visit.insert(visit.end(), cur.begin(), cur.end());
  } while (!visit.empty());
  return true;
}

bool MacroDefConverterCallback::isMacroWithParams(TNode n) const
{
  return n.isVar() && d_subs.hasSubstitution(n)
         && d_subs.getSubstitution(n).getKind() == Kind::LAMBDA;
}

bool MacroDefConverterCallback::shouldConvert(std::shared_ptr<ProofNode> pn)
{
  const std::vector<Node>& args = pn->getArguments();
  for (const Node& a : args)
  {
    if (convertTerm(a) != a)
    {
      return true;
    }
  }
  Node res = pn->getResult();
  return convertTerm(res) != res;
}

Node MacroDefConverterCallback::convert(Node res,
                                        ProofRule id,
                                        const std::vector<Node>& children,
                                        const std::vector<Node>& args,
                                        CDProof* cdp)
{
  std::vector<Node> cargs;
  std::vector<Node> eargs;
  bool argsDiffer = false;
  for (const Node& a : args)
  {
    cargs.push_back(convertTerm(a));
    eargs.push_back(expandTerm(a));
    argsDiffer = argsDiffer || cargs.back() != eargs.back();
  }
  // the conclusion we are required to prove
  Node resc = convertTerm(res);
  Trace("pf-macro-def") << "Convert " << id << " to prove " << resc
                        << std::endl;
  // Trivial case: the conclusion is now an equality between identical terms.
  // This is the case e.g. for the assumption of a definition, and for the
  // beta reduction steps that expanded its applications.
  if (resc.getKind() == Kind::EQUAL && resc[0] == resc[1])
  {
    cdp->addStep(resc, ProofRule::REFL, {}, {resc[0]});
    return resc;
  }
  // The step may have become superfluous, e.g. a transitivity step whose
  // remaining premises are reflexivity. In this case we take the premise.
  if (std::find(children.begin(), children.end(), resc) != children.end())
  {
    return resc;
  }
  if (id == ProofRule::CONG && !eargs.empty() && eargs[0].hasOperator()
      && eargs[0].getOperator().getKind() == Kind::LAMBDA)
  {
    // Congruence over an application of a defined function. Since its operator
    // is a lambda after expanding the definition, we use higher-order
    // congruence, which additionally takes the (reflexivity of the) operator
    // as a premise.
    Node op = eargs[0].getOperator();
    Node opeq = op.eqNode(op);
    cdp->addStep(opeq, ProofRule::REFL, {}, {op});
    std::vector<Node> hchildren;
    hchildren.push_back(opeq);
    hchildren.insert(hchildren.end(), children.begin(), children.end());
    std::vector<Node> hargs;
    hargs.push_back(
        ProofRuleChecker::mkKindNode(nodeManager(), eargs[0].getKind()));
    Node newRes;
    if (tryWith(ProofRule::HO_CONG, hchildren, hargs, resc, newRes, cdp)
        || bridgeBeta(ProofRule::HO_CONG, hchildren, hargs, newRes, resc, cdp))
    {
      return resc;
    }
  }
  // We try the rule with the converted arguments first. If this fails, we try
  // it with the arguments where the definitions are expanded but the beta
  // redexes this introduces are *not* eliminated. The latter is required e.g.
  // for congruence, where the argument determines the operator of the
  // conclusion, which is lost when the application is beta reduced.
  std::vector<std::vector<Node>> argsTry;
  argsTry.push_back(cargs);
  if (argsDiffer)
  {
    argsTry.push_back(eargs);
  }
  for (const std::vector<Node>& ta : argsTry)
  {
    Node newRes;
    if (tryWith(id, children, ta, resc, newRes, cdp))
    {
      return resc;
    }
    if (bridgeBeta(id, children, ta, newRes, resc, cdp))
    {
      return resc;
    }
  }
  // Otherwise we fail to convert the step. Note this does not occur for the
  // steps that involve definitions, which are handled above.
  Trace("pf-macro-def-warn") << "WARNING: failed to convert " << id
                             << " to prove " << resc << std::endl;
  Trace("pf-macro-def-warn") << "  premises: " << children << std::endl;
  Trace("pf-macro-def-warn") << "  args: " << cargs << std::endl;
  cdp->addTrustedStep(resc, TrustId::UNKNOWN_PREPROCESS, children, {});
  return resc;
}

bool MacroDefConverterCallback::bridgeBeta(ProofRule id,
                                           const std::vector<Node>& children,
                                           const std::vector<Node>& args,
                                           const Node& newRes,
                                           const Node& resc,
                                           CDProof* cdp)
{
  // The rule proves an equality that is not the required one, where the two
  // are related by beta reduction. This is the case e.g. for congruence over
  // an application of a defined function, where HO_CONG proves
  //   (= ((lambda ((x Int)) (+ x 1)) a) ((lambda ((x Int)) (+ 1 x)) a))
  // whereas we require (= (+ a 1) (+ 1 a)). We connect the two by beta
  // reducing both sides.
  if (newRes.isNull() || newRes.getKind() != Kind::EQUAL
      || resc.getKind() != Kind::EQUAL)
  {
    return false;
  }
  if (!proveBeta(newRes[0], resc[0], cdp)
      || !proveBeta(newRes[1], resc[1], cdp))
  {
    return false;
  }
  if (!cdp->addStep(newRes, id, children, args))
  {
    return false;
  }
  std::vector<Node> tchildren;
  if (newRes[0] != resc[0])
  {
    Node eqs = newRes[0].eqNode(resc[0]);
    cdp->addStep(resc[0].eqNode(newRes[0]), ProofRule::SYMM, {eqs}, {});
    tchildren.push_back(resc[0].eqNode(newRes[0]));
  }
  tchildren.push_back(newRes);
  if (newRes[1] != resc[1])
  {
    tchildren.push_back(newRes[1].eqNode(resc[1]));
  }
  Trace("pf-macro-def") << "...connect " << newRes << " via beta reduction"
                        << std::endl;
  return cdp->addStep(resc, ProofRule::TRANS, tchildren, {});
}

bool MacroDefConverterCallback::tryWith(ProofRule id,
                                        const std::vector<Node>& children,
                                        const std::vector<Node>& args,
                                        const Node& expected,
                                        Node& newRes,
                                        CDProof* cdp)
{
  newRes = d_pc->checkDebug(id, children, args);
  if (!newRes.isNull() && newRes == expected)
  {
    cdp->addStep(newRes, id, children, args);
    return true;
  }
  return false;
}

bool MacroDefConverterCallback::proveBeta(const Node& a,
                                          const Node& b,
                                          CDProof* cdp)
{
  if (a == b)
  {
    return true;
  }
  if (d_brc.convert(a) != b)
  {
    return false;
  }
  Node eq = a.eqNode(b);
  return cdp->addTheoryRewriteStep(eq, ProofRewriteRule::BETA_REDUCE);
}

}  // namespace cvc5::internal

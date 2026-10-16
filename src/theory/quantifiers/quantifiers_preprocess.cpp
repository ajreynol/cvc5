/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Preprocessor for the theory of quantifiers.
 */

#include "theory/quantifiers/quantifiers_preprocess.h"

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "proof/eager_proof_generator.h"
#include "proof/proof.h"
#include "proof/proof_node_algorithm.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/skolemize.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

QuantifiersPreprocess::QuantifiersPreprocess(Env& env)
    : EnvObj(env),
      d_qrew(nodeManager(), env.getRewriter(), options()),
      d_epg(env.isProofProducing()
                ? new EagerProofGenerator(
                      env, userContext(), "QuantifiersPreprocess::epg")
                : nullptr)
{
}

QuantifiersPreprocess::~QuantifiersPreprocess() {}

Node QuantifiersPreprocess::computePrenexAgg(
    Node n, std::map<Node, Node>& visited) const
{
  std::map<Node, Node>::iterator itv = visited.find(n);
  if (itv != visited.end())
  {
    return itv->second;
  }
  if (!expr::hasClosure(n))
  {
    // trivial
    return n;
  }
  NodeManager* nm = nodeManager();
  Node ret = n;
  if (n.getKind() == Kind::NOT)
  {
    ret = computePrenexAgg(n[0], visited).negate();
  }
  else if (n.getKind() == Kind::FORALL)
  {
    std::vector<Node> children;
    children.push_back(computePrenexAgg(n[1], visited));
    std::vector<Node> args;
    args.insert(args.end(), n[0].begin(), n[0].end());
    // only combine if standard
    if (d_qrew.isStandard(n, options()))
    {
      // for each child, strip top level quant
      for (unsigned i = 0; i < children.size(); i++)
      {
        if (children[i].getKind() == Kind::FORALL)
        {
          args.insert(args.end(), children[i][0].begin(), children[i][0].end());
          children[i] = children[i][1];
        }
      }
    }
    // keep the pattern
    std::vector<Node> iplc;
    if (n.getNumChildren() == 3)
    {
      iplc.insert(iplc.end(), n[2].begin(), n[2].end());
    }
    Node nb = nm->mkOr(children);
    ret = d_qrew.mkForall(args, nb, iplc, true);
  }
  else
  {
    Node q;
    std::vector<Node> args, nargs;
    Node nn = d_qrew.computePrenex(q, n, args, nargs, true, true);
    std::unordered_set<Node> argsSet(args.begin(), args.end());
    std::unordered_set<Node> nargsSet(nargs.begin(), nargs.end());
    Assert(n != nn || argsSet.empty());
    Assert(n != nn || nargsSet.empty());
    if (n != nn)
    {
      Node nnn = computePrenexAgg(nn, visited);
      // merge prenex
      if (nnn.getKind() == Kind::FORALL)
      {
        argsSet.insert(nnn[0].begin(), nnn[0].end());
        nnn = nnn[1];
        // pos polarity variables are inner
        if (!argsSet.empty())
        {
          nnn = d_qrew.mkForall({argsSet.begin(), argsSet.end()}, nnn, true);
        }
        argsSet.clear();
      }
      else if (nnn.getKind() == Kind::NOT && nnn[0].getKind() == Kind::FORALL)
      {
        nargsSet.insert(nnn[0][0].begin(), nnn[0][0].end());
        nnn = nnn[0][1].negate();
      }
      if (!nargsSet.empty())
      {
        nnn = d_qrew
                  .mkForall(
                      {nargsSet.begin(), nargsSet.end()}, nnn.negate(), true)
                  .negate();
      }
      if (!argsSet.empty())
      {
        nnn = d_qrew.mkForall({argsSet.begin(), argsSet.end()}, nnn, true);
      }
      ret = nnn;
    }
  }
  visited[n] = ret;
  return ret;
}

Node QuantifiersPreprocess::preSkolemizeQuantifiers(
    Node n,
    bool polarity,
    std::vector<TNode>& fvs,
    std::unordered_map<std::pair<Node, bool>, Node, NodePolPairHashFunction>&
        visited,
    CDProof* cdp) const
{
  Assert(options().quantifiers.preSkolemQuant
         != options::PreSkolemQuantMode::OFF);
  std::pair<Node, bool> key(n, polarity);
  std::unordered_map<std::pair<Node, bool>, Node, NodePolPairHashFunction>::
      iterator it = visited.find(key);
  if (it != visited.end())
  {
    return it->second;
  }
  NodeManager* nm = nodeManager();
  Trace("pre-sk") << "Pre-skolem " << n << " " << polarity << " " << fvs.size()
                  << std::endl;
  if (n.getKind() == Kind::FORALL)
  {
    Node ret = n;
    if (n.getNumChildren() == 3)
    {
      // Do not pre-skolemize quantified formulas with three children.
      // This includes non-standard quantified formulas
      // like recursive function definitions, or sygus conjectures, and
      // quantified formulas with triggers.
    }
    else if (polarity)
    {
      if (options().quantifiers.preSkolemQuantNested)
      {
        std::vector<Node> children;
        children.push_back(n[0]);
        // add children to current scope
        std::vector<TNode> fvss;
        fvss.insert(fvss.end(), fvs.begin(), fvs.end());
        fvss.insert(fvss.end(), n[0].begin(), n[0].end());
        // process body in a new context
        std::unordered_map<std::pair<Node, bool>, Node, NodePolPairHashFunction>
            visitedSub;
        Node pbody =
            preSkolemizeQuantifiers(n[1], polarity, fvss, visitedSub, nullptr);
        children.push_back(pbody);
        // return processed quantifier
        ret = nm->mkNode(Kind::FORALL, children);
        // the body is skolemized using fresh functions, which does not have
        // proof support
        if (cdp != nullptr && ret != n)
        {
          cdp->addTrustedStep(
              n.eqNode(ret), TrustId::QUANTIFIERS_PREPROCESS, {}, {});
        }
      }
    }
    else
    {
      bool hasInd = false;
      for (const Node& v : n[0])
      {
        if (Skolemize::isInductionTerm(options(), v))
        {
          hasInd = true;
          break;
        }
      }
      if (fvs.empty() && !hasInd)
      {
        // Skolemize current using the skolems of n, which are the same as
        // those used by SKOLEMIZE, then process the body. Note that we
        // substitute before processing the body to ensure that quantified
        // formulas we skolemize in the body are closed.
        std::vector<Node> vars(n[0].begin(), n[0].end());
        std::vector<Node> skc = Skolemize::getSkolemConstants(n);
        Node body =
            n[1].substitute(vars.begin(), vars.end(), skc.begin(), skc.end());
        if (cdp != nullptr)
        {
          proveSkolemizeEq(cdp, n, body);
        }
        ret = preSkolemizeQuantifiers(body, polarity, fvs, visited, cdp);
        if (cdp != nullptr)
        {
          addTrans(cdp, n, body, ret);
        }
        // if it has an instantiation level, set the skolemized body to that
        // level
        uint64_t level;
        if (QuantAttributes::getInstantiationLevel(n, level))
        {
          QuantAttributes::setInstantiationLevelAttr(ret, level);
        }
      }
      else
      {
        // will skolemize current, process body
        Node nn = preSkolemizeQuantifiers(n[1], polarity, fvs, visited, nullptr);
        std::vector<Node> sk;
        Node sub;
        std::vector<unsigned> sub_vars;
        // return skolemized body
        ret = Skolemize::mkSkolemizedBodyInduction(
            options(), n, nn, fvs, sk, sub, sub_vars);
        // skolemization with fresh functions or inductive strengthening does
        // not have proof support
        if (cdp != nullptr && ret != n)
        {
          cdp->addTrustedStep(
              n.eqNode(ret), TrustId::QUANTIFIERS_PREPROCESS, {}, {});
        }
      }
    }
    visited[key] = ret;
    return ret;
  }
  // check if it contains a quantifier as a subterm
  // if so, we may preprocess this node
  if (!expr::hasClosure(n))
  {
    visited[key] = n;
    return n;
  }
  Kind k = n.getKind();
  Node ret = n;
  Assert(n.getType().isBoolean());
  if (k == Kind::ITE || (k == Kind::EQUAL && n[0].getType().isBoolean()))
  {
    if (options().quantifiers.preSkolemQuant
        == options::PreSkolemQuantMode::AGG)
    {
      Node nn;
      // must remove structure
      if (k == Kind::ITE)
      {
        nn = nm->mkNode(Kind::AND,
                        {nm->mkNode(Kind::OR, n[0].notNode(), n[1]),
                         nm->mkNode(Kind::OR, n[0], n[2])});
      }
      else if (k == Kind::EQUAL)
      {
        nn = nm->mkNode(Kind::AND,
                        {nm->mkNode(Kind::OR, n[0].notNode(), n[1]),
                         nm->mkNode(Kind::OR, n[0], n[1].notNode())});
      }
      if (cdp != nullptr)
      {
        cdp->addTrustedStep(
            n.eqNode(nn), TrustId::QUANTIFIERS_PREPROCESS, {}, {});
      }
      ret = preSkolemizeQuantifiers(nn, polarity, fvs, visited, cdp);
      if (cdp != nullptr)
      {
        addTrans(cdp, n, nn, ret);
      }
    }
  }
  else if (k == Kind::AND || k == Kind::OR || k == Kind::NOT
           || k == Kind::IMPLIES)
  {
    std::vector<Node> children;
    std::vector<Node> premises;
    for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; i++)
    {
      bool newHasPol;
      bool newPol;
      QuantPhaseReq::getPolarity(n, i, true, polarity, newHasPol, newPol);
      Assert(newHasPol);
      Node nc = preSkolemizeQuantifiers(n[i], newPol, fvs, visited, cdp);
      children.push_back(nc);
      premises.push_back(nc == n[i] ? Node::null() : n[i].eqNode(nc));
    }
    ret = nm->mkNode(k, children);
    if (cdp != nullptr && ret != n)
    {
      [[maybe_unused]] Node eq = expr::proveCong(d_env, cdp, n, premises);
      Assert(eq == n.eqNode(ret));
    }
  }
  visited[key] = ret;
  return ret;
}

void QuantifiersPreprocess::proveSkolemizeEq(CDProof* cdp,
                                             const Node& q,
                                             const Node& body) const
{
  Assert(q.getKind() == Kind::FORALL);
  NodeManager* nm = nodeManager();
  Node eq = q.eqNode(body);
  if (body.isConst())
  {
    // SCOPE treats a conclusion of false specially, this case does not happen
    // since the body of q is rewritten
    cdp->addTrustedStep(eq, TrustId::QUANTIFIERS_PREPROCESS, {}, {});
    return;
  }
  // We use a separate proof to ensure the assumptions q and (not q) are not
  // justified by other steps in cdp.
  CDProof lcdp(d_env);
  Node tt = nm->mkConst(true);
  Node nq = q.notNode();
  Node nbody = body.notNode();
  // (=> q body) by INSTANTIATE
  std::vector<Node> skc = Skolemize::getSkolemConstants(q);
  lcdp.addStep(body, ProofRule::INSTANTIATE, {q}, {nm->mkNode(Kind::SEXPR, skc)});
  Node imp1 = nm->mkNode(Kind::IMPLIES, q, body);
  lcdp.addStep(imp1, ProofRule::SCOPE, {body}, {q});
  Node c1 = nm->mkNode(Kind::OR, nq, body);
  lcdp.addStep(c1, ProofRule::IMPLIES_ELIM, {imp1}, {});
  // (=> (not q) (not body)) by SKOLEMIZE
  lcdp.addStep(nbody, ProofRule::SKOLEMIZE, {nq}, {});
  Node imp2 = nm->mkNode(Kind::IMPLIES, nq, nbody);
  lcdp.addStep(imp2, ProofRule::SCOPE, {nbody}, {nq});
  Node c2 = nm->mkNode(Kind::OR, nq.notNode(), nbody);
  lcdp.addStep(c2, ProofRule::IMPLIES_ELIM, {imp2}, {});
  // (or (= q body) q body) and (or (= q body) (not q) (not body))
  Node cn1 = nm->mkNode(Kind::OR, eq, q, body);
  lcdp.addStep(cn1, ProofRule::CNF_EQUIV_NEG1, {}, {eq});
  Node cn2 = nm->mkNode(Kind::OR, eq, nq, nbody);
  lcdp.addStep(cn2, ProofRule::CNF_EQUIV_NEG2, {}, {eq});
  // resolve to (or (= q body) body) and (or (= q body) (not body))
  Node r1 = nm->mkNode(Kind::OR, eq, body);
  lcdp.addStep(r1,
               ProofRule::CHAIN_M_RESOLUTION,
               {cn1, c1},
               {r1, nm->mkNode(Kind::SEXPR, tt), nm->mkNode(Kind::SEXPR, q)});
  Node r2 = nm->mkNode(Kind::OR, eq, nbody);
  lcdp.addStep(r2,
               ProofRule::CHAIN_M_RESOLUTION,
               {cn2, c2},
               {r2, nm->mkNode(Kind::SEXPR, tt), nm->mkNode(Kind::SEXPR, nq)});
  // resolve to (= q body)
  lcdp.addStep(
      eq,
      ProofRule::CHAIN_M_RESOLUTION,
      {r1, r2},
      {eq, nm->mkNode(Kind::SEXPR, tt), nm->mkNode(Kind::SEXPR, body)});
  cdp->addProof(lcdp.getProofFor(eq));
}

void QuantifiersPreprocess::addTrans(CDProof* cdp,
                                     const Node& a,
                                     const Node& b,
                                     const Node& c) const
{
  if (a == b || b == c || a == c)
  {
    // already have a proof of (= a c), or it is not needed
    return;
  }
  cdp->addStep(a.eqNode(c), ProofRule::TRANS, {a.eqNode(b), b.eqNode(c)}, {});
}

TrustNode QuantifiersPreprocess::preprocess(Node n, bool isInst) const
{
  Node prev = n;
  std::unique_ptr<CDProof> cdp;
  if (d_epg != nullptr)
  {
    cdp.reset(new CDProof(d_env));
  }
  if (options().quantifiers.preSkolemQuant != options::PreSkolemQuantMode::OFF)
  {
    if (!isInst || !options().quantifiers.preSkolemQuantNested)
    {
      Trace("quantifiers-preprocess-debug")
          << "Pre-skolemize " << n << "..." << std::endl;
      // apply pre-skolemization to existential quantifiers
      std::vector<TNode> fvs;
      std::unordered_map<std::pair<Node, bool>, Node, NodePolPairHashFunction>
          visited;
      n = preSkolemizeQuantifiers(prev, true, fvs, visited, cdp.get());
    }
  }
  // pull all quantifiers globally
  if (options().quantifiers.prenexQuant == options::PrenexQuantMode::NORMAL)
  {
    Trace("quantifiers-prenex") << "Prenexing : " << n << std::endl;
    Node pn = n;
    std::map<Node, Node> visited;
    n = computePrenexAgg(n, visited);
    n = rewrite(n);
    // prenexing does not have proof support
    if (cdp != nullptr && n != pn)
    {
      cdp->addTrustedStep(
          pn.eqNode(n), TrustId::QUANTIFIERS_PREPROCESS, {}, {});
      addTrans(cdp.get(), prev, pn, n);
    }
    Trace("quantifiers-prenex") << "Prenexing returned : " << n << std::endl;
  }
  if (n != prev)
  {
    Trace("quantifiers-preprocess") << "Preprocess " << prev << std::endl;
    Trace("quantifiers-preprocess") << "..returned " << n << std::endl;
    if (cdp != nullptr)
    {
      std::shared_ptr<ProofNode> pf = cdp->getProofFor(prev.eqNode(n));
      return d_epg->mkTrustedRewrite(prev, n, pf);
    }
    return TrustNode::mkTrustRewrite(prev, n, nullptr);
  }
  return TrustNode::null();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

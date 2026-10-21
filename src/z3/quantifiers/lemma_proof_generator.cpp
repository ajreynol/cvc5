/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The proofs of the lemmas of the ported Z3 core.
 */

#include "z3/quantifiers/lemma_proof_generator.h"

#include "proof/lazy_proof.h"
#include "proof/proof.h"
#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "theory/inference_id.h"

namespace cvc5::internal {
namespace z3 {

LemmaProofGenerator::LemmaProofGenerator(Env& env) : EnvObj(env) {}

Node LemmaProofGenerator::mkInstance(TNode q, const std::vector<Node>& terms)
{
  Assert(q.getKind() == Kind::FORALL);
  Assert(q[0].getNumChildren() == terms.size());
  std::vector<Node> vars(q[0].begin(), q[0].end());
  Node body =
      q[1].substitute(vars.begin(), vars.end(), terms.begin(), terms.end());
  Node lem = NodeManager::mkNode(Kind::IMPLIES, q, body);
  if (d_env.isTheoryProofProducing())
  {
    d_terms.emplace(lem, terms);
  }
  return lem;
}

void LemmaProofGenerator::notifyPreprocessed(const Node& form,
                                             const TrustNode& trn,
                                             const TrustNode& pp)
{
  d_forms.emplace(form, std::make_pair(trn, pp));
}

TrustNode LemmaProofGenerator::getLemmaFor(const Node& form) const
{
  auto it = d_forms.find(form);
  return it == d_forms.end() ? TrustNode::null() : it->second.first;
}

Node LemmaProofGenerator::mkWeakened(const Node& form, const Node& d)
{
  if (d_env.isTheoryProofProducing() && d_forms.find(form) == d_forms.end())
  {
    return Node::null();
  }
  std::vector<Node> disj;
  if (form.getKind() == Kind::OR)
  {
    disj.insert(disj.end(), form.begin(), form.end());
  }
  else
  {
    disj.push_back(form);
  }
  disj.push_back(d.negate());
  Node w = nodeManager()->mkNode(Kind::OR, disj);
  if (d_env.isTheoryProofProducing())
  {
    d_weakened.emplace(w, std::make_pair(form, d));
  }
  return w;
}

std::shared_ptr<ProofNode> LemmaProofGenerator::getProofFor(Node f)
{
  if (d_terms.find(f) != d_terms.end())
  {
    return getInstanceProof(f);
  }
  auto it = d_weakened.find(f);
  Assert(it != d_weakened.end());
  const Node& form = it->second.first;
  const Node& d = it->second.second;
  //  form
  // ------------------ SCOPE
  // (=> d form)
  // ------------------ IMPLIES_ELIM
  // (or (not d) form)
  // ------------------ MACRO_SR_PRED_TRANSFORM
  // (or ~d l1 ... ln)
  //
  // where ~d is the negation of d, without a double negation
  // ------------------ REORDERING
  // (or l1 ... ln ~d)
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  std::vector<Node> assumps{d};
  std::shared_ptr<ProofNode> pfImp =
      pnm->mkScope(getFormProof(form), assumps, true, false);
  Node imp = pfImp->getResult();
  NodeManager* nm = nodeManager();
  Node elim = nm->mkNode(Kind::OR, d.notNode(), form);
  std::vector<Node> flat{d.negate()};
  if (form.getKind() == Kind::OR)
  {
    flat.insert(flat.end(), form.begin(), form.end());
  }
  else
  {
    flat.push_back(form);
  }
  Node flatn = nm->mkNode(Kind::OR, flat);
  CDProof cdp(d_env);
  cdp.addProof(pfImp);
  cdp.addStep(elim, ProofRule::IMPLIES_ELIM, {imp}, {});
  if (flatn != elim)
  {
    cdp.addStep(flatn, ProofRule::MACRO_SR_PRED_TRANSFORM, {elim}, {flatn});
  }
  cdp.addStep(f, ProofRule::REORDERING, {flatn}, {f});
  return cdp.getProofFor(f);
}

bool LemmaProofGenerator::hasProofFor(Node f)
{
  return d_terms.find(f) != d_terms.end()
         || d_weakened.find(f) != d_weakened.end();
}

std::shared_ptr<ProofNode> LemmaProofGenerator::getFormProof(const Node& form)
{
  auto it = d_forms.find(form);
  Assert(it != d_forms.end());
  const TrustNode& trn = it->second.first;
  const TrustNode& pp = it->second.second;
  //  lem   (= lem form)
  // ------------------- EQ_RESOLVE
  //  form
  LazyCDProof lcp(d_env);
  Node lem = trn.getProven();
  lcp.addLazyStep(lem, trn.getGenerator());
  if (!pp.isNull())
  {
    Node eq = pp.getProven();
    lcp.addLazyStep(eq, pp.getGenerator());
    lcp.addStep(form, ProofRule::EQ_RESOLVE, {lem, eq}, {});
  }
  return lcp.getProofFor(form);
}

std::shared_ptr<ProofNode> LemmaProofGenerator::getInstanceProof(
    const Node& f)
{
  auto it = d_terms.find(f);
  Assert(it != d_terms.end());
  // ... free assumption q ...
  // ------------------------- INSTANTIATE
  // body
  // ------------------------- SCOPE
  // (=> q body)
  Node q = f[0];
  Node body = f[1];
  NodeManager* nm = nodeManager();
  std::vector<Node> args{
      nm->mkNode(Kind::SEXPR, it->second),
      theory::mkInferenceIdNode(
          nm, theory::InferenceId::QUANTIFIERS_INST_Z3)};
  CDProof cdp(d_env);
  cdp.addStep(body, ProofRule::INSTANTIATE, {q}, args);
  std::vector<Node> assumps{q};
  return d_env.getProofNodeManager()->mkScope(cdp.getProofFor(body), assumps);
}

}  // namespace z3
}  // namespace cvc5::internal

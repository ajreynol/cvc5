/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The proofs of the lemmas of the eager E-matching core.
 *
 * Not ported from Z3: original cvc5 code.
 */

#include "theory/quantifiers/eager/lemma_proof_generator.h"

#include "expr/node_algorithm.h"
#include "proof/lazy_proof.h"
#include "proof/proof.h"
#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "theory/inference_id.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

LemmaProofGenerator::LemmaProofGenerator(Env& env)
    : EnvObj(env),
      d_forms(userContext()),
      d_hostForms(userContext()),
      d_weakened(userContext())
{
}

Node LemmaProofGenerator::mkInstance(TNode q, const std::vector<Node>& terms)
{
  // The instance is valid, whatever led the core to it, if it substitutes
  // closed terms of their types for the variables of q. This is what the
  // soundness of the lemmas the core sends rests on, so it is checked in
  // all builds.
  AlwaysAssert(q.getKind() == Kind::FORALL
               && q[0].getNumChildren() == terms.size());
  for (size_t i = 0, nterms = terms.size(); i < nterms; ++i)
  {
    TypeNode termType = terms[i].getType();
    TypeNode varType = q[0][i].getType();
    AlwaysAssert(termType == varType)
        << "ill-typed term " << terms[i] << " for " << q[0][i];
    AlwaysAssert(!expr::hasFreeVar(terms[i]))
        << "term " << terms[i] << " with a free variable for " << q[0][i];
  }
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

void LemmaProofGenerator::notifyPreprocessed(const Node& norm,
                                             const Node& form,
                                             const TrustNode& trn,
                                             const TrustNode& pp)
{
  // the first lemma preprocessed to form, and the first form of norm
  if (d_forms.find(form) == d_forms.end())
  {
    d_forms.insert(form, std::make_pair(trn, pp));
  }
  if (d_env.isTheoryProofProducing()
      && d_hostForms.find(norm) == d_hostForms.end())
  {
    d_hostForms.insert(norm, form);
  }
}

TrustNode LemmaProofGenerator::getLemmaFor(const Node& form) const
{
  auto it = d_forms.find(form);
  return it == d_forms.end() ? TrustNode::null() : it->second.first;
}

Node LemmaProofGenerator::getHostForm(const Node& norm) const
{
  auto it = d_hostForms.find(norm);
  return it == d_hostForms.end() ? Node::null() : it->second;
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
    d_weakened.insert(w, std::make_pair(form, d));
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

std::shared_ptr<ProofNode> LemmaProofGenerator::getInstanceProof(const Node& f)
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
          nm, theory::InferenceId::QUANTIFIERS_INST_EAGER_E_MATCHING)};
  CDProof cdp(d_env);
  cdp.addStep(body, ProofRule::INSTANTIATE, {q}, args);
  std::vector<Node> assumps{q};
  return d_env.getProofNodeManager()->mkScope(cdp.getProofFor(body), assumps);
}

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

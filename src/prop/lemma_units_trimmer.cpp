/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Trims lemmas based on unit facts asserted to the SAT solver.
 */

#include "prop/lemma_units_trimmer.h"

#include <algorithm>
#include <map>
#include <unordered_map>

#include "options/base_options.h"
#include "proof/lazy_proof.h"
#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"

namespace cvc5::internal {
namespace prop {

namespace {

/**
 * Return a proof of the conclusion of pn, where all free assumptions in subs
 * are replaced by their given proofs. This shares all subproofs of pn that do
 * not contain these assumptions.
 *
 * Moreover, if this substitution leads to a subproof of the form
 *   (MODUS_PONENS Q (SCOPE P :args (A_1 ... A_n))), or
 *   (CONTRA Q (SCOPE P :args (A_1 ... A_n)))
 * where Q proves each of the A_i, we recursively substitute the A_i in P,
 * which avoids the SCOPE.
 */
std::shared_ptr<ProofNode> substituteAssumptions(
    ProofNodeManager* pnm,
    std::shared_ptr<ProofNode> pn,
    const std::map<Node, std::shared_ptr<ProofNode>>& subs)
{
  std::unordered_map<ProofNode*, std::shared_ptr<ProofNode>> visited;
  std::unordered_map<ProofNode*, std::shared_ptr<ProofNode>>::iterator it;
  std::vector<std::shared_ptr<ProofNode>> visit;
  visit.push_back(pn);
  while (!visit.empty())
  {
    std::shared_ptr<ProofNode> cur = visit.back();
    it = visited.find(cur.get());
    if (it == visited.end())
    {
      if (cur->getRule() == ProofRule::ASSUME)
      {
        std::map<Node, std::shared_ptr<ProofNode>>::const_iterator its =
            subs.find(cur->getResult());
        visited[cur.get()] = its != subs.end() ? its->second : cur;
        visit.pop_back();
        continue;
      }
      if (cur->getRule() == ProofRule::SCOPE)
      {
        // The assumptions bound by this SCOPE are not substituted.
        const std::vector<Node>& sargs = cur->getArguments();
        std::map<Node, std::shared_ptr<ProofNode>> ssubs;
        for (const std::pair<const Node, std::shared_ptr<ProofNode>>& sp : subs)
        {
          if (std::find(sargs.begin(), sargs.end(), sp.first) == sargs.end())
          {
            ssubs.insert(sp);
          }
        }
        std::shared_ptr<ProofNode> body = cur->getChildren()[0];
        std::shared_ptr<ProofNode> sbody =
            ssubs.empty() ? body : substituteAssumptions(pnm, body, ssubs);
        visited[cur.get()] =
            sbody == body
                ? cur
                : pnm->mkNode(
                      ProofRule::SCOPE, {sbody}, sargs, cur->getResult());
        visit.pop_back();
        continue;
      }
      visited[cur.get()] = nullptr;
      const std::vector<std::shared_ptr<ProofNode>>& cs = cur->getChildren();
      visit.insert(visit.end(), cs.begin(), cs.end());
      continue;
    }
    visit.pop_back();
    if (it->second != nullptr)
    {
      continue;
    }
    bool childChanged = false;
    std::vector<std::shared_ptr<ProofNode>> children;
    for (const std::shared_ptr<ProofNode>& c : cur->getChildren())
    {
      Assert(visited.find(c.get()) != visited.end()
             && visited[c.get()] != nullptr);
      children.push_back(visited[c.get()]);
      childChanged = childChanged || children.back() != c;
    }
    ProofRule r = cur->getRule();
    if (childChanged && (r == ProofRule::MODUS_PONENS || r == ProofRule::CONTRA)
        && children[1]->getRule() == ProofRule::SCOPE)
    {
      // If we now have proofs of all assumptions of the SCOPE, i.e.
      //   (MODUS_PONENS Q (SCOPE P :args (A_1 ... A_n))), or
      //   (CONTRA Q (SCOPE P :args (A_1 ... A_n)))
      // where Q is (AND_INTRO Q_1 ... Q_n) and Q_i proves A_i, or Q proves A_1
      // if n=1, we substitute the Q_i into P, which avoids the SCOPE.
      const std::vector<Node>& sargs = children[1]->getArguments();
      std::map<Node, std::shared_ptr<ProofNode>> apfs;
      if (sargs.size() == 1)
      {
        apfs[children[0]->getResult()] = children[0];
      }
      else if (children[0]->getRule() == ProofRule::AND_INTRO)
      {
        for (const std::shared_ptr<ProofNode>& c : children[0]->getChildren())
        {
          apfs[c->getResult()] = c;
        }
      }
      std::map<Node, std::shared_ptr<ProofNode>> ssubs;
      for (const Node& a : sargs)
      {
        std::map<Node, std::shared_ptr<ProofNode>>::iterator ita = apfs.find(a);
        if (ita == apfs.end())
        {
          ssubs.clear();
          break;
        }
        ssubs[a] = ita->second;
      }
      if (!ssubs.empty())
      {
        std::shared_ptr<ProofNode> sbody =
            substituteAssumptions(pnm, children[1]->getChildren()[0], ssubs);
        if (sbody->getResult() == cur->getResult())
        {
          visited[cur.get()] = sbody;
          continue;
        }
      }
    }
    // Note that substituting assumptions does not change the conclusion.
    visited[cur.get()] = childChanged ? pnm->mkNode(cur->getRule(),
                                                    children,
                                                    cur->getArguments(),
                                                    cur->getResult())
                                      : cur;
  }
  Assert(visited[pn.get()] != nullptr);
  return visited[pn.get()];
}

}  // namespace

LemmaUnitsTrimmer::LemmaUnitsTrimmer(Env& env, LazyCDProof* cnfProof)
    : EnvObj(env),
      d_cnfProof(cnfProof),
      d_facts(userContext()),
      d_asserted(userContext()),
      d_trimmed(userContext())
{
}

void LemmaUnitsTrimmer::notifyUnitFact(const Node& lit)
{
  // In incremental mode, we only consider facts at user context level zero,
  // since lemmas may be kept by the SAT solver after the user context is
  // popped.
  if (!options().base.incrementalSolving || userContext()->getLevel() == 0)
  {
    Trace("lemma-units-trim") << "Unit fact: " << lit << std::endl;
    d_facts.insert(lit);
  }
}

void LemmaUnitsTrimmer::notifyAsserted(const Node& f) { d_asserted.insert(f); }

TrustNode LemmaUnitsTrimmer::trim(const TrustNode& trn)
{
  if (d_facts.empty() || trn.getGenerator() == nullptr)
  {
    return trn;
  }
  TrustNodeKind tnk = trn.getKind();
  Node proven = trn.getProven();
  // The antecedent and consequent of the lemma. We do not trim all
  // antecedents of conflicts or propagations, since the SAT solver requires
  // a non-unit clause for these.
  Node ante;
  Node conc;
  bool keepOne = true;
  switch (tnk)
  {
    case TrustNodeKind::CONFLICT: ante = trn.getNode(); break;
    case TrustNodeKind::PROP_EXP:
      ante = proven[0];
      conc = proven[1];
      break;
    case TrustNodeKind::LEMMA:
      if (proven.getKind() == Kind::NOT)
      {
        ante = proven[0];
      }
      else if (proven.getKind() == Kind::IMPLIES)
      {
        ante = proven[0];
        conc = proven[1];
        keepOne = false;
      }
      break;
    default: break;
  }
  if (ante.isNull() || (!conc.isNull() && conc.isConst()))
  {
    return trn;
  }
  std::shared_ptr<TrimInfo> ti = std::make_shared<TrimInfo>();
  if (ante.getKind() == Kind::AND)
  {
    ti->d_ante.insert(ti->d_ante.end(), ante.begin(), ante.end());
  }
  else
  {
    ti->d_ante.push_back(ante);
  }
  for (const Node& a : ti->d_ante)
  {
    if (d_facts.find(a) != d_facts.end())
    {
      ti->d_elim.push_back(a);
    }
    else
    {
      ti->d_remaining.push_back(a);
    }
  }
  if (keepOne && ti->d_remaining.empty() && !ti->d_elim.empty())
  {
    ti->d_remaining.push_back(ti->d_elim.back());
    ti->d_elim.pop_back();
  }
  if (ti->d_elim.empty())
  {
    Trace("lemma-units-trim-debug")
        << "No trim (" << tnk << ", " << ti->d_ante.size() << ") " << proven
        << std::endl;
    return trn;
  }
  ti->d_origProven = proven;
  ti->d_origGen = trn.getGenerator();
  ti->d_conc = conc;
  NodeManager* nm = nodeManager();
  Node nante =
      ti->d_remaining.empty() ? Node::null() : nm->mkAnd(ti->d_remaining);
  TrustNode ntrn;
  switch (tnk)
  {
    case TrustNodeKind::CONFLICT:
      ntrn = TrustNode::mkTrustConflict(nante, this);
      break;
    case TrustNodeKind::PROP_EXP:
      ntrn = TrustNode::mkTrustPropExp(conc, nante, this);
      break;
    default:
      ntrn = TrustNode::mkTrustLemma(
          conc.isNull()
              ? nante.notNode()
              : (nante.isNull() ? conc
                                : nm->mkNode(Kind::IMPLIES, nante, conc)),
          this);
      break;
  }
  Node nproven = ntrn.getProven();
  if (d_asserted.find(nproven) != d_asserted.end())
  {
    Trace("lemma-units-trim-debug")
        << "No trim, already asserted: " << nproven << std::endl;
    return trn;
  }
  Trace("lemma-units-trim")
      << "Trim (" << tnk << ", " << ti->d_elim.size() << "/"
      << ti->d_ante.size() << ") " << proven << std::endl
      << "  to " << nproven << std::endl;
  if (d_trimmed.find(nproven) == d_trimmed.end())
  {
    d_trimmed[nproven] = ti;
  }
  return ntrn;
}

std::shared_ptr<ProofNode> LemmaUnitsTrimmer::getProofFor(Node f)
{
  context::CDHashMap<Node, std::shared_ptr<TrimInfo>>::const_iterator it =
      d_trimmed.find(f);
  if (it == d_trimmed.end())
  {
    Assert(false) << "LemmaUnitsTrimmer: no proof for " << f;
    return nullptr;
  }
  const TrimInfo& ti = *it->second;
  std::shared_ptr<ProofNode> opf = ti.d_origGen->getProofFor(ti.d_origProven);
  if (opf == nullptr)
  {
    return nullptr;
  }
  if (TraceIsOn("lemma-units-trim-pf"))
  {
    Trace("lemma-units-trim-pf")
        << "Proof for " << f << std::endl
        << "  original " << ti.d_origProven << std::endl
        << "  ante " << ti.d_ante << ", elim " << ti.d_elim << std::endl
        << "  proof " << *opf.get() << std::endl;
  }
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  Node conc = ti.d_conc.isNull() ? nodeManager()->mkConst(false) : ti.d_conc;
  // Get the proof of the consequent of the lemma from its antecedents as
  // assumptions.
  std::shared_ptr<ProofNode> body;
  if (opf->getRule() == ProofRule::SCOPE
      && opf->getChildren()[0]->getResult() == conc)
  {
    // the common case, where the lemma is proven by SCOPE over its antecedents
    std::vector<Node> sargs = opf->getArguments();
    std::vector<Node> ante = ti.d_ante;
    std::sort(sargs.begin(), sargs.end());
    std::sort(ante.begin(), ante.end());
    if (sargs == ante)
    {
      body = opf->getChildren()[0];
    }
  }
  Trace("lemma-units-trim-path")
      << (body == nullptr ? "fallback " : "scope ") << opf->getRule()
      << std::endl;
  if (body == nullptr)
  {
    // otherwise, we use the antecedents to eliminate the antecedent of the
    // lemma.
    std::vector<std::shared_ptr<ProofNode>> apfs;
    for (const Node& a : ti.d_ante)
    {
      apfs.push_back(pnm->mkAssume(a));
    }
    Node ante = ti.d_origProven[0];
    std::shared_ptr<ProofNode> apf =
        apfs.size() == 1 ? apfs[0]
                         : pnm->mkNode(ProofRule::AND_INTRO, apfs, {}, ante);
    body = ti.d_conc.isNull()
               ? pnm->mkNode(ProofRule::CONTRA, {apf, opf}, {}, conc)
               : pnm->mkNode(ProofRule::MODUS_PONENS, {apf, opf}, {}, conc);
  }
  // replace the eliminated antecedents by the proofs of the unit facts
  std::map<Node, std::shared_ptr<ProofNode>> subs;
  for (const Node& e : ti.d_elim)
  {
    subs[e] = d_cnfProof->getProofFor(e);
  }
  body = substituteAssumptions(pnm, body, subs);
  return mkScope(body, ti.d_remaining, f);
}

std::shared_ptr<ProofNode> LemmaUnitsTrimmer::mkScope(
    std::shared_ptr<ProofNode> body,
    const std::vector<Node>& assumps,
    const Node& expected)
{
  if (assumps.empty())
  {
    Assert(body->getResult() == expected);
    return body;
  }
  return d_env.getProofNodeManager()->mkNode(
      ProofRule::SCOPE, {body}, assumps, expected);
}

std::string LemmaUnitsTrimmer::identify() const { return "LemmaUnitsTrimmer"; }

}  // namespace prop
}  // namespace cvc5::internal

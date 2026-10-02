/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the module for processing proof nodes in the prop engine.
 */

#include "prop/proof_post_processor.h"

#include <algorithm>
#include <map>
#include <unordered_map>
#include <unordered_set>

#include "options/proof_options.h"
#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "theory/builtin/proof_checker.h"

namespace cvc5::internal {
namespace prop {

ProofPostprocessCallback::ProofPostprocessCallback(
    Env& env, ProofGenerator* proofCnfStream)
    : EnvObj(env), d_pg(proofCnfStream), d_blocked(userContext())
{
}

void ProofPostprocessCallback::initializeUpdate() { d_assumpToProof.clear(); }

bool ProofPostprocessCallback::shouldUpdate(
    std::shared_ptr<ProofNode> pn,
    CVC5_UNUSED const std::vector<Node>& fa,
    bool& continueUpdate)
{
  bool result =
      pn->getRule() == ProofRule::ASSUME && d_pg->hasProofFor(pn->getResult());
  if (TraceIsOn("prop-proof-pp") && !result
      && pn->getRule() == ProofRule::ASSUME)
  {
    Trace("prop-proof-pp") << "- Ignoring no-proof assumption "
                           << pn->getResult() << "\n";
  }
  // check if should continue traversing
  if (isBlocked(pn))
  {
    continueUpdate = false;
    result = false;
  }
  return result;
}

bool ProofPostprocessCallback::update(Node res,
                                      ProofRule id,
                                      const std::vector<Node>& children,
                                      const std::vector<Node>& args,
                                      CDProof* cdp,
                                      bool& continueUpdate)
{
  Trace("prop-proof-pp") << "- Post process " << id << " " << res << " : "
                         << children << " / " << args << "\n"
                         << push;
  Assert(id == ProofRule::ASSUME);
  // we cache based on the assumption node, not the proof node, since there
  // may be multiple occurrences of the same node.
  Node f = args[0];
  std::shared_ptr<ProofNode> pfn;
  std::map<Node, std::shared_ptr<ProofNode>>::iterator it =
      d_assumpToProof.find(f);
  if (it != d_assumpToProof.end())
  {
    Trace("prop-proof-pp") << "...already computed" << std::endl;
    pfn = it->second;
  }
  else
  {
    Assert(d_pg != nullptr);
    // get proof from proof cnf stream
    pfn = d_pg->getProofFor(f);
    Assert(pfn != nullptr && pfn->getResult() == f);
    if (TraceIsOn("prop-proof-pp"))
    {
      Trace("prop-proof-pp") << "=== Connect CNF proof for: " << f << "\n";
      Trace("prop-proof-pp") << *pfn.get() << "\n";
    }
    d_assumpToProof[f] = pfn;
  }
  Trace("prop-proof-pp") << pop;
  // connect the proof
  cdp->addProof(pfn);
  // do not recursively process the result
  continueUpdate = false;
  // moreover block the fact f so that its proof node is not traversed if we run
  // this post processor again (which can happen in incremental benchmarks)
  addBlocked(pfn);
  return true;
}

void ProofPostprocessCallback::addBlocked(std::shared_ptr<ProofNode> pfn)
{
  d_blocked.insert(pfn);
}

bool ProofPostprocessCallback::isBlocked(std::shared_ptr<ProofNode> pfn)
{
  return d_blocked.contains(pfn);
}

ProofPostprocess::ProofPostprocess(Env& env, ProofGenerator* pg)
    : EnvObj(env), d_cb(env, pg)
{
}

ProofPostprocess::~ProofPostprocess() {}

void ProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  // Initialize the callback, which computes necessary static information about
  // how to process, including how to process assumptions in pf.
  d_cb.initializeUpdate();
  // now, process
  ProofNodeUpdater updater(d_env, d_cb);
  updater.process(pf);
  if (options().proof.proofPpLemmaUnits)
  {
    shortenLemmasWithUnits(pf);
  }
}

namespace {

/**
 * Return a proof of the conclusion of pn, where all assumptions in subs are
 * replaced by their given proofs. This shares all subproofs of pn that do not
 * contain these assumptions. Returns nullptr if an assumption in subs occurs
 * free within a SCOPE in pn.
 *
 * Moreover, if this substitution leads to a subproof of the form
 *   (MODUS_PONENS Q (SCOPE P :args (A_1 ... A_n)))
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
        // The assumptions bound by this SCOPE are not substituted. We do not
        // substitute other assumptions into nested SCOPEs, since the proofs
        // we substitute would then be local to that SCOPE, which makes them
        // harder to share, e.g. when printing proofs.
        const std::vector<Node>& sargs = cur->getArguments();
        std::map<Node, std::shared_ptr<ProofNode>> ssubs;
        for (const std::pair<const Node, std::shared_ptr<ProofNode>>& sp : subs)
        {
          if (std::find(sargs.begin(), sargs.end(), sp.first) == sargs.end())
          {
            ssubs.insert(sp);
          }
        }
        if (!ssubs.empty()
            && substituteAssumptions(pnm, cur->getChildren()[0], ssubs)
                   != cur->getChildren()[0])
        {
          return nullptr;
        }
        visited[cur.get()] = cur;
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
    if (childChanged && cur->getRule() == ProofRule::MODUS_PONENS
        && children[1]->getRule() == ProofRule::SCOPE)
    {
      // If we now have proofs of all assumptions of the SCOPE, i.e.
      //   (MODUS_PONENS Q (SCOPE P :args (A_1 ... A_n)))
      // where Q is (AND_INTRO Q_1 ... Q_n) and Q_i proves A_i, or Q proves A_1
      // if n=1, we substitute the Q_i into P, which avoids the SCOPE.
      const std::vector<Node>& sargs = children[1]->getArguments();
      std::vector<std::shared_ptr<ProofNode>> spfs;
      if (sargs.size() == 1)
      {
        spfs.push_back(children[0]);
      }
      else if (children[0]->getRule() == ProofRule::AND_INTRO)
      {
        spfs = children[0]->getChildren();
      }
      std::map<Node, std::shared_ptr<ProofNode>> ssubs;
      if (spfs.size() == sargs.size())
      {
        for (size_t i = 0, nargs = sargs.size(); i < nargs; i++)
        {
          if (spfs[i]->getResult() != sargs[i])
          {
            ssubs.clear();
            break;
          }
          ssubs[sargs[i]] = spfs[i];
        }
      }
      if (!ssubs.empty())
      {
        std::shared_ptr<ProofNode> sbody =
            substituteAssumptions(pnm, children[1]->getChildren()[0], ssubs);
        if (sbody != nullptr && sbody->getResult() == cur->getResult())
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

void ProofPostprocess::shortenLemmasWithUnits(std::shared_ptr<ProofNode> pf)
{
  if (d_env.getProofNodeManager()->getChecker() == nullptr)
  {
    return;
  }
  // Post-order traversal of the propositional proof, which does not traverse
  // into the (blocked) proofs that were connected to it.
  std::unordered_set<ProofNode*> visited;
  std::vector<std::pair<std::shared_ptr<ProofNode>, bool>> visit;
  visit.emplace_back(pf, false);
  while (!visit.empty())
  {
    std::shared_ptr<ProofNode> cur = visit.back().first;
    bool postVisit = visit.back().second;
    visit.pop_back();
    if (postVisit)
    {
      ProofRule r = cur->getRule();
      if (r == ProofRule::CHAIN_RESOLUTION
          || r == ProofRule::CHAIN_M_RESOLUTION)
      {
        shortenLemmasWithUnitsStep(cur.get());
      }
      continue;
    }
    if (!visited.insert(cur.get()).second || d_cb.isBlocked(cur))
    {
      continue;
    }
    visit.emplace_back(cur, true);
    for (const std::shared_ptr<ProofNode>& c : cur->getChildren())
    {
      visit.emplace_back(c, false);
    }
  }
}

bool ProofPostprocess::shortenLemmasWithUnitsStep(ProofNode* pn)
{
  ProofRule r = pn->getRule();
  std::vector<std::shared_ptr<ProofNode>> children = pn->getChildren();
  // copy, since pn is updated below
  std::vector<Node> args = pn->getArguments();
  size_t start = r == ProofRule::CHAIN_M_RESOLUTION ? 1 : 0;
  if (children.size() < 2 || args.size() != start + 2
      || args[start].getKind() != Kind::SEXPR
      || args[start + 1].getKind() != Kind::SEXPR
      || args[start].getNumChildren() + 1 != children.size()
      || args[start + 1].getNumChildren() + 1 != children.size())
  {
    return false;
  }
  std::vector<Node> pols(args[start].begin(), args[start].end());
  std::vector<Node> pivs(args[start + 1].begin(), args[start + 1].end());
  Node res = pn->getResult();
  Trace("prop-pf-lemma-units") << "Process " << r << " with " << children.size()
                               << " premises" << std::endl;
  // We remember the proofs of units even after they are removed from the
  // resolution, so that they can be used for multiple lemmas.
  std::map<Node, std::shared_ptr<ProofNode>> units;
  for (size_t i = 0, nchild = children.size(); i < nchild; i++)
  {
    Node lit = getEliminatedLiteral(pols, pivs, i);
    if (children[i]->getResult() == lit)
    {
      // only use the first unit for each literal
      units.emplace(lit, children[i]);
    }
  }
  if (units.empty())
  {
    return false;
  }
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  NodeManager* nm = nodeManager();
  bool changed = false;
  for (size_t i = 0; i < children.size(); i++)
  {
    // the clause must be a disjunction of the negated assumptions of a SCOPE
    // and possibly its conclusion
    Node clause = children[i]->getResult();
    if (clause.getKind() != Kind::OR)
    {
      continue;
    }
    std::shared_ptr<ProofNode> scope = findLemmaScope(children[i]);
    if (scope == nullptr)
    {
      continue;
    }
    // All assumptions must be proven by units. We do not handle the case
    // where only some are, since this would require a SCOPE over the
    // remaining assumptions, which would contain the proofs of the units. This
    // makes proofs harder to share, and leads to larger proofs in practice.
    std::map<Node, std::shared_ptr<ProofNode>> subs;
    for (const Node& a : scope->getArguments())
    {
      std::map<Node, std::shared_ptr<ProofNode>>::iterator itu = units.find(a);
      // the unit must not be the lemma itself
      if (itu == units.end() || itu->second == children[i])
      {
        subs.clear();
        break;
      }
      subs[a] = itu->second;
    }
    if (subs.empty())
    {
      continue;
    }
    // the literals we expect for the new clause
    std::vector<Node> nlits(clause.begin(), clause.end());
    bool litsValid = true;
    for (const std::pair<const Node, std::shared_ptr<ProofNode>>& sa : subs)
    {
      std::vector<Node>::iterator itl =
          std::find(nlits.begin(), nlits.end(), sa.first.notNode());
      if (itl == nlits.end())
      {
        litsValid = false;
        break;
      }
      nlits.erase(itl);
    }
    if (!litsValid)
    {
      continue;
    }
    Trace("prop-pf-lemma-units")
        << "...premise #" << i << " is a lemma whose " << subs.size()
        << " assumptions are proven by units" << std::endl;
    std::shared_ptr<ProofNode> lemPf =
        substituteAssumptions(pnm, scope->getChildren()[0], subs);
    if (lemPf == nullptr)
    {
      Trace("prop-pf-lemma-units")
          << "...assumption occurs in nested SCOPE" << std::endl;
      continue;
    }
    // The negated assumptions that occur in other premises. The units for
    // these must be kept to eliminate them.
    std::unordered_set<Node> neededLits;
    for (size_t j = 0, nchild = children.size(); j < nchild; j++)
    {
      Node cj = children[j]->getResult();
      if (j == i || subs.find(cj) != subs.end())
      {
        continue;
      }
      if (cj.getKind() == Kind::OR)
      {
        neededLits.insert(cj.begin(), cj.end());
      }
      neededLits.insert(cj);
    }
    // Construct the new resolution step, where the units are removed and the
    // lemma is replaced. Removing the i^th premise for i > 0 removes the
    // (i-1)^th pivot, removing the first removes the first pivot.
    std::vector<std::shared_ptr<ProofNode>> nchildren;
    std::vector<Node> npols;
    std::vector<Node> npivs;
    size_t ni = 0;
    for (size_t j = 0, nchild = children.size(); j < nchild; j++)
    {
      // remove the units we used, unless they are needed
      if (j != i)
      {
        Node cj = children[j]->getResult();
        std::map<Node, std::shared_ptr<ProofNode>>::iterator its =
            subs.find(cj);
        if (its != subs.end() && its->second == children[j]
            && neededLits.find(cj.notNode()) == neededLits.end())
        {
          continue;
        }
      }
      if (j == i)
      {
        ni = nchildren.size();
      }
      // the pivot used to resolve the j^th premise, which is dropped if this
      // is the first remaining premise
      if (!nchildren.empty())
      {
        npols.push_back(pols[j - 1]);
        npivs.push_back(pivs[j - 1]);
      }
      nchildren.push_back(j == i ? lemPf : children[j]);
    }
    std::shared_ptr<ProofNode> npn;
    Node nclause = lemPf->getResult();
    if (nchildren.size() == 1)
    {
      if (nclause == res)
      {
        npn = lemPf;
      }
    }
    else if (nlits.size() == 1)
    {
      // Check that the new clause is a unit that is eliminated in this step.
      // This ensures that it is interpreted as a clause in the same way as
      // the original, which is required e.g. by the CPC proof checker.
      if (nclause == nlits[0]
          && nclause == getEliminatedLiteral(npols, npivs, ni))
      {
        std::vector<Node> nargs;
        if (start == 1)
        {
          nargs.push_back(args[0]);
        }
        nargs.push_back(nm->mkNode(Kind::SEXPR, npols));
        nargs.push_back(nm->mkNode(Kind::SEXPR, npivs));
        npn = mkCheckedNode(r, nchildren, nargs, res);
      }
    }
    if (npn == nullptr)
    {
      Trace("prop-pf-lemma-units")
          << "...failed to construct resolution step" << std::endl;
      continue;
    }
    Trace("prop-pf-lemma-units")
        << "...success, now " << nchildren.size() << " premises" << std::endl;
    changed = true;
    pnm->updateNode(pn, npn.get());
    if (nchildren.size() == 1)
    {
      return true;
    }
    children = nchildren;
    pols = npols;
    pivs = npivs;
    // continue with the premise after the lemma
    i = ni;
  }
  return changed;
}

Node ProofPostprocess::getEliminatedLiteral(const std::vector<Node>& pols,
                                            const std::vector<Node>& pivs,
                                            size_t i)
{
  // The first premise (i = 0) is resolved against the second on the first
  // pivot, where the polarity is relative to the first premise.
  size_t pi = i == 0 ? 0 : i - 1;
  bool pivInPrem = pols[pi].getConst<bool>() == (i == 0);
  return pivInPrem ? pivs[pi] : pivs[pi].notNode();
}

std::shared_ptr<ProofNode> ProofPostprocess::findLemmaScope(
    std::shared_ptr<ProofNode> pn)
{
  while (pn != nullptr)
  {
    switch (pn->getRule())
    {
      case ProofRule::SCOPE: return pn;
      case ProofRule::REORDERING:
      case ProofRule::FACTORING:
      case ProofRule::IMPLIES_ELIM:
      case ProofRule::NOT_AND: pn = pn->getChildren()[0]; break;
      case ProofRule::RESOLUTION:
      case ProofRule::CHAIN_RESOLUTION:
      case ProofRule::CHAIN_M_RESOLUTION:
      {
        // all premises but one must be tautologies, e.g. CNF_AND_NEG
        std::shared_ptr<ProofNode> next;
        for (const std::shared_ptr<ProofNode>& c : pn->getChildren())
        {
          if (c->getRule() != ProofRule::ASSUME && c->getChildren().empty())
          {
            continue;
          }
          if (next != nullptr)
          {
            return nullptr;
          }
          next = c;
        }
        pn = next;
      }
      break;
      default: return nullptr;
    }
  }
  return nullptr;
}

std::shared_ptr<ProofNode> ProofPostprocess::mkCheckedNode(
    ProofRule id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args,
    Node expected)
{
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  std::vector<Node> cconcs;
  for (const std::shared_ptr<ProofNode>& c : children)
  {
    cconcs.push_back(c->getResult());
  }
  // Note we do not pass expected to the checker, since it would be trusted
  // when proof checking is disabled.
  Node res = pnm->getChecker()->checkDebug(
      id, cconcs, args, Node::null(), "prop-pf-lemma-units");
  if (res.isNull() || (!expected.isNull() && res != expected))
  {
    return nullptr;
  }
  return pnm->mkNode(id, children, args, res);
}

}  // namespace prop
}  // namespace cvc5::internal

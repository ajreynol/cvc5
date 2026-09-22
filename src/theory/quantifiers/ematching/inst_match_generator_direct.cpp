/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Direct inst match generator for nested single triggers.
 */

#include "theory/quantifiers/ematching/inst_match_generator_direct.h"

#include "theory/quantifiers/ematching/trigger_term_info.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_util.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/equality_engine_iterator.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

namespace {

bool isSupportedAtomicKind(Kind k)
{
  return k != Kind::APPLY_CONSTRUCTOR && k != Kind::APPLY_SELECTOR
         && k != Kind::APPLY_TESTER && k != Kind::HO_APPLY;
}

}  // namespace

InstMatchGeneratorDirect::InstMatchGeneratorDirect(Env& env,
                                                   Trigger* tparent,
                                                   Node q,
                                                   Node pat)
    : IMGenerator(env, tparent),
      d_quant(q),
      d_pattern(pat),
      d_root(compile(pat))
{
  Assert(isApplicable(q, pat));
}

bool InstMatchGeneratorDirect::CandidateKey::operator<(
    const CandidateKey& other) const
{
  if (d_eqc != other.d_eqc)
  {
    return d_eqc < other.d_eqc;
  }
  return d_op < other.d_op;
}

bool InstMatchGeneratorDirect::SubMatchKey::operator<(
    const SubMatchKey& other) const
{
  if (d_pattern != other.d_pattern)
  {
    return d_pattern < other.d_pattern;
  }
  return d_eqc < other.d_eqc;
}

bool InstMatchGeneratorDirect::isApplicable(Node q, Node pat)
{
  if (pat.getKind() == Kind::NOT || pat.getKind() == Kind::EQUAL
      || pat.getKind() == Kind::GEQ)
  {
    return false;
  }
  if (TriggerTermInfo::isSimpleTrigger(pat))
  {
    return false;
  }
  return isApplicableInternal(q, pat, true);
}

bool InstMatchGeneratorDirect::isApplicableInternal(Node q,
                                                    Node pat,
                                                    bool isRoot)
{
  if (!TermUtil::hasInstConstAttr(pat))
  {
    return true;
  }
  if (pat.getKind() == Kind::INST_CONSTANT)
  {
    return !isRoot && TermUtil::getInstConstAttr(pat) == q;
  }
  if (!TriggerTermInfo::isAtomicTrigger(pat)
      || !isSupportedAtomicKind(pat.getKind()))
  {
    return false;
  }
  for (const Node& child : pat)
  {
    if (!isApplicableInternal(q, child, false))
    {
      return false;
    }
  }
  return true;
}

std::unique_ptr<InstMatchGeneratorDirect::PatternNode>
InstMatchGeneratorDirect::compile(Node pat) const
{
  if (!TermUtil::hasInstConstAttr(pat))
  {
    return std::make_unique<PatternNode>(pat, PatternKind::GROUND);
  }
  if (pat.getKind() == Kind::INST_CONSTANT)
  {
    auto p = std::make_unique<PatternNode>(pat, PatternKind::VARIABLE);
    p->d_varNum = pat.getAttribute(InstVarNumAttribute());
    return p;
  }
  auto p = std::make_unique<PatternNode>(pat, PatternKind::APP);
  p->d_op = d_treg.getTermDatabase()->getMatchOperator(pat);
  Assert(!p->d_op.isNull());
  for (const Node& child : pat)
  {
    p->d_children.push_back(compile(child));
  }
  return p;
}

Node InstMatchGeneratorDirect::getEqcKey(Node n) const
{
  if (n.isNull())
  {
    return Node::null();
  }
  return d_qstate.hasTerm(n) ? Node(d_qstate.getRepresentative(n)) : n;
}

bool InstMatchGeneratorDirect::isGoodCandidate(TNode n,
                                               bool requireCurrent) const
{
  TermDb* tdb = d_treg.getTermDatabase();
  if (!tdb->isTermActive(n))
  {
    return false;
  }
  return !requireCurrent || tdb->hasTermCurrent(n);
}

const std::vector<Node>& InstMatchGeneratorDirect::getCandidates(Node eqc,
                                                                 Node op)
{
  CandidateKey key{getEqcKey(eqc), op};
  auto it = d_candidateCache.find(key);
  if (it != d_candidateCache.end())
  {
    return it->second;
  }
  std::vector<Node>& out = d_candidateCache[key];
  TermDb* tdb = d_treg.getTermDatabase();
  if (key.d_eqc.isNull())
  {
    DbList* dbl = tdb->getGroundTermList(op);
    if (dbl == nullptr)
    {
      return out;
    }
    for (const Node& n : dbl->d_list)
    {
      if (isGoodCandidate(n, true))
      {
        out.push_back(n);
      }
    }
    return out;
  }
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  if (ee->hasTerm(key.d_eqc))
  {
    eq::EqClassIterator iteq(key.d_eqc, ee);
    while (!iteq.isFinished())
    {
      Node n = *iteq;
      ++iteq;
      if (tdb->getMatchOperator(n) == op && isGoodCandidate(n, false))
      {
        out.push_back(n);
      }
    }
    return out;
  }
  if (tdb->getMatchOperator(key.d_eqc) == op
      && isGoodCandidate(key.d_eqc, false))
  {
    out.push_back(key.d_eqc);
  }
  return out;
}

std::vector<InstMatchGeneratorDirect::MatchResult>
InstMatchGeneratorDirect::computeSubMatches(const PatternNode& pat, Node target)
{
  std::vector<MatchResult> out;
  size_t numVars = d_quant[0].getNumChildren();
  if (pat.d_kind == PatternKind::VARIABLE)
  {
    MatchResult mr;
    mr.d_vals.resize(numVars);
    mr.d_vals[pat.d_varNum] = target;
    mr.d_matched = target;
    out.push_back(std::move(mr));
    return out;
  }
  if (pat.d_kind == PatternKind::GROUND)
  {
    if (d_qstate.areEqual(pat.d_pattern, target))
    {
      MatchResult mr;
      mr.d_vals.resize(numVars);
      mr.d_matched = target;
      out.push_back(std::move(mr));
    }
    return out;
  }
  const std::vector<Node>& cands = getCandidates(target, pat.d_op);
  for (const Node& cand : cands)
  {
    addApplicationMatches(pat, cand, out);
  }
  return out;
}

const std::vector<InstMatchGeneratorDirect::MatchResult>&
InstMatchGeneratorDirect::getSubMatches(const PatternNode& pat, Node target)
{
  Assert(pat.d_kind == PatternKind::APP);
  SubMatchKey key{pat.d_pattern, getEqcKey(target)};
  auto it = d_subMatchCache.find(key);
  if (it != d_subMatchCache.end())
  {
    return it->second;
  }
  std::vector<MatchResult>& out = d_subMatchCache[key];
  out = computeSubMatches(pat, target);
  return out;
}

void InstMatchGeneratorDirect::addApplicationMatches(
    const PatternNode& pat, TNode cand, std::vector<MatchResult>& out)
{
  std::vector<Node> current(d_quant[0].getNumChildren());
  combineChildMatches(pat, cand, 0, current, out);
}

void InstMatchGeneratorDirect::combineChildMatches(
    const PatternNode& pat,
    TNode cand,
    size_t index,
    std::vector<Node>& current,
    std::vector<MatchResult>& out)
{
  if (index == pat.d_children.size())
  {
    MatchResult mr;
    mr.d_vals = current;
    mr.d_matched = cand;
    out.push_back(std::move(mr));
    return;
  }
  const PatternNode& child = *pat.d_children[index];
  std::vector<MatchResult> local;
  const std::vector<MatchResult>* childMatches;
  if (child.d_kind == PatternKind::APP)
  {
    childMatches = &getSubMatches(child, cand[index]);
  }
  else
  {
    local = computeSubMatches(child, cand[index]);
    childMatches = &local;
  }
  for (const MatchResult& cm : *childMatches)
  {
    std::vector<size_t> touched;
    if (mergeMatch(current, cm.d_vals, touched))
    {
      combineChildMatches(pat, cand, index + 1, current, out);
    }
    undoMerge(current, touched);
  }
}

bool InstMatchGeneratorDirect::mergeMatch(std::vector<Node>& current,
                                          const std::vector<Node>& delta,
                                          std::vector<size_t>& touched) const
{
  for (size_t i = 0, size = delta.size(); i < size; i++)
  {
    if (delta[i].isNull())
    {
      continue;
    }
    if (current[i].isNull())
    {
      current[i] = delta[i];
      touched.push_back(i);
      continue;
    }
    if (!d_qstate.areEqual(current[i], delta[i]))
    {
      return false;
    }
  }
  return true;
}

void InstMatchGeneratorDirect::undoMerge(std::vector<Node>& current,
                                         const std::vector<size_t>& touched) const
{
  for (size_t i : touched)
  {
    current[i] = Node::null();
  }
}

bool InstMatchGeneratorDirect::restoreFromPrefix(
    const std::vector<Node>& prefix,
    const std::vector<Node>& vals,
    InstMatch& m) const
{
  m.resetAll();
  for (size_t i = 0, size = prefix.size(); i < size; i++)
  {
    if (!prefix[i].isNull() && !m.set(i, prefix[i]))
    {
      return false;
    }
  }
  for (size_t i = 0, size = vals.size(); i < size; i++)
  {
    if (!vals[i].isNull() && !m.set(i, vals[i]))
    {
      return false;
    }
  }
  return !d_qstate.isInConflict();
}

bool InstMatchGeneratorDirect::advanceToNextRoot()
{
  d_rootMatches.clear();
  d_rootMatchIndex = 0;
  while (d_rootIndex < d_rootCandidates.size())
  {
    Node cand = d_rootCandidates[d_rootIndex];
    d_rootIndex++;
    if (d_excludedMatches.find(cand) != d_excludedMatches.end())
    {
      continue;
    }
    d_currMatched = cand;
    addApplicationMatches(*d_root, cand, d_rootMatches);
    if (!d_rootMatches.empty())
    {
      return true;
    }
    if (d_independentGen)
    {
      d_excludedMatches[cand] = true;
    }
  }
  d_currMatched = Node::null();
  return false;
}

void InstMatchGeneratorDirect::resetInstantiationRound()
{
  d_needsReset = true;
  d_eqc = Node::null();
  d_currMatched = Node::null();
  d_rootCandidates.clear();
  d_rootMatches.clear();
  d_rootIndex = 0;
  d_rootMatchIndex = 0;
  d_candidateCache.clear();
  d_subMatchCache.clear();
  d_excludedMatches.clear();
}

bool InstMatchGeneratorDirect::reset(Node eqc)
{
  d_eqc = getEqcKey(eqc);
  d_rootCandidates = getCandidates(d_eqc, d_root->d_op);
  d_rootIndex = 0;
  d_rootMatches.clear();
  d_rootMatchIndex = 0;
  d_currMatched = Node::null();
  d_needsReset = false;
  for (const Node& cand : d_rootCandidates)
  {
    if (d_excludedMatches.find(cand) == d_excludedMatches.end())
    {
      return true;
    }
  }
  return false;
}

int InstMatchGeneratorDirect::getNextMatch(InstMatch& m)
{
  const std::vector<Node> prefix = m.get();
  if (d_needsReset && !reset(d_eqc))
  {
    bool restored = restoreFromPrefix(prefix, std::vector<Node>(), m);
    AlwaysAssert(restored) << "Failed to restore prefix for direct E-matching";
    return -1;
  }
  while (true)
  {
    if (d_currMatched.isNull() && !advanceToNextRoot())
    {
      bool restored = restoreFromPrefix(prefix, std::vector<Node>(), m);
      AlwaysAssert(restored) << "Failed to restore prefix for direct E-matching";
      return -1;
    }
    while (d_rootMatchIndex < d_rootMatches.size())
    {
      const std::vector<Node>& vals = d_rootMatches[d_rootMatchIndex].d_vals;
      d_rootMatchIndex++;
      if (!restoreFromPrefix(prefix, vals, m))
      {
        if (d_qstate.isInConflict())
        {
          return -1;
        }
        continue;
      }
      if (!d_activeAdd)
      {
        return 1;
      }
      std::vector<Node> terms = m.get();
      if (sendInstantiation(terms))
      {
        d_currMatched = Node::null();
        d_rootMatches.clear();
        d_rootMatchIndex = 0;
        return 1;
      }
      if (d_qstate.isInConflict())
      {
        return -1;
      }
    }
    d_currMatched = Node::null();
    d_rootMatches.clear();
    d_rootMatchIndex = 0;
  }
}

uint64_t InstMatchGeneratorDirect::addInstantiations(InstMatch& m)
{
  uint64_t addedLemmas = 0;
  m.resetAll();
  while (getNextMatch(m) > 0)
  {
    if (!d_activeAdd)
    {
      std::vector<Node> terms = m.get();
      if (sendInstantiation(terms))
      {
        addedLemmas++;
      }
    }
    else
    {
      addedLemmas++;
    }
    if (d_qstate.isInConflict())
    {
      break;
    }
    m.resetAll();
  }
  return addedLemmas;
}

int InstMatchGeneratorDirect::getActiveScore()
{
  TermDb* tdb = d_treg.getTermDatabase();
  return static_cast<int>(tdb->getNumGroundTerms(d_root->d_op));
}

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

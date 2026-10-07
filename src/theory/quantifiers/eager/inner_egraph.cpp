/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The congruence closure of the inner SMT solver.
 */

#include "theory/quantifiers/eager/inner_egraph.h"

#include <algorithm>
#include <ostream>
#include <set>
#include <unordered_set>

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

InnerEGraph::InnerEGraph(Env& env) : EnvObj(env), d_listener(nullptr) {}

InnerEGraph::~InnerEGraph() {}

InnerEGraph::TermId InnerEGraph::getTerm(TNode n) const
{
  std::map<Node, TermId>::const_iterator it = d_termMap.find(n);
  return it == d_termMap.end() ? undefinedTerm : it->second;
}

InnerEGraph::TermId InnerEGraph::find(TermId a) const
{
  while (d_terms[a].d_find != a)
  {
    a = d_terms[a].d_find;
  }
  return a;
}

InnerEGraph::TermId InnerEGraph::addTerm(TNode n)
{
  TermId t = getTerm(n);
  if (t != undefinedTerm)
  {
    return t;
  }
  std::vector<TermId> args;
  for (const Node& nc : n)
  {
    args.push_back(addTerm(nc));
  }
  t = d_terms.size();
  Term term;
  term.d_node = n;
  term.d_label = n.hasOperator() ? n.getOperator() : Node::null();
  term.d_isBool = n.getType().isBoolean();
  term.d_args = args;
  term.d_find = t;
  term.d_next = t;
  term.d_classSize = 1;
  term.d_cgOwner = false;
  term.d_pfParent = undefinedTerm;
  term.d_pfCongruence = false;
  d_terms.push_back(term);
  d_termMap[n] = t;
  d_undo.push_back(UndoEntry(UndoEntry::Kind::ADD_TERM, t));
  if (!args.empty())
  {
    for (TermId a : args)
    {
      TermId r = find(a);
      d_terms[r].d_parents.push_back(t);
      d_undo.push_back(UndoEntry(UndoEntry::Kind::PARENTS,
                                 r,
                                 undefinedTerm,
                                 d_terms[r].d_parents.size() - 1));
    }
    // register in the congruence table, merging with the existing application
    // of the same label to the same classes if there is one
    CgKey key = mkCgKey(t);
    std::map<CgKey, TermId>::iterator itc = d_cg.find(key);
    if (itc == d_cg.end())
    {
      cgInsert(t, key);
    }
    else if (!areEqual(t, itc->second))
    {
      // a congruence, justified by the congruence of the arguments
      assertEqInternal(t, itc->second, Node::null(), true);
    }
  }
  return t;
}

InnerEGraph::CgKey InnerEGraph::mkCgKey(TermId t) const
{
  std::vector<TermId> roots;
  roots.reserve(d_terms[t].d_args.size());
  for (TermId a : d_terms[t].d_args)
  {
    roots.push_back(find(a));
  }
  return CgKey(d_terms[t].d_label, roots);
}

bool InnerEGraph::assertEq(TermId a, TermId b, TNode reason)
{
  return assertEqInternal(a, b, reason, false);
}

bool InnerEGraph::assertEqInternal(TermId a,
                                   TermId b,
                                   TNode reason,
                                   bool congruence)
{
  TermId ra = find(a);
  TermId rb = find(b);
  if (ra == rb)
  {
    return true;
  }
  // The proof forest edge is between the terms the equality was asserted
  // about, not between their representatives, since that is what the
  // explanation has to reconstruct.
  addProofEdge(a, b, reason, congruence);
  if (d_terms[ra].d_classSize > d_terms[rb].d_classSize)
  {
    std::swap(ra, rb);
  }
  merge(ra, rb);
  // process the congruences the merge created, to a fixed point
  std::vector<std::pair<TermId, TermId>> cong;
  repairParents(ra, cong);
  while (!cong.empty())
  {
    std::pair<TermId, TermId> c = cong.back();
    cong.pop_back();
    TermId rc1 = find(c.first);
    TermId rc2 = find(c.second);
    if (rc1 == rc2)
    {
      continue;
    }
    addProofEdge(c.first, c.second, Node::null(), true);
    if (d_terms[rc1].d_classSize > d_terms[rc2].d_classSize)
    {
      std::swap(rc1, rc2);
    }
    merge(rc1, rc2);
    repairParents(rc1, cong);
  }
  // a disequality asserted earlier may now be violated
  return checkDisequalities();
}

bool InnerEGraph::checkDisequalities()
{
  for (size_t i = 0, ndeqs = d_diseqs.size(); i < ndeqs; i++)
  {
    if (find(d_diseqs[i].first) == find(d_diseqs[i].second))
    {
      setDiseqConflict(i);
      return false;
    }
  }
  return true;
}

void InnerEGraph::setDiseqConflict(size_t i)
{
  const std::pair<TermId, TermId>& d = d_diseqs[i];
  d_conflict.clear();
  explain(d.first, d.second, d_conflict);
  std::map<std::pair<TermId, TermId>, Node>::const_iterator itr =
      d_reasons.find(d);
  if (itr != d_reasons.end() && !itr->second.isNull())
  {
    d_conflict.push_back(itr->second);
  }
}

void InnerEGraph::addProofEdge(TermId a,
                               TermId b,
                               TNode reason,
                               bool congruence)
{
  reorient(a);
  d_undo.push_back(UndoEntry(UndoEntry::Kind::PROOF_EDGE,
                             a,
                             d_terms[a].d_pfParent,
                             d_terms[a].d_pfReason,
                             d_terms[a].d_pfCongruence));
  d_terms[a].d_pfParent = b;
  d_terms[a].d_pfReason = reason;
  d_terms[a].d_pfCongruence = congruence;
}

void InnerEGraph::reorient(TermId a)
{
  TermId prev = undefinedTerm;
  Node prevReason;
  bool prevCong = false;
  TermId curr = a;
  while (curr != undefinedTerm)
  {
    TermId next = d_terms[curr].d_pfParent;
    Node nextReason = d_terms[curr].d_pfReason;
    bool nextCong = d_terms[curr].d_pfCongruence;
    d_undo.push_back(UndoEntry(
        UndoEntry::Kind::PROOF_EDGE, curr, next, nextReason, nextCong));
    d_terms[curr].d_pfParent = prev;
    d_terms[curr].d_pfReason = prevReason;
    d_terms[curr].d_pfCongruence = prevCong;
    prev = curr;
    prevReason = nextReason;
    prevCong = nextCong;
    curr = next;
  }
}

InnerEGraph::TermId InnerEGraph::proofAncestor(TermId a, TermId b) const
{
  std::unordered_set<TermId> onPath;
  for (TermId curr = a; curr != undefinedTerm; curr = d_terms[curr].d_pfParent)
  {
    onPath.insert(curr);
  }
  for (TermId curr = b; curr != undefinedTerm; curr = d_terms[curr].d_pfParent)
  {
    if (onPath.find(curr) != onPath.end())
    {
      return curr;
    }
  }
  return undefinedTerm;
}

void InnerEGraph::explainPath(
    TermId a,
    TermId c,
    std::vector<Node>& exp,
    std::vector<std::pair<TermId, TermId>>& pending) const
{
  TermId curr = a;
  while (curr != c && curr != undefinedTerm)
  {
    TermId parent = d_terms[curr].d_pfParent;
    if (d_terms[curr].d_pfCongruence)
    {
      // the two terms are congruent, so the explanation is the explanation of
      // their arguments being equal
      Assert(d_terms[curr].d_args.size() == d_terms[parent].d_args.size());
      for (size_t i = 0, nargs = d_terms[curr].d_args.size(); i < nargs; i++)
      {
        pending.emplace_back(d_terms[curr].d_args[i],
                             d_terms[parent].d_args[i]);
      }
    }
    else if (!d_terms[curr].d_pfReason.isNull())
    {
      exp.push_back(d_terms[curr].d_pfReason);
    }
    curr = parent;
  }
}

void InnerEGraph::explain(TermId a, TermId b, std::vector<Node>& exp) const
{
  std::vector<std::pair<TermId, TermId>> pending{{a, b}};
  std::set<std::pair<TermId, TermId>> seen;
  while (!pending.empty())
  {
    std::pair<TermId, TermId> curr = pending.back();
    pending.pop_back();
    if (curr.first == curr.second || !seen.insert(curr).second)
    {
      continue;
    }
    TermId c = proofAncestor(curr.first, curr.second);
    Assert(c != undefinedTerm)
        << "inner e-graph: explaining an equality that does not hold";
    explainPath(curr.first, c, exp, pending);
    explainPath(curr.second, c, exp, pending);
  }
  // the same literal may justify several steps
  std::sort(exp.begin(), exp.end());
  exp.erase(std::unique(exp.begin(), exp.end()), exp.end());
}

void InnerEGraph::merge(TermId a, TermId b)
{
  Assert(find(a) == a && find(b) == b);
  if (d_listener != nullptr)
  {
    d_listener->notifyMerge(a, b);
  }
  d_undo.push_back(UndoEntry(UndoEntry::Kind::MERGE, a, b));
  // re-root the class of a
  TermId curr = a;
  do
  {
    d_terms[curr].d_find = b;
    curr = d_terms[curr].d_next;
  } while (curr != a);
  std::swap(d_terms[a].d_next, d_terms[b].d_next);
  d_terms[b].d_classSize += d_terms[a].d_classSize;
  d_undo.push_back(UndoEntry(
      UndoEntry::Kind::PARENTS, b, undefinedTerm, d_terms[b].d_parents.size()));
  d_terms[b].d_parents.insert(d_terms[b].d_parents.end(),
                              d_terms[a].d_parents.begin(),
                              d_terms[a].d_parents.end());
}

void InnerEGraph::repairParents(TermId oldRoot,
                                std::vector<std::pair<TermId, TermId>>& cong)
{
  // The parents of the class that was absorbed have a stale congruence key.
  // Remove them and re-insert them under the new representatives, which is
  // where congruences are discovered.
  std::vector<TermId> ps = d_terms[oldRoot].d_parents;
  for (TermId p : ps)
  {
    if (d_terms[p].d_cgOwner)
    {
      cgErase(p);
    }
    CgKey key = mkCgKey(p);
    std::map<CgKey, TermId>::iterator itc = d_cg.find(key);
    if (itc == d_cg.end())
    {
      cgInsert(p, key);
    }
    else if (!areEqual(p, itc->second))
    {
      cong.emplace_back(p, itc->second);
    }
  }
}

void InnerEGraph::cgInsert(TermId t, const CgKey& key)
{
  d_cg[key] = t;
  d_terms[t].d_cgOwner = true;
  d_terms[t].d_cgKey = key;
  d_undo.push_back(UndoEntry(UndoEntry::Kind::CG_INSERT, t, key));
}

void InnerEGraph::cgErase(TermId t)
{
  Assert(d_terms[t].d_cgOwner);
  const CgKey& key = d_terms[t].d_cgKey;
  d_undo.push_back(UndoEntry(UndoEntry::Kind::CG_ERASE, t, key));
  d_cg.erase(key);
  d_terms[t].d_cgOwner = false;
}

bool InnerEGraph::assertDiseq(TermId a, TermId b, TNode reason)
{
  std::pair<TermId, TermId> d(a, b);
  d_diseqs.push_back(d);
  d_undo.push_back(
      UndoEntry(UndoEntry::Kind::DISEQ, a, b, d_diseqs.size() - 1));
  if (!reason.isNull())
  {
    d_reasons[d] = reason;
  }
  if (find(a) == find(b))
  {
    d_conflict.clear();
    explain(a, b, d_conflict);
    if (!reason.isNull())
    {
      d_conflict.push_back(reason);
    }
    return false;
  }
  return true;
}

void InnerEGraph::restoreTo(size_t c)
{
  Assert(c <= d_undo.size());
  while (d_undo.size() > c)
  {
    undo(d_undo.back());
    d_undo.pop_back();
  }
}

void InnerEGraph::undo(const UndoEntry& e)
{
  switch (e.d_kind)
  {
    case UndoEntry::Kind::ADD_TERM:
      Assert(e.d_a + 1 == d_terms.size());
      d_termMap.erase(d_terms[e.d_a].d_node);
      d_terms.pop_back();
      break;
    case UndoEntry::Kind::MERGE:
    {
      TermId a = e.d_a;
      TermId b = e.d_b;
      std::swap(d_terms[a].d_next, d_terms[b].d_next);
      TermId curr = a;
      do
      {
        d_terms[curr].d_find = a;
        curr = d_terms[curr].d_next;
      } while (curr != a);
      d_terms[b].d_classSize -= d_terms[a].d_classSize;
    }
    break;
    case UndoEntry::Kind::PARENTS:
      d_terms[e.d_a].d_parents.resize(e.d_size);
      break;
    case UndoEntry::Kind::CG_INSERT:
      d_cg.erase(e.d_key);
      d_terms[e.d_a].d_cgOwner = false;
      break;
    case UndoEntry::Kind::CG_ERASE:
      d_cg[e.d_key] = e.d_a;
      d_terms[e.d_a].d_cgOwner = true;
      d_terms[e.d_a].d_cgKey = e.d_key;
      break;
    case UndoEntry::Kind::DISEQ:
      d_diseqs.resize(e.d_size);
      d_reasons.erase(std::pair<TermId, TermId>(e.d_a, e.d_b));
      break;
    case UndoEntry::Kind::PROOF_EDGE:
      d_terms[e.d_a].d_pfParent = e.d_b;
      d_terms[e.d_a].d_pfReason = e.d_key.first;
      d_terms[e.d_a].d_pfCongruence = e.d_size == 1;
      break;
  }
}

void InnerEGraph::debugPrint(std::ostream& out) const
{
  out << "inner-egraph: " << d_terms.size() << " terms" << std::endl;
  for (TermId t = 0; t < d_terms.size(); t++)
  {
    if (find(t) != t)
    {
      continue;
    }
    out << "  class " << d_terms[t].d_node << ":";
    TermId curr = t;
    do
    {
      out << " " << d_terms[curr].d_node;
      curr = d_terms[curr].d_next;
    } while (curr != t);
    out << std::endl;
  }
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The e-graph mirror used by eager E-matching.
 */

#include "theory/quantifiers/eager/egraph.h"

#include <ostream>

#include "expr/node_algorithm.h"
#include "theory/quantifiers/term_util.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

ENode::ENode(Node n,
             Node label,
             std::vector<ENode*>&& args,
             uint32_t generation)
    : d_node(n),
      d_label(label),
      d_args(std::move(args)),
      d_root(this),
      d_next(this),
      d_classSize(1),
      d_cgr(this),
      d_lblHash(-1),
      d_generation(generation),
      d_mark(false),
      d_mark2(false)
{
}

std::ostream& operator<<(std::ostream& out, const ENode& e)
{
  return out << e.getNode();
}

EGraph::EGraph(Env& env, Trail& trail)
    : EnvObj(env),
      d_trail(trail),
      d_termStack(*this),
      d_mergeStack(*this),
      d_generation(0)
{
}

EGraph::~EGraph() {}

Node EGraph::getLabelFor(TNode n)
{
  if (!n.hasOperator())
  {
    return Node::null();
  }
  return n.getOperator();
}

bool EGraph::isTracked(TNode n)
{
  Kind k = n.getKind();
  if (k == Kind::BUILTIN || n.isClosure())
  {
    return false;
  }
  // terms with variables in them are not ground, hence are not candidates for
  // matching and cannot be arguments of the terms we match against
  if (expr::hasBoundVar(n))
  {
    return false;
  }
  // Instantiation constants stand for the universally quantified holes of a
  // quantified formula, and cvc5 marks the terms that represent a
  // counterexample with the same attribute. Both are in the master equality
  // engine because of counterexample-guided and sygus instantiation, and it is
  // model-unsound to instantiate with either, which is why cvc5's
  // TermDb::addTerm excludes them and Instantiate rejects them outright.
  return !TermUtil::hasInstConstAttr(Node(n));
}

EGraph::CgKey EGraph::mkCgKey(ENode* e) const
{
  std::vector<ENode*> roots;
  roots.reserve(e->getNumArgs());
  for (size_t i = 0, nargs = e->getNumArgs(); i < nargs; i++)
  {
    roots.push_back(e->getArg(i)->getRoot());
  }
  return CgKey(e->getLabel(), roots);
}

void EGraph::cgInsert(ENode* e)
{
  CgKey key = mkCgKey(e);
  std::map<CgKey, ENode*>::const_iterator it = d_cg.find(key);
  if (it == d_cg.end())
  {
    d_cg[key] = e;
    e->d_cgr = e;
    e->d_cgKey = key;
    return;
  }
  // e is congruent to a node that already owns the entry; e is not a
  // congruence representative. The two are in the same class as soon as the
  // master equality engine has propagated the congruence, which it reports to
  // us as an ordinary merge.
  e->d_cgr = it->second;
}

void EGraph::cgErase(ENode* e)
{
  Assert(e->isCgr());
  d_cg.erase(e->d_cgKey);
  e->d_cgKey = CgKey(Node::null(), std::vector<ENode*>());
}

ENode* EGraph::getENodeEqTo(TNode label, const std::vector<ENode*>& args) const
{
  std::vector<ENode*> roots;
  roots.reserve(args.size());
  for (ENode* a : args)
  {
    roots.push_back(a->getRoot());
  }
  std::map<CgKey, ENode*>::const_iterator it = d_cg.find(CgKey(label, roots));
  return it == d_cg.end() ? nullptr : it->second;
}

ENode* EGraph::getENode(TNode n) const
{
  std::map<Node, ENode*>::const_iterator it = d_nodeMap.find(n);
  return it == d_nodeMap.end() ? nullptr : it->second;
}

bool EGraph::areEqual(TNode t1, TNode t2) const
{
  ENode* e1 = getENode(t1);
  ENode* e2 = getENode(t2);
  return e1 != nullptr && e2 != nullptr && e1->getRoot() == e2->getRoot();
}

ENode* EGraph::addTerm(TNode n)
{
  ENode* e = getENode(n);
  if (e != nullptr)
  {
    return e;
  }
  if (!isTracked(n))
  {
    return nullptr;
  }
  // ensure the arguments exist, bottom up
  Node label = getLabelFor(n);
  std::vector<ENode*> args;
  for (const Node& nc : n)
  {
    ENode* ec = addTerm(nc);
    if (ec == nullptr)
    {
      // an argument we do not track makes the application untrackable
      return nullptr;
    }
    args.push_back(ec);
  }
  d_trail.restoreSize(&d_termStack, d_enodes.size());
  d_enodes.emplace_back(new ENode(n, label, std::move(args), d_generation));
  e = d_enodes.back().get();
  d_nodeMap[n] = e;
  Trace("eager-egraph") << "EGraph: add " << n << ", generation "
                        << d_generation << std::endl;
  if (!label.isNull())
  {
    d_opMap[label].push_back(e);
    // register as a parent of the classes of the arguments
    for (size_t i = 0, nargs = e->getNumArgs(); i < nargs; i++)
    {
      e->getArg(i)->getRoot()->d_parents.push_back(e);
    }
    if (e->getNumArgs() > 0)
    {
      cgInsert(e);
    }
  }
  // this is the label maintenance half of z3's mam::relevant_eh
  if (e->hasLblHash())
  {
    updateLbls(e, e->getLblHash());
  }
  if (e->getNumArgs() > 0)
  {
    size_t h = getLabelHash(label);
    if (isChildLabel(label))
    {
      updateLbls(e, h);
    }
    if (isParentLabel(label))
    {
      updateChildrenPlbls(e, h);
    }
  }
  // the candidate collection half of z3's mam::relevant_eh
  for (EGraphListener* l : d_listeners)
  {
    l->notifyNewENode(e);
  }
  return e;
}

void EGraph::assertEq(TNode t1, TNode t2)
{
  ENode* e1 = addTerm(t1);
  ENode* e2 = addTerm(t2);
  if (e1 == nullptr || e2 == nullptr)
  {
    return;
  }
  ENode* r1 = e1->getRoot();
  ENode* r2 = e2->getRoot();
  if (r1 == r2)
  {
    return;
  }
  // z3 merges the smaller class into the larger one (context::add_eq)
  if (r1->getClassSize() > r2->getClassSize())
  {
    std::swap(r1, r2);
  }
  Trace("eager-egraph") << "EGraph: merge " << *r1 << " into " << *r2
                        << std::endl;
  // Notify before the union, which is where z3 calls mam::add_eq_eh: the two
  // classes must still be separate for the matcher to find the terms that the
  // merge makes congruent.
  for (EGraphListener* l : d_listeners)
  {
    l->notifyPreMerge(r1, r2);
  }
  merge(r1, r2);
}

void EGraph::merge(ENode* r1, ENode* r2)
{
  Assert(r1->getRoot() == r1 && r2->getRoot() == r2);
  d_trail.restoreSize(&d_mergeStack, d_merges.size());
  d_merges.push_back(MergeRecord{r1,
                                 r2,
                                 r1->d_next,
                                 r2->d_next,
                                 r2->d_classSize,
                                 static_cast<uint32_t>(r2->d_parents.size()),
                                 r2->d_lbls,
                                 r2->d_plbls,
                                 d_cgUndo.size()});
  // The parents of the class being absorbed have a congruence key that is
  // about to become stale. z3 does the same in two steps around the splice
  // (remove_parents_from_cg_table / reinsert_parents_into_cg_table).
  const std::vector<ENode*> parents1(r1->d_parents.begin(),
                                     r1->d_parents.end());
  for (ENode* p : parents1)
  {
    d_cgUndo.push_back(CgUndo{p, p->d_cgr, p->d_cgKey, p->isCgr()});
    if (p->isCgr())
    {
      cgErase(p);
    }
  }
  // re-root the class of r1
  ENode* curr = r1;
  do
  {
    curr->d_root = r2;
    curr = curr->d_next;
  } while (curr != r1);
  // splice the two cyclic lists
  std::swap(r1->d_next, r2->d_next);
  r2->d_classSize += r1->d_classSize;
  // the parents of the class are maintained on the root
  r2->d_parents.insert(
      r2->d_parents.end(), r1->d_parents.begin(), r1->d_parents.end());
  // z3: add_eq_eh, r2_lbls |= r1_lbls; r2_plbls |= r1_plbls
  r2->d_lbls |= r1->d_lbls;
  r2->d_plbls |= r1->d_plbls;
  // re-insert the parents under their new keys, which is where congruences
  // become visible
  for (ENode* p : parents1)
  {
    cgInsert(p);
  }
}

void EGraph::popMerges(size_t n)
{
  while (d_merges.size() > n)
  {
    const MergeRecord& m = d_merges.back();
    ENode* r1 = m.d_r1;
    ENode* r2 = m.d_r2;
    // restore the two cyclic lists before walking the class of r1
    r1->d_next = m.d_next1;
    r2->d_next = m.d_next2;
    ENode* curr = r1;
    do
    {
      curr->d_root = r1;
      curr = curr->d_next;
    } while (curr != r1);
    r2->d_classSize = m.d_classSize2;
    r2->d_parents.resize(m.d_numParents2);
    r2->d_lbls = m.d_lbls2;
    r2->d_plbls = m.d_plbls2;
    // undo the congruence table changes of this merge, in two passes so that
    // a key that moved from one node to another is restored correctly
    for (size_t i = d_cgUndo.size(); i-- > m.d_cgUndoBegin;)
    {
      ENode* p = d_cgUndo[i].d_node;
      if (p->isCgr())
      {
        cgErase(p);
      }
    }
    for (size_t i = d_cgUndo.size(); i-- > m.d_cgUndoBegin;)
    {
      const CgUndo& cu = d_cgUndo[i];
      cu.d_node->d_cgr = cu.d_oldCgr;
      cu.d_node->d_cgKey = cu.d_oldKey;
      if (cu.d_wasOwner)
      {
        d_cg[cu.d_oldKey] = cu.d_node;
      }
    }
    d_cgUndo.resize(m.d_cgUndoBegin);
    d_merges.pop_back();
  }
}

void EGraph::popTerms(size_t n)
{
  while (d_enodes.size() > n)
  {
    ENode* e = d_enodes.back().get();
    if (!e->getLabel().isNull())
    {
      // remove from the parent lists of the arguments, in reverse order
      for (size_t i = e->getNumArgs(); i-- > 0;)
      {
        TrailedVector<ENode*>& ps = e->getArg(i)->getRoot()->d_parents;
        Assert(!ps.empty() && ps.back() == e);
        ps.pop_back();
      }
      std::vector<ENode*>& os = d_opMap[e->getLabel()];
      Assert(!os.empty() && os.back() == e);
      os.pop_back();
      if (e->getNumArgs() > 0 && e->isCgr())
      {
        cgErase(e);
      }
    }
    d_nodeMap.erase(e->getNode());
    d_enodes.pop_back();
  }
}

void EGraph::assertDiseq(TNode t1, TNode t2, CVC5_UNUSED TNode reason)
{
  ENode* e1 = addTerm(t1);
  ENode* e2 = addTerm(t2);
  size_t sz = d_diseqs.size();
  d_diseqs.emplace_back(t1, t2);
  d_trail.onPop([this, sz]() { d_diseqs.resize(sz); });
  if (e1 == nullptr || e2 == nullptr)
  {
    return;
  }
  for (EGraphListener* l : d_listeners)
  {
    l->notifyDiseq(e1, e2);
  }
}

void EGraph::updateLbls(ENode* e, size_t h)
{
  ApproxSet& lbls = e->getRoot()->d_lbls;
  if (!lbls.mayContain(h))
  {
    d_trail.restore(&lbls);
    lbls.insert(h);
  }
}

void EGraph::updateChildrenPlbls(ENode* e, size_t h)
{
  for (size_t i = 0, nargs = e->getNumArgs(); i < nargs; i++)
  {
    ApproxSet& plbls = e->getArg(i)->getRoot()->d_plbls;
    if (!plbls.mayContain(h))
    {
      d_trail.restore(&plbls);
      plbls.insert(h);
    }
  }
}

bool EGraph::isChildLabel(TNode op) const
{
  return d_isClbl.find(op) != d_isClbl.end();
}

bool EGraph::isParentLabel(TNode op) const
{
  return d_isPlbl.find(op) != d_isPlbl.end();
}

void EGraph::markChildLabel(TNode op)
{
  if (isChildLabel(op))
  {
    return;
  }
  Node opn = op;
  d_isClbl.insert(opn);
  d_trail.onPop([this, opn]() { d_isClbl.erase(opn); });
  size_t h = getLabelHash(op);
  for (ENode* e : getENodesForLabel(op))
  {
    updateLbls(e, h);
  }
}

void EGraph::markParentLabel(TNode op)
{
  if (isParentLabel(op))
  {
    return;
  }
  Node opn = op;
  d_isPlbl.insert(opn);
  d_trail.onPop([this, opn]() { d_isPlbl.erase(opn); });
  size_t h = getLabelHash(op);
  for (ENode* e : getENodesForLabel(op))
  {
    updateChildrenPlbls(e, h);
  }
}

void EGraph::setLblHash(ENode* e, size_t h)
{
  if (e->hasLblHash())
  {
    Assert(e->getLblHash() == h);
    return;
  }
  e->d_lblHash = static_cast<int32_t>(h);
  d_trail.onPop([e]() { e->d_lblHash = -1; });
  updateLbls(e, h);
}

const std::vector<ENode*>& EGraph::getENodesForLabel(TNode op) const
{
  std::map<Node, std::vector<ENode*>>::const_iterator it = d_opMap.find(op);
  return it == d_opMap.end() ? d_emptyVec : it->second;
}

size_t EGraph::getNumENodesForLabel(TNode op) const
{
  return getENodesForLabel(op).size();
}

void EGraph::debugPrint(std::ostream& out) const
{
  out << "egraph: " << d_enodes.size() << " nodes" << std::endl;
  for (const std::unique_ptr<ENode>& e : d_enodes)
  {
    if (e->getRoot() != e.get())
    {
      continue;
    }
    out << "  class " << *e << " (size " << e->getClassSize() << ", lbls "
        << e->getLbls() << ", plbls " << e->getPlbls() << "):";
    ENode* curr = e.get();
    do
    {
      out << " " << *curr;
      curr = curr->getNext();
    } while (curr != e.get());
    out << std::endl;
  }
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

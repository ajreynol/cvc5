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
 *
 * This maintains, for the terms the master equality engine tells us about, the
 * structure that z3's matching abstract machine reads from its enodes: the
 * cyclic list of class members, the parent list of each class, the two
 * approximate label sets, and the generation of each term. See
 * theory/quantifiers/eager/README.md sections 3.1 and 4 for why this is a
 * separate structure rather than reads of cvc5's EqualityEngine.
 *
 * z3 counterpart: smt/smt_enode.h together with the e-graph part of
 * smt/smt_context.cpp.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__EGRAPH_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__EGRAPH_H

#include <map>
#include <memory>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/eager/approx_set.h"
#include "theory/quantifiers/eager/trail.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

class EGraph;

/**
 * A node of the e-graph mirror. The fields that are only meaningful on the
 * root of a class are marked as such; this mirrors z3's enode, where the same
 * convention holds.
 */
class ENode
{
  friend class EGraph;

 public:
  /** The term this node stands for */
  Node getNode() const { return d_node; }
  /**
   * The label of this node, i.e. its operator, or the null node if this node
   * is a leaf (a variable or a constant). z3: enode::get_decl.
   */
  TNode getLabel() const { return d_label; }
  /** The number of arguments */
  size_t getNumArgs() const { return d_args.size(); }
  /** The i^th argument */
  ENode* getArg(size_t i) const { return d_args[i]; }
  /** The representative of this node's class. z3: enode::get_root */
  ENode* getRoot() const { return d_root; }
  /** The next node in this node's class, cyclically. z3: enode::get_next */
  ENode* getNext() const { return d_next; }
  /** The number of nodes in this node's class (root only) */
  size_t getClassSize() const { return d_classSize; }
  /** The parents of this node's class (root only) */
  const std::vector<ENode*>& getParents() const { return d_parents; }
  size_t getNumParents() const { return d_parents.size(); }
  /** The labels of the applications in this node's class (root only) */
  const ApproxSet& getLbls() const { return d_lbls; }
  /** The labels of the parents of this node's class (root only) */
  const ApproxSet& getPlbls() const { return d_plbls; }
  /**
   * Whether this node occurs as a ground term in a pattern; if so, its label
   * hash is tracked in the class label set. z3: enode::has_lbl_hash.
   */
  bool hasLblHash() const { return d_lblHash >= 0; }
  size_t getLblHash() const { return static_cast<size_t>(d_lblHash); }
  /**
   * The congruence representative of this node, i.e. the node that owns the
   * entry of the congruence table for this node's label and argument
   * representatives. z3: enode::get_cg.
   */
  ENode* getCgr() const { return d_cgr; }
  /** Is this node its own congruence representative? z3: enode::is_cgr */
  bool isCgr() const { return d_cgr == this; }
  /**
   * The generation of this term: 0 for terms from the input, g for terms
   * introduced by an instance of generation g. As in z3, this is the
   * generation of the congruence representative (context::get_generation).
   */
  uint32_t getGeneration() const { return d_cgr->d_generation; }
  /** Is this node the same as or equal to e? */
  bool isEqualTo(const ENode* e) const { return d_root == e->d_root; }

  /**
   * Temporary marks, used by the matcher while walking parents. They are
   * always cleared before returning to the caller, hence not trailed. z3:
   * enode::is_marked / is_marked2.
   */
  bool isMarked() const { return d_mark; }
  void setMark(bool v) { d_mark = v; }
  bool isMarked2() const { return d_mark2; }
  void setMark2(bool v) { d_mark2 = v; }

 private:
  ENode(Node n, Node label, std::vector<ENode*>&& args, uint32_t generation);
  /** The term */
  Node d_node;
  /** The operator, or null if a leaf */
  Node d_label;
  /** The arguments */
  std::vector<ENode*> d_args;
  /** The representative of this node's class */
  ENode* d_root;
  /** The next element of this node's class */
  ENode* d_next;
  /** The size of this node's class (root only) */
  uint32_t d_classSize;
  /** The parents of this node's class (root only) */
  TrailedVector<ENode*> d_parents;
  /** Label sets (root only) */
  ApproxSet d_lbls;
  ApproxSet d_plbls;
  /** The congruence representative of this node */
  ENode* d_cgr;
  /** The key of the congruence table entry this node owns, if it owns one */
  std::pair<Node, std::vector<ENode*>> d_cgKey;
  /** The label hash of this node if it is a pattern ground term, else -1 */
  int32_t d_lblHash;
  /** The generation */
  uint32_t d_generation;
  /** Temporary marks */
  bool d_mark;
  bool d_mark2;
};

std::ostream& operator<<(std::ostream& out, const ENode& e);

/**
 * Interface for the consumer of e-graph events, implemented by Mam. Kept
 * separate so that the e-graph does not depend on the matcher.
 */
class EGraphListener
{
 public:
  virtual ~EGraphListener() {}
  /**
   * Called when e is added to the e-graph. This is the candidate-collection
   * half of z3's mam::relevant_eh.
   */
  virtual void notifyNewENode(ENode* e) = 0;
  /**
   * Called when the classes of r1 and r2 are about to be merged, with r1 the
   * class that will be absorbed into r2. The classes are still separate, as
   * they are at the point where z3 calls mam::add_eq_eh (smt_context.cpp, in
   * context::add_eq, before the parents of r1 are touched).
   */
  virtual void notifyPreMerge(ENode* r1, ENode* r2) = 0;
  /**
   * Called when the classes of e1 and e2 are asserted disequal. Only the inner
   * SMT solver cares; the matcher does not.
   */
  virtual void notifyDiseq(CVC5_UNUSED ENode* e1, CVC5_UNUSED ENode* e2) {}
};

/**
 * The e-graph mirror. It is fed by the notifications of the master equality
 * engine and is backtracked through its own Trail.
 */
class EGraph : protected EnvObj
{
 public:
  /** The key of the congruence table: a label and the argument classes */
  using CgKey = std::pair<Node, std::vector<ENode*>>;

  EGraph(Env& env, Trail& trail);
  ~EGraph();

  /**
   * Add a listener, which must outlive this object. Listeners are notified in
   * the order they were added.
   */
  void addListener(EGraphListener* l) { d_listeners.push_back(l); }

  //-------------------------------------------- the master e-graph interface
  /**
   * Add the term n, called when the master equality engine reports a new
   * equivalence class. Returns the node for n, or nullptr if n is not a term
   * we track. Idempotent.
   */
  ENode* addTerm(TNode n);
  /**
   * Assert that t1 and t2 are equal, called when the master equality engine
   * reports a merge. Notifies the listener before performing the union.
   */
  void assertEq(TNode t1, TNode t2);
  /**
   * Assert that t1 and t2 are disequal, called when the master equality engine
   * reports a disequality. Recorded for the inner SMT solver.
   */
  void assertDiseq(TNode t1, TNode t2, TNode reason);
  //---------------------------------------- end master e-graph interface

  /** The node for n, or nullptr if n is not in the e-graph */
  ENode* getENode(TNode n) const;
  /**
   * The application of label to the classes of args, if the e-graph contains
   * one, else nullptr. z3: context::get_enode_eq_to.
   */
  ENode* getENodeEqTo(TNode label, const std::vector<ENode*>& args) const;
  /** Are t1 and t2 in the same class of this e-graph? */
  bool areEqual(TNode t1, TNode t2) const;
  /** The disequalities asserted so far, in assertion order */
  const std::vector<std::pair<Node, Node>>& getDisequalities() const
  {
    return d_diseqs;
  }

  /** The label hash of op. z3: label_hasher */
  size_t getLabelHash(TNode op) { return d_lblHasher(op); }
  /**
   * The label hash of the term n, i.e. of its operator, or of n itself if n is
   * a leaf. z3 takes the declaration of the enode, which for a constant is the
   * constant itself.
   */
  size_t getLabelHashForTerm(TNode n)
  {
    return d_lblHasher(n.hasOperator() ? Node(n.getOperator()) : Node(n));
  }

  //-------------------------------------------- label tracking
  /**
   * Record that applications of op must contribute their label to the label
   * set of their own class, and annotate the existing applications of op.
   * z3: mam_impl::update_clbls.
   */
  void markChildLabel(TNode op);
  /**
   * Record that applications of op must contribute their label to the parent
   * label set of the classes of their arguments, and annotate the existing
   * applications of op. z3: mam_impl::update_plbls.
   */
  void markParentLabel(TNode op);
  /** Is op marked by markChildLabel? z3: mam_impl::is_clbl */
  bool isChildLabel(TNode op) const;
  /** Is op marked by markParentLabel? z3: mam_impl::is_plbl */
  bool isParentLabel(TNode op) const;
  /** Give e a label hash, for ground terms occurring in patterns */
  void setLblHash(ENode* e, size_t h);
  //---------------------------------------- end label tracking

  /** The applications of op, in creation order. z3: context::enodes_of */
  const std::vector<ENode*>& getENodesForLabel(TNode op) const;
  /** The number of applications of op */
  size_t getNumENodesForLabel(TNode op) const;
  /** The number of nodes in the e-graph */
  size_t getNumENodes() const { return d_enodes.size(); }
  /** The generation assigned to terms added from now on */
  void setGeneration(uint32_t g) { d_generation = g; }
  uint32_t getGeneration() const { return d_generation; }

  /** Print the e-graph, for debugging */
  void debugPrint(std::ostream& out) const;

 private:
  /** Compute the label of n, or the null node if n is a leaf */
  static Node getLabelFor(TNode n);
  /** Should n be tracked at all? */
  static bool isTracked(TNode n);
  /** Add the label of e to the label set of e's own class */
  void updateLbls(ENode* e, size_t h);
  /** Add h to the parent label sets of the classes of e's arguments */
  void updateChildrenPlbls(ENode* e, size_t h);
  /** The key of the congruence table entry of e, under the current classes */
  CgKey mkCgKey(ENode* e) const;
  /** Make e the owner of its congruence table entry, or point it at the owner
   */
  void cgInsert(ENode* e);
  /** Remove the congruence table entry owned by e */
  void cgErase(ENode* e);
  /** Perform the union of the classes of r1 and r2, r1 into r2 */
  void merge(ENode* r1, ENode* r2);
  /** Undo term creations until only n nodes remain */
  void popTerms(size_t n);
  /** Undo merges until only n remain */
  void popMerges(size_t n);

  /** Shrinkable view of the node allocation, for the trail */
  class TermStack : public Shrinkable
  {
   public:
    TermStack(EGraph& eg) : d_eg(eg) {}
    void shrinkTo(size_t n) override { d_eg.popTerms(n); }

   private:
    EGraph& d_eg;
  };
  /** Shrinkable view of the merge stack, for the trail */
  class MergeStack : public Shrinkable
  {
   public:
    MergeStack(EGraph& eg) : d_eg(eg) {}
    void shrinkTo(size_t n) override { d_eg.popMerges(n); }

   private:
    EGraph& d_eg;
  };
  /** What is needed to undo the congruence table change of one node */
  struct CgUndo
  {
    ENode* d_node;
    ENode* d_oldCgr;
    CgKey d_oldKey;
    bool d_wasOwner;
  };
  /** What is needed to undo one merge */
  struct MergeRecord
  {
    ENode* d_r1;
    ENode* d_r2;
    ENode* d_next1;
    ENode* d_next2;
    uint32_t d_classSize2;
    uint32_t d_numParents2;
    ApproxSet d_lbls2;
    ApproxSet d_plbls2;
    /** where the congruence table undo entries of this merge start */
    size_t d_cgUndoBegin;
  };

  /** The trail, owned by the engine */
  Trail& d_trail;
  /** The listener */
  std::vector<EGraphListener*> d_listeners;
  /** The label hasher */
  LabelHasher d_lblHasher;
  /** All nodes, in creation order */
  std::vector<std::unique_ptr<ENode>> d_enodes;
  /** Map from terms to nodes */
  std::map<Node, ENode*> d_nodeMap;
  /** Map from labels to the applications with that label, in creation order */
  std::map<Node, std::vector<ENode*>> d_opMap;
  /** The labels marked by markChildLabel / markParentLabel */
  std::unordered_set<Node> d_isClbl;
  std::unordered_set<Node> d_isPlbl;
  /** Asserted disequalities */
  std::vector<std::pair<Node, Node>> d_diseqs;
  /** The congruence table. z3: smt::cg_table */
  std::map<CgKey, ENode*> d_cg;
  /** The congruence table undo entries of the merges on the merge stack */
  std::vector<CgUndo> d_cgUndo;
  /** The merge stack */
  std::vector<MergeRecord> d_merges;
  /** Trail views */
  TermStack d_termStack;
  MergeStack d_mergeStack;
  /** The generation of terms being added */
  uint32_t d_generation;
  /** Empty vector, returned for labels with no applications */
  std::vector<ENode*> d_emptyVec;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif

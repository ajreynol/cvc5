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
 *
 * This is a fresh implementation rather than theory::eq::EqualityEngine
 * because the inner solver adds and removes instances, and hence terms and
 * equalities, in a way that does not correspond to the scopes of cvc5's
 * context: an instance may be retracted and later re-added at a different
 * cost threshold. All state changes therefore go through an explicit undo log
 * with checkpoints. See theory/quantifiers/eager/README.md section 6.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__INNER_EGRAPH_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__INNER_EGRAPH_H

#include <map>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

/**
 * Interface for the consumer of the merges of an InnerEGraph, implemented by
 * the inner SMT solver to find the atoms a merge may imply.
 */
class InnerEGraphListener
{
 public:
  virtual ~InnerEGraphListener() {}
  /**
   * Called when the class of a is about to be absorbed into the class of b.
   * Both are representatives and the classes are still separate.
   */
  virtual void notifyMerge(size_t a, size_t b) = 0;
};

/**
 * A congruence closure over the terms of the instances the inner solver holds.
 */
class InnerEGraph : protected EnvObj
{
 public:
  /** The identifier of a term in this structure */
  using TermId = size_t;
  static constexpr TermId undefinedTerm = static_cast<TermId>(-1);
  /** The key of the congruence table: a label and the representatives */
  using CgKey = std::pair<Node, std::vector<TermId>>;

  InnerEGraph(Env& env);
  ~InnerEGraph();

  /** Add n and its subterms, returning the identifier of n */
  TermId addTerm(TNode n);
  /** The identifier of n, or undefinedTerm */
  TermId getTerm(TNode n) const;
  /** The term of an identifier */
  TNode getNode(TermId t) const { return d_terms[t].d_node; }
  /** Is the term t of Boolean type? */
  bool isBoolean(TermId t) const { return d_terms[t].d_isBool; }
  /** The next term in the class of t, cyclically */
  TermId getNext(TermId t) const { return d_terms[t].d_next; }
  /** The number of terms in the class of t */
  size_t getClassSize(TermId t) const { return d_terms[find(t)].d_classSize; }
  /** Set the listener, which must outlive this object */
  void setListener(InnerEGraphListener* l) { d_listener = l; }

  /**
   * Assert that a and b are equal, justified by reason. Returns false if this
   * makes the structure inconsistent, in which case getConflict describes why.
   */
  bool assertEq(TermId a, TermId b, TNode reason);
  /** Assert that a and b are disequal, justified by reason */
  bool assertDiseq(TermId a, TermId b, TNode reason);
  /**
   * Check that no asserted disequality is violated. A merge made while adding
   * a term (a congruence) can violate one without being reported, since
   * addTerm has no way to fail. Returns false if one is violated, in which
   * case getConflict describes why.
   */
  bool checkDisequalities();
  /** Are a and b in the same class? */
  bool areEqual(TermId a, TermId b) const { return find(a) == find(b); }
  /** The representative of a */
  TermId find(TermId a) const;

  /**
   * The reasons of the current conflict, valid after assertEq or assertDiseq
   * returned false.
   */
  const std::vector<Node>& getConflict() const { return d_conflict; }
  /**
   * Explain why a and b are equal, appending to exp the literals that were
   * asserted to this structure and that the equality follows from.
   */
  void explain(TermId a, TermId b, std::vector<Node>& exp) const;

  //----------------------------------------------------------- removal
  /**
   * A checkpoint of the state, to which restoreTo can return. Checkpoints are
   * used in last-in-first-out order.
   */
  size_t checkpoint() const { return d_undo.size(); }
  /** Undo everything done since the checkpoint c */
  void restoreTo(size_t c);
  //------------------------------------------------------- end removal

  /** The number of terms */
  size_t getNumTerms() const { return d_terms.size(); }
  /** Print this structure */
  void debugPrint(std::ostream& out) const;

 private:
  /** A term */
  struct Term
  {
    Node d_node;
    Node d_label;
    /** whether d_node is of Boolean type */
    bool d_isBool;
    std::vector<TermId> d_args;
    TermId d_find;
    TermId d_next;
    uint32_t d_classSize;
    /** the parents of this term's class, maintained on the representative */
    std::vector<TermId> d_parents;
    /**
     * A constant in this term's class, if there is one, maintained on the
     * representative. Two distinct constants in one class are a conflict; z3's
     * e-graph does the same with its interpreted roots
     * (context::add_eq, the interpreted roots check).
     */
    TermId d_constTerm;
    /** whether this term owns an entry of the congruence table */
    bool d_cgOwner;
    /** the key of that entry */
    std::pair<Node, std::vector<TermId>> d_cgKey;
    /**
     * The parent of this term in the proof forest, which records why terms are
     * equal. The forest is independent of the union-find: an edge is added for
     * each equality that is asserted or derived by congruence, and the path
     * between two terms in it is the explanation of their equality.
     */
    TermId d_pfParent;
    /** The literal labelling the edge to d_pfParent, null for a congruence */
    Node d_pfReason;
    /** Whether the edge to d_pfParent is a congruence rather than a literal */
    bool d_pfCongruence;
  };
  /** An entry of the undo log */
  struct UndoEntry
  {
    enum class Kind
    {
      ADD_TERM,
      MERGE,
      PARENTS,
      CG_INSERT,
      CG_ERASE,
      DISEQ,
      PROOF_EDGE,
      CONST_TERM
    };
    UndoEntry(Kind k,
              TermId a = undefinedTerm,
              TermId b = undefinedTerm,
              size_t size = 0)
        : d_kind(k),
          d_a(a),
          d_b(b),
          d_size(size),
          d_key(Node::null(), std::vector<TermId>())
    {
    }
    UndoEntry(Kind k, TermId a, const CgKey& key)
        : d_kind(k), d_a(a), d_b(undefinedTerm), d_size(0), d_key(key)
    {
    }
    /** For PROOF_EDGE: restore the proof forest edge of a */
    UndoEntry(Kind k, TermId a, TermId parent, Node reason, bool congruence)
        : d_kind(k),
          d_a(a),
          d_b(parent),
          d_size(congruence ? 1 : 0),
          d_key(reason, std::vector<TermId>())
    {
    }
    Kind d_kind;
    TermId d_a;
    TermId d_b;
    size_t d_size;
    CgKey d_key;
  };
  /** The congruence key of t under the current representatives */
  CgKey mkCgKey(TermId t) const;
  /** Merge the classes of a and b, a into b */
  void merge(TermId a, TermId b);
  /** Re-insert the parents of the old representative, finding congruences */
  void repairParents(TermId oldRoot,
                     std::vector<std::pair<TermId, TermId>>& cong);
  /**
   * Assert that a and b are equal, where reason is the literal that was
   * asserted, or the null node if this is a congruence.
   */
  bool assertEqInternal(TermId a, TermId b, TNode reason, bool congruence);
  /** Set the conflict to the violation of the i^th disequality */
  void setDiseqConflict(size_t i);
  /**
   * Check that the classes of r1 and r2, which are about to be merged, do not
   * hold two distinct constants. Returns false on a conflict.
   */
  bool checkConstClash(TermId r1, TermId r2);
  /** Add the proof forest edge from a to b. z3: euf::egraph proof forest */
  void addProofEdge(TermId a, TermId b, TNode reason, bool congruence);
  /** Make a the root of its proof tree, reversing the path to the old root */
  void reorient(TermId a);
  /** The nearest common ancestor of a and b in the proof forest */
  TermId proofAncestor(TermId a, TermId b) const;
  /**
   * Append to exp the explanation of the proof forest path from a up to the
   * ancestor c, queueing the argument pairs of the congruence edges on it.
   */
  void explainPath(TermId a,
                   TermId c,
                   std::vector<Node>& exp,
                   std::vector<std::pair<TermId, TermId>>& pending) const;
  /** Install t as the owner of the congruence table entry for key */
  void cgInsert(TermId t, const CgKey& key);
  /** Remove the congruence table entry owned by t */
  void cgErase(TermId t);
  /** Undo one entry of the log */
  void undo(const UndoEntry& e);

  /** The terms */
  std::vector<Term> d_terms;
  /** Map from nodes to terms */
  std::map<Node, TermId> d_termMap;
  /** The congruence table */
  std::map<CgKey, TermId> d_cg;
  /** The asserted disequalities, as pairs of representatives at assert time */
  std::vector<std::pair<TermId, TermId>> d_diseqs;
  /** The justification of each merge, indexed as the undo log */
  std::map<std::pair<TermId, TermId>, Node> d_reasons;
  /** The undo log */
  std::vector<UndoEntry> d_undo;
  /** The reasons of the current conflict */
  std::vector<Node> d_conflict;
  /** The listener, if any */
  InnerEGraphListener* d_listener;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif

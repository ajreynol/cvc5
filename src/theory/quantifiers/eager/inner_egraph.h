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

  /**
   * Assert that a and b are equal, justified by reason. Returns false if this
   * makes the structure inconsistent, in which case getConflict describes why.
   */
  bool assertEq(TermId a, TermId b, TNode reason);
  /** Assert that a and b are disequal, justified by reason */
  bool assertDiseq(TermId a, TermId b, TNode reason);
  /** Are a and b in the same class? */
  bool areEqual(TermId a, TermId b) const { return find(a) == find(b); }
  /** The representative of a */
  TermId find(TermId a) const;

  /**
   * The reasons of the current conflict, valid after assertEq or assertDiseq
   * returned false.
   */
  const std::vector<Node>& getConflict() const { return d_conflict; }
  /** Explain why a and b are equal, appending the reasons to exp */
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
    std::vector<TermId> d_args;
    TermId d_find;
    TermId d_next;
    uint32_t d_classSize;
    /** the parents of this term's class, maintained on the representative */
    std::vector<TermId> d_parents;
    /** whether this term owns an entry of the congruence table */
    bool d_cgOwner;
    /** the key of that entry */
    std::pair<Node, std::vector<TermId>> d_cgKey;
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
      DISEQ
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
    Kind d_kind;
    TermId d_a;
    TermId d_b;
    size_t d_size;
    CgKey d_key;
  };
  /** The congruence key of t under the current representatives */
  CgKey mkCgKey(TermId t) const;
  /** Merge the classes of a and b, a into b */
  void merge(TermId a, TermId b, TNode reason);
  /** Re-insert the parents of the old representative, finding congruences */
  void repairParents(TermId oldRoot,
                     std::vector<std::pair<TermId, TermId>>& cong);
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
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif

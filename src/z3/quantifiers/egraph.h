/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The E-graph of the ported Z3 core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * the E-graph part of file src/smt/smt_context.cpp, and recast in cvc5
 * style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__QUANTIFIERS__EGRAPH_H
#define CVC5__Z3__QUANTIFIERS__EGRAPH_H

#include <unordered_map>
#include <utility>
#include <vector>

#include "context/cdhashmap.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "z3/quantifiers/cg_table.h"
#include "z3/quantifiers/enode.h"
#include "z3/quantifiers/statistics.h"
#include "z3/quantifiers/trail.h"

namespace cvc5::internal {

namespace theory::eq {
class EqualityEngine;
}

namespace z3 {

class SmtContext;

/**
 * The E-graph: the enodes of the terms the core internalized, their
 * equivalence classes and congruence closure, the parents of each class, the
 * congruence table, and the generations of the terms.
 *
 * Its merges are those of the atoms the core assigns, which SmtContext
 * gives it (addEq), the congruences they imply, and the merges of cvc5's
 * master equality engine (notifyMasterMerge). Its state is backtracked
 * through the trail stack of SmtContext, which owns it. A merge notifies
 * SmtContext, for relevancy, E-matching, and the Boolean value of the classes
 * of Boolean terms (see addEq).
 */
class EGraph : protected EnvObj
{
 public:
  EGraph(Env& env, SmtContext& ctx, TrailStack& trail, Statistics& stats);

  EGraph(const EGraph&) = delete;
  EGraph& operator=(const EGraph&) = delete;

  // ------------------------------------------------------------- the enodes
  /**
   * Make the enode of n, of the given generation, at the scope level
   * scopeLvl; see ENode::mk.
   */
  ENode* mkENode(TNode n,
                 uint32_t generation,
                 bool suppressArgs,
                 bool mergeTf,
                 bool cgcEnabled,
                 uint32_t scopeLvl);
  /** Undo the last mkENode; invoked from the trail. */
  void undoMkENode();

  ENode* getENode(TNode n) const
  {
    Assert(eInternalized(n));
    return d_app2ENode[n.getId()];
  }

  /** Like getENode, but returns null if n is not internalized. */
  ENode* findENode(TNode n) const
  {
    size_t id = n.getId();
    return id < d_app2ENode.size() ? d_app2ENode[id] : nullptr;
  }

  bool eInternalized(TNode n) const { return findENode(n) != nullptr; }

  size_t getNumEInternalized() const { return d_eInternalizedStack.size(); }

  TNode getEInternalized(size_t idx) const { return d_eInternalizedStack[idx]; }

  /**
   * The term after n in its equivalence class (n itself for a singleton),
   * or null if n is not a term of the E-graph.
   */
  TNode getNextInEClass(TNode n) const
  {
    ENode* e = findENode(n);
    return e == nullptr ? TNode::null() : TNode(e->getNext()->getExpr());
  }

  size_t getNumENodesOf(TNode decl) const
  {
    uint32_t id = getDeclIdOption(decl);
    return id < d_decl2ENodes.size() ? d_decl2ENodes[id].size() : 0;
  }

  const ENodeVector& enodesOf(TNode decl) const
  {
    uint32_t id = getDeclIdOption(decl);
    return id < d_decl2ENodes.size() ? d_decl2ENodes[id] : d_emptyVector;
  }

  /**
   * A dense id for a declaration, created on demand. This is the counterpart
   * of Z3's func_decl::get_small_id, which the E-matching engine uses to index
   * its tables by function symbol.
   */
  uint32_t getDeclId(TNode decl);
  /** The dense id of decl, or UINT32_MAX if it has none yet. */
  uint32_t getDeclIdOption(TNode decl) const;

  // -------------------------------------------------------- the generations
  uint32_t getGeneration(ENode* e) const
  {
    // Patterns with equalities are not supported, so there is no need to
    // track the generation of equality nodes.
    if (e->isEq())
    {
      return 0;
    }
    return getCgRoot(e)->d_generation;
  }

  uint32_t getMaxGeneration(size_t numENodes, ENode* const* enodes) const
  {
    uint32_t max = 0;
    for (size_t i = 0; i < numENodes; ++i)
    {
      uint32_t curr = getGeneration(enodes[i]);
      if (curr > max)
      {
        max = curr;
      }
    }
    return max;
  }

  void setGeneration(ENode* e, uint32_t generation);
  /** Undo a congruence class generation merge; invoked from the trail. */
  void undoMergeCgcGenerations(ENode* e1,
                               uint32_t e1Generation,
                               ENode* e2,
                               uint32_t e2Generation);

  // ---------------------------------------------- equality and congruence
  static bool isEq(const ENode* n1, const ENode* n2)
  {
    return n1->getRoot() == n2->getRoot();
  }

  /** Merge the classes of n1 and n2. */
  void addEq(ENode* n1, ENode* n2);
  /** Undo an addEq; invoked from the trail. */
  void undoAddEq(ENode* r1, size_t r2NumParents);

  /** Queue the merge of the classes of lhs and rhs, for propagateEqs. */
  void pushEq(ENode* lhs, ENode* rhs)
  {
    if (lhs->getRoot() != rhs->getRoot())
    {
      d_eqPropagationQueue.push_back(NewEq(lhs, rhs));
    }
  }

  bool hasPendingEqs() const { return !d_eqPropagationQueue.empty(); }

  void clearPendingEqs() { d_eqPropagationQueue.clear(); }

  /** Merge the queued equalities; returns false on a conflict. */
  bool propagateEqs();

  ENode* getCgRoot(ENode* n) const
  {
    if (!n->usesCgTable())
    {
      return n;
    }
    // Fast path: if n is already the congruence root, avoid the table lookup.
    // This matters because getCgRoot is on every generation lookup.
    if (n->isCgr())
    {
      return n;
    }
    ENode* r = d_cgTable.find(n);
    return r != nullptr ? r : n;
  }

  /** An enode congruent to decl(args), or null if there is none. */
  ENode* getENodeEqTo(TNode decl,
                      bool commutative,
                      size_t numArgs,
                      ENode* const* args);

  // -------------------------------- the merges of cvc5's master equality
  //                                  engine
  /** Take the merges of master, which then notifies them. */
  void setMasterEqualityEngine(theory::eq::EqualityEngine* master)
  {
    d_masterEe = master;
  }
  /** The master equality engine merged the classes of t1 and t2. */
  void notifyMasterMerge(TNode t1, TNode t2);
  /**
   * Queue the merges of the master equality engine notified since the last
   * call, and those of the terms internalized since then, for propagateEqs.
   */
  void applyMasterMerges();
  /** The SAT context popped: the merges notified and not applied are void. */
  void clearPendingMasterMerges() { d_pendingMerges.clear(); }

 private:
  struct NewEq
  {
    ENode* d_lhs;
    ENode* d_rhs;
    NewEq(ENode* lhs, ENode* rhs) : d_lhs(lhs), d_rhs(rhs) {}
  };

  /** The trail object that undoes mkENode. */
  class MkENodeTrail : public Trail
  {
   public:
    MkENodeTrail(EGraph& eg) : d_eg(eg) {}
    void undo() override { d_eg.undoMkENode(); }

   private:
    EGraph& d_eg;
  };

  void removeParentsFromCgTable(ENode* r1);
  void reinsertParentsIntoCgTable(ENode* r1, ENode* r2);
  void mergeCgcGenerations(ENode* e1, uint32_t e1Generation, ENode* e2);

  void pushNewCongruence(ENode* n1, ENode* n2)
  {
    Assert(n1->d_cg == n2);
    pushEq(n1, n2);
  }

  /** The term of the E-graph recorded for the representative rep, or null. */
  Node masterTermOf(TNode rep) const;
  /** Merge a and b, which the master equality engine made equal, if both
   * are internalized. */
  void mergeMasterTerms(TNode a, TNode b);

  /** The core, which owns this object. */
  SmtContext& d_ctx;
  /** The trail stack of the core, and the memory of the enodes. */
  TrailStack& d_trailStack;
  Statistics& d_stats;

  /** The expressions already internalized as enodes. */
  std::vector<Node> d_eInternalizedStack;
  /** Maps the id of a term to its enode. */
  App2ENode d_app2ENode;
  /** Maps a declaration id to the enodes with that declaration. */
  std::vector<ENodeVector> d_decl2ENodes;
  std::unordered_map<TNode, uint32_t> d_declIds;
  ENodeVector d_emptyVector;
  CgTable d_cgTable;
  /**
   * A temporary cache of parent generations, held between
   * removeParentsFromCgTable and reinsertParentsIntoCgTable.
   */
  std::vector<std::pair<ENode*, uint32_t>> d_r1ParentGenerations;
  std::vector<NewEq> d_eqPropagationQueue;
  TmpENode d_tmpENode;
  MkENodeTrail d_mkENodeTrail;

  /**
   * The master equality engine, which collects the terms and merges of the
   * equality engines of cvc5's theories, or null. Its merges are queued as
   * they are notified (notifyMasterMerge), and applied at the next check
   * (applyMasterMerges). The master equality engine keeps no reasons, so the
   * core cannot explain these merges, and it does not need to: the core
   * keeps no explanations.
   */
  theory::eq::EqualityEngine* d_masterEe;
  /**
   * For a representative of the master equality engine, a term of the
   * E-graph in its class, in the SAT context.
   */
  context::CDHashMap<Node, Node> d_masterTerm;
  /**
   * How many of the terms internalized were looked up in the master equality
   * engine. In the SAT context, as the core's scopes are.
   */
  context::CDO<size_t> d_masterIdx;
  /**
   * The merges notified since the last check, as the representative that
   * survived and the one that was merged into it.
   */
  std::vector<std::pair<Node, Node>> d_pendingMerges;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIERS__EGRAPH_H */

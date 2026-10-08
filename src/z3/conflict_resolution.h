/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Conflict resolution: deriving a lemma from a conflict.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_conflict_resolution.h, and recast in cvc5 style. The proof
 * production half of Z3's conflict resolution is not ported.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__CONFLICT_RESOLUTION_H
#define CVC5__Z3__CONFLICT_RESOLUTION_H

#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "z3/b_justification.h"
#include "z3/bool_var_data.h"
#include "z3/dyn_ack.h"
#include "z3/enode.h"
#include "z3/justification.h"
#include "z3/params.h"
#include "z3/util/approx_set.h"
#include "z3/watch_list.h"

namespace cvc5::internal {
namespace z3 {

/** An approximation of a set of scope levels. */
using LevelApproxSet = ApproxSetTpl<uint32_t, UnsignedToUnsigned, uint32_t>;

/**
 * Conflict resolution, implementing the first-UIP strategy.
 *
 * Given a conflict, this walks the implication graph backwards from the
 * conflict level to the first unique implication point, collecting the
 * antecedents. The antecedents of a theory propagation are obtained from its
 * Justification, and the antecedents of an equality are read off the
 * E-graph's transitivity forest, which is what lets the same mechanism handle
 * both Boolean and congruence reasoning.
 */
class ConflictResolution
{
  struct ENodePairHash
  {
    size_t operator()(const ENodePair& p) const
    {
      return reinterpret_cast<size_t>(p.first) * 31
             + reinterpret_cast<size_t>(p.second);
    }
  };

  using ENodePairSet = std::unordered_set<ENodePair, ENodePairHash>;

 public:
  ConflictResolution(SmtContext& ctx,
                     DynAckManager& dackManager,
                     const Params& params,
                     const LiteralVector& assignedLiterals,
                     std::vector<WatchList>& watches);

  virtual ~ConflictResolution() = default;

  void setup() {}

  /**
   * Resolve the given conflict, storing the resulting lemma. Returns false if
   * the conflict cannot be resolved because it sits at the search level, which
   * means the problem is unsatisfiable.
   */
  virtual bool resolve(BJustification conflict, Literal notL);

  SmtContext& getContext() { return d_ctx; }

  uint32_t getNewScopeLvl() const { return d_newScopeLvl; }

  uint32_t getLemmaInternLvl() const { return d_lemmaIscopeLvl; }

  size_t getLemmaNumLiterals() const { return d_lemma.size(); }

  Literal* getLemmaLiterals() { return d_lemma.data(); }

  std::vector<Node>& getLemmaAtoms() { return d_lemmaAtoms; }

  void releaseLemmaAtoms() { d_lemmaAtoms.clear(); }

  LiteralVector::const_iterator beginUnsatCore() const
  {
    return d_assumptions.begin();
  }

  LiteralVector::const_iterator endUnsatCore() const
  {
    return d_assumptions.end();
  }

  // ------------------------------------- the marking interface used by
  //                                       Justification::getAntecedents
  void markJustification(Justification* js)
  {
    if (!js->isMarked())
    {
      js->setMark();
      d_todoJs.push_back(js);
    }
  }

  void markEq(ENode* n1, ENode* n2)
  {
    if (n1 != n2)
    {
      if (n1->getOwnerId() > n2->getOwnerId())
      {
        std::swap(n1, n2);
      }
      ENodePair p(n1, n2);
      if (d_alreadyProcessedEqs.insert(p).second)
      {
        d_todoEqs.push_back(p);
      }
    }
  }

  void markLiteral(Literal l)
  {
    Assert(d_antecedents != nullptr);
    d_antecedents->push_back(l);
  }

  void markJustifiedEq(ENode* lhs, ENode* rhs, EqJustification js)
  {
    eqJustification2Literals(lhs, rhs, js);
  }
  // ------------------------------------- end marking interface

  /** The antecedent literals of a justification object. */
  void justification2Literals(Justification* js, LiteralVector& result);

  /** The antecedent literals of the equality n1 = n2. */
  void eq2Literals(ENode* n1, ENode* n2, LiteralVector& result);

  void reset();

  /** Build the unsat core of a conflict at the search level. */
  void mkUnsatCore(BJustification conflict, Literal notL);

 protected:
  /** Mark, or unmark, all enodes on the proof branch starting at n. */
  template <bool Set>
  void markENodesInTrans(ENode* n);
  ENode* findCommonAncestor(ENode* n1, ENode* n2);
  void eqJustification2Literals(ENode* lhs, ENode* rhs, EqJustification js);
  void eqBranch2Literals(ENode* n1, ENode* n2);
  void eq2Literals(ENode* n1, ENode* n2);
  void justification2LiteralsCore(Justification* js, LiteralVector& result);
  void processJustifications();
  void unmarkJustifications(size_t oldJsQhead);

  uint32_t getJustificationMaxLvl(Justification* js);
  uint32_t getMaxLvl(Literal consequent, BJustification js);
  size_t skipLiteralsAboveConflictLevel();
  void processAntecedent(Literal antecedent, size_t& numMarks);
  void processJustification(Literal consequent,
                            Justification* js,
                            size_t& numMarks);

  LevelApproxSet getLemmaApproxLevelSet();
  void resetUnmark(size_t oldSize);
  void resetUnmarkAndJustifications(size_t oldSize, size_t oldJsQhead);
  bool processAntecedentForMinimization(Literal antecedent);
  bool processJustificationForMinimization(Justification* js);
  bool impliedByMarked(Literal lit);
  void minimizeLemma();

  void processAntecedentForUnsatCore(Literal antecedent);
  void processJustificationForUnsatCore(Justification* js);

  bool initializeResolve(BJustification conflict,
                         Literal notL,
                         BJustification& js,
                         Literal& consequent);
  void finalizeResolve(BJustification conflict, Literal notL);

  const Params& d_params;
  SmtContext& d_ctx;
  DynAckManager& d_dynAckManager;
  const LiteralVector& d_assignedLiterals;

  uint32_t d_conflictLvl;

  LiteralVector d_lemma;
  std::vector<Node> d_lemmaAtoms;
  uint32_t d_newScopeLvl;
  uint32_t d_lemmaIscopeLvl;

  JustificationVector d_todoJs;
  size_t d_todoJsQhead;
  ENodePairVector d_todoEqs;
  ENodePairSet d_alreadyProcessedEqs;

  LiteralVector* d_antecedents;

  /** The watch lists, used to implement subsumption resolution. */
  std::vector<WatchList>& d_watches;

  LiteralVector d_tmpLiteralVector;

  BoolVarVector d_unmark;
  BoolVarVector d_lemmaMinStack;
  LevelApproxSet d_lvlSet;

  LiteralVector d_assumptions;
};

inline void markLiterals(ConflictResolution& cr,
                         size_t sz,
                         const Literal* ls)
{
  for (size_t i = 0; i < sz; ++i)
  {
    cr.markLiteral(ls[i]);
  }
}

ConflictResolution* mkConflictResolution(
    SmtContext& ctx,
    DynAckManager& dackManager,
    const Params& params,
    const LiteralVector& assignedLiterals,
    std::vector<WatchList>& watches);

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__CONFLICT_RESOLUTION_H */

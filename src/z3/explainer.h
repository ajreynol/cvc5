/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The explanation of justifications and equalities as literals.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), the
 * explanation half of file src/smt/smt_conflict_resolution.{h,cpp}, and recast
 * in cvc5 style. In Z3 this is part of conflict_resolution; here it is
 * separate because it reads the E-graph, while the rest of conflict
 * resolution only reads the Boolean search.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__EXPLAINER_H
#define CVC5__Z3__EXPLAINER_H

#include <unordered_set>
#include <vector>

#include "z3/dyn_ack.h"
#include "z3/enode.h"
#include "z3/eq_justification.h"
#include "z3/justification.h"
#include "z3/util/literal.h"

namespace cvc5::internal {
namespace z3 {

class SmtContext;

/**
 * Explains justifications and equalities as the literals they depend on.
 *
 * The antecedents of a theory propagation are obtained from its
 * Justification, which marks them through the methods below, and the
 * antecedents of an equality are read off the E-graph's transitivity forest.
 * This is the interface through which conflict resolution, on the side of the
 * Boolean search, learns about the reasoning of the E-graph and the theories.
 *
 * Explanations share their caches until rollback is called: a justification
 * or an equality that was explained since then is not explained again. This
 * is what lets conflict resolution explain each antecedent once per conflict.
 */
class Explainer
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
  Explainer(SmtContext& ctx, DynAckManager& dackManager);

  SmtContext& getContext() { return d_ctx; }

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

  /**
   * Append to result the antecedent literals of js, skipping the
   * justifications and equalities explained since the last rollback.
   */
  void explain(Justification* js, LiteralVector& result);

  /** The position to roll back to, in order to undo later explanations. */
  size_t getCheckpoint() const { return d_todoJsQhead; }

  /**
   * Forget the justifications explained since checkpoint, so that they are
   * explained again when next asked. The cache of explained equalities is
   * cleared entirely.
   */
  void rollback(size_t checkpoint);

  /** True if nothing has been explained since the last rollback to 0. */
  bool isClear() const
  {
    return d_todoJs.empty() && d_todoJsQhead == 0 && d_todoEqs.empty();
  }

  /** The antecedent literals of a justification object, from a clear state. */
  void justification2Literals(Justification* js, LiteralVector& result);

  /** The antecedent literals of the equality n1 = n2, from a clear state. */
  void eq2Literals(ENode* n1, ENode* n2, LiteralVector& result);

 private:
  /** Mark, or unmark, all enodes on the proof branch starting at n. */
  template <bool Set>
  void markENodesInTrans(ENode* n);
  ENode* findCommonAncestor(ENode* n1, ENode* n2);
  void eqJustification2Literals(ENode* lhs, ENode* rhs, EqJustification js);
  void eqBranch2Literals(ENode* n1, ENode* n2);
  void eq2Literals(ENode* n1, ENode* n2);
  void processJustifications();

  SmtContext& d_ctx;
  DynAckManager& d_dynAckManager;

  JustificationVector d_todoJs;
  size_t d_todoJsQhead;
  ENodePairVector d_todoEqs;
  ENodePairSet d_alreadyProcessedEqs;

  LiteralVector* d_antecedents;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__EXPLAINER_H */

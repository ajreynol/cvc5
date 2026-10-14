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
 * production half of Z3's conflict resolution is not ported, and the
 * explanation of justifications and equalities is in explainer.h.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__CONFLICT_RESOLUTION_H
#define CVC5__Z3__CONFLICT_RESOLUTION_H

#include <vector>

#include "expr/node.h"
#include "z3/b_justification.h"
#include "z3/bool_var_data.h"
#include "z3/justification.h"
#include "z3/params.h"
#include "z3/util/approx_set.h"

namespace cvc5::internal {
namespace z3 {

class Explainer;
class PropCore;

/** An approximation of a set of scope levels. */
using LevelApproxSet = ApproxSetTpl<uint32_t, UnsignedToUnsigned, uint32_t>;

/**
 * Conflict resolution, implementing the first-UIP strategy.
 *
 * Given a conflict, this walks the implication graph backwards from the
 * conflict level to the first unique implication point, collecting the
 * antecedents. The antecedents of a theory propagation or of an equality are
 * obtained from the Explainer, which is what lets the same mechanism handle
 * both Boolean and congruence reasoning while reading only the Boolean search
 * itself.
 */
class ConflictResolution
{
 public:
  ConflictResolution(PropCore& core,
                     Explainer& explainer,
                     const Params& params,
                     const LiteralVector& assignedLiterals);

  virtual ~ConflictResolution() = default;

  void setup() {}

  /**
   * Resolve the given conflict, storing the resulting lemma. Returns false if
   * the conflict cannot be resolved because it sits at the search level, which
   * means the problem is unsatisfiable.
   */
  virtual bool resolve(BJustification conflict, Literal notL);

  uint32_t getNewScopeLvl() const { return d_newScopeLvl; }

  uint32_t getLemmaInternLvl() const { return d_lemmaIscopeLvl; }

  size_t getLemmaNumLiterals() const { return d_lemma.size(); }

  Literal* getLemmaLiterals() { return d_lemma.data(); }

  std::vector<Node>& getLemmaAtoms() { return d_lemmaAtoms; }

  void releaseLemmaAtoms() { d_lemmaAtoms.clear(); }

  void reset();

 protected:
  uint32_t getJustificationMaxLvl(Justification* js);
  uint32_t getMaxLvl(Literal consequent, BJustification js);
  size_t skipLiteralsAboveConflictLevel();
  void processAntecedent(Literal antecedent, size_t& numMarks);
  void processJustification(Literal consequent,
                            Justification* js,
                            size_t& numMarks);

  LevelApproxSet getLemmaApproxLevelSet();
  void resetUnmark(size_t oldSize);
  void resetUnmarkAndJustifications(size_t oldSize, size_t oldCheckpoint);
  bool processAntecedentForMinimization(Literal antecedent);
  bool processJustificationForMinimization(Justification* js);
  bool impliedByMarked(Literal lit);
  void minimizeLemma();

  bool initializeResolve(BJustification conflict,
                         Literal notL,
                         BJustification& js,
                         Literal& consequent);
  void finalizeResolve(BJustification conflict, Literal notL);

  const Params& d_params;
  /** The propositional side, whose conflicts this resolves. */
  PropCore& d_core;
  Explainer& d_explainer;
  const LiteralVector& d_assignedLiterals;

  uint32_t d_conflictLvl;

  LiteralVector d_lemma;
  std::vector<Node> d_lemmaAtoms;
  uint32_t d_newScopeLvl;
  uint32_t d_lemmaIscopeLvl;

  LiteralVector d_tmpLiteralVector;

  BoolVarVector d_unmark;
  BoolVarVector d_lemmaMinStack;
  LevelApproxSet d_lvlSet;
};

ConflictResolution* mkConflictResolution(PropCore& core,
                                         Explainer& explainer,
                                         const Params& params,
                                         const LiteralVector& assignedLiterals);

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__CONFLICT_RESOLUTION_H */

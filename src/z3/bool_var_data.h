/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Per-Boolean-variable data of the ported Z3 SMT core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/smt_bool_var_data.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__BOOL_VAR_DATA_H
#define CVC5__Z3__BOOL_VAR_DATA_H

#include "z3/b_justification.h"
#include "z3/types.h"

namespace cvc5::internal {
namespace z3 {

struct BoolVarData
{
 private:
  BJustification d_justification;

 public:
  /** the scope level at which the variable was assigned */
  uint32_t d_scopeLvl : 24;
  uint32_t d_mark : 1;
  uint32_t d_assumption : 1;
  uint32_t d_phaseAvailable : 1;
  uint32_t d_phase : 1;

 private:
  uint32_t d_eq : 1;
  /**
   * If true, try the positive phase first when case splitting on this
   * variable, rather than consulting the phase selection heuristic.
   */
  uint32_t d_trueFirst : 1;
  /** has an enode associated with it */
  uint32_t d_enode : 1;
  /** true if the variable is attached to a quantifier */
  uint32_t d_quantifier : 1;
  /** the scope level at which the variable was internalized */
  uint32_t d_iscopeLvl : 23;
  /**
   * the disjunction of d_eq, d_enode, d_quantifier and whether a theory is
   * notified
   */
  uint32_t d_atom : 1;
  /**
   * One plus the id of the theory to notify, or zero for none. Note the
   * offset: cvc5's first TheoryId is zero, whereas Z3 reserves family id zero
   * for the operators the core handles itself.
   */
  uint32_t d_notifyTheory : 8;

  void updateAtomFlag()
  {
    d_atom = d_eq || d_notifyTheory != 0 || d_quantifier || d_enode;
  }

 public:
  uint32_t getInternLevel() const { return d_iscopeLvl; }

  BJustification justification() const { return d_justification; }

  void setAxiom() { d_justification = BJustification::mkAxiom(); }

  void setNullJustification() { d_justification = s_nullBJustification; }

  void setJustification(const BJustification& j) { d_justification = j; }

  bool isAtom() const { return d_atom; }

  TheoryId getTheory() const
  {
    return d_notifyTheory == 0 ? s_nullTheoryId
                               : static_cast<TheoryId>(d_notifyTheory - 1);
  }

  bool isTheoryAtom() const { return d_notifyTheory != 0; }

  void setNotifyTheory(TheoryId thid)
  {
    Assert(thid >= 0 && thid < 255);
    d_notifyTheory = static_cast<uint32_t>(thid) + 1;
    d_atom = true;
  }

  void resetNotifyTheory()
  {
    d_notifyTheory = 0;
    updateAtomFlag();
  }

  bool isENode() const { return d_enode; }

  void setENodeFlag()
  {
    d_enode = true;
    d_atom = true;
  }

  void resetENodeFlag()
  {
    d_enode = false;
    updateAtomFlag();
  }

  bool isQuantifier() const { return d_quantifier; }

  void setQuantifierFlag()
  {
    d_quantifier = true;
    d_atom = true;
  }

  bool isEq() const { return d_eq; }

  void setEqFlag()
  {
    d_eq = true;
    d_atom = true;
  }

  void resetEqFlag()
  {
    d_eq = false;
    updateAtomFlag();
  }

  bool tryTrueFirst() const { return d_trueFirst; }

  void setTrueFirstFlag() { d_trueFirst = true; }

  void resetTrueFirstFlag() { d_trueFirst = false; }

  void init(uint32_t iscopeLvl)
  {
    d_justification = s_nullBJustification;
    d_scopeLvl = 0;
    d_mark = false;
    d_assumption = false;
    d_phaseAvailable = false;
    d_phase = false;
    d_iscopeLvl = iscopeLvl;
    d_eq = false;
    d_trueFirst = false;
    d_notifyTheory = 0;
    d_enode = false;
    d_quantifier = false;
    d_atom = false;
  }
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__BOOL_VAR_DATA_H */

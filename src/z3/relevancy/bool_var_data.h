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

#ifndef CVC5__Z3__RELEVANCY__BOOL_VAR_DATA_H
#define CVC5__Z3__RELEVANCY__BOOL_VAR_DATA_H

namespace cvc5::internal {
namespace z3 {

struct BoolVarData
{
 private:
  uint32_t d_eq : 1;
  /** has an enode associated with it */
  uint32_t d_enode : 1;
  /** true if the variable is attached to a quantifier */
  uint32_t d_quantifier : 1;
  /** the scope level at which the variable was internalized */
  uint32_t d_iscopeLvl : 23;

 public:
  uint32_t getInternLevel() const { return d_iscopeLvl; }

  bool isAtom() const { return d_eq || d_quantifier || d_enode; }

  bool isENode() const { return d_enode; }

  void setENodeFlag() { d_enode = true; }

  void resetENodeFlag() { d_enode = false; }

  bool isQuantifier() const { return d_quantifier; }

  void setQuantifierFlag() { d_quantifier = true; }

  bool isEq() const { return d_eq; }

  void setEqFlag() { d_eq = true; }

  void init(uint32_t iscopeLvl)
  {
    d_iscopeLvl = iscopeLvl;
    d_eq = false;
    d_enode = false;
    d_quantifier = false;
  }
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__RELEVANCY__BOOL_VAR_DATA_H */

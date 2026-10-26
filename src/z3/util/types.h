/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Basic types for the ported Z3 SMT engine.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * files src/smt/smt_types.h and src/util/lbool.h, and recast in cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__TYPES_H
#define CVC5__Z3__UTIL__TYPES_H

#include <cstdint>
#include <ostream>
#include <vector>

namespace cvc5::internal {
namespace z3 {

/**
 * A lifted Boolean. The numeric values matter: negation is arithmetic
 * negation, and the ordering FALSE < UNDEF < TRUE is relied upon.
 */
enum LBool : int8_t
{
  L_FALSE = -1,
  L_UNDEF = 0,
  L_TRUE = 1
};

inline LBool operator~(LBool lb)
{
  return static_cast<LBool>(-static_cast<int8_t>(lb));
}

std::ostream& operator<<(std::ostream& out, LBool b);

class ENode;

using ENodeVector = std::vector<ENode*>;

class SmtContext;

/** The outcome of a theory's final check. */
enum FinalCheckStatus
{
  /** The theory is satisfied with the current assignment. */
  FC_DONE,
  /** The theory made progress and wants the search to continue. */
  FC_CONTINUE
};

std::ostream& operator<<(std::ostream& out, FinalCheckStatus st);

/**
 * Store val at index i, growing v with def as needed. This is Z3's
 * vector::setx.
 */
template <typename T>
void setx(std::vector<T>& v, size_t i, const T& val, const T& def)
{
  if (i >= v.size())
  {
    v.resize(i + 1, def);
  }
  v[i] = val;
}

/** Read index i, or def if i is out of range. This is Z3's vector::get. */
template <typename T>
const T& getx(const std::vector<T>& v, size_t i, const T& def)
{
  return i < v.size() ? v[i] : def;
}

/** Grow v to at least size sz, filling with def. */
template <typename T>
void reservex(std::vector<T>& v, size_t sz, const T& def)
{
  if (v.size() < sz)
  {
    v.resize(sz, def);
  }
}

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__TYPES_H */

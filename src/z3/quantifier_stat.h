/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Per-quantifier statistics, which the instantiation heuristics key on.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * files src/ast/quantifier_stat.h and src/ast/quantifier_stat.cpp, recast in
 * cvc5 style.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__QUANTIFIER_STAT_H
#define CVC5__Z3__QUANTIFIER_STAT_H

#include <cstdint>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "z3/util/region.h"

namespace cvc5::internal {
namespace z3 {

class QuantifierStatGen;

/**
 * Statistics of one quantifier. The instantiation cost function and the
 * matching-loop heuristics are expressed in terms of these numbers, so they
 * are part of what decides how many instances get produced.
 */
class QuantifierStat
{
 public:
  uint32_t getSize() const { return d_size; }
  uint32_t getDepth() const { return d_depth; }
  uint32_t getGeneration() const { return d_generation; }
  /** The product of the sizes of the clauses this quantifier creates. */
  uint32_t getCaseSplitFactor() const { return d_caseSplitFactor; }
  uint32_t getNumNestedQuantifiers() const { return d_numNestedQuantifiers; }
  uint32_t getNumInstances() const { return d_numInstances; }
  uint32_t getNumInstancesSimplifyTrue() const
  {
    return d_numInstancesSimplifyTrue;
  }
  uint32_t getNumInstancesCheckerSat() const
  {
    return d_numInstancesCheckerSat;
  }
  uint32_t getNumInstancesCurrSearch() const
  {
    return d_numInstancesCurrSearch;
  }
  uint32_t& getNumInstancesCurrBranch() { return d_numInstancesCurrBranch; }

  void incNumInstancesSimplifyTrue() { d_numInstancesSimplifyTrue++; }
  void incNumInstancesCheckerSat() { d_numInstancesCheckerSat++; }

  void incNumInstances()
  {
    d_numInstances++;
    d_numInstancesCurrSearch++;
  }

  void incNumInstancesCurrBranch() { d_numInstancesCurrBranch++; }

  void resetNumInstancesCurrSearch() { d_numInstancesCurrSearch = 0; }

  void updateMaxGeneration(uint32_t g)
  {
    if (d_maxGeneration < g)
    {
      d_maxGeneration = g;
    }
  }

  uint32_t getMaxGeneration() const { return d_maxGeneration; }

  void updateMaxCost(float c)
  {
    if (d_maxCost < c)
    {
      d_maxCost = c;
    }
  }

  float getMaxCost() const { return d_maxCost; }

 private:
  friend class QuantifierStatGen;

  QuantifierStat(uint32_t generation);

  uint32_t d_size;
  uint32_t d_depth;
  uint32_t d_generation;
  uint32_t d_caseSplitFactor;
  uint32_t d_numNestedQuantifiers;
  uint32_t d_numInstances;
  uint32_t d_numInstancesCheckerSat;
  uint32_t d_numInstancesSimplifyTrue;
  uint32_t d_numInstancesCurrSearch;
  uint32_t d_numInstancesCurrBranch;
  /** The maximum generation of an instance. */
  uint32_t d_maxGeneration;
  float d_maxCost;
};

/** Computes the statistics of a quantifier. */
class QuantifierStatGen
{
 public:
  QuantifierStatGen(Region& r);

  QuantifierStat* operator()(TNode q, uint32_t generation);

 private:
  struct Entry
  {
    Node d_expr;
    uint32_t d_depth : 31;
    /** track only the depth of this entry */
    uint32_t d_depthOnly : 1;
    Entry() : d_depth(0), d_depthOnly(false) {}
    Entry(TNode n, uint32_t depth = 0, bool depthOnly = false)
        : d_expr(n), d_depth(depth), d_depthOnly(depthOnly ? 1 : 0)
    {
    }
  };

  void reset();

  Region& d_region;
  /** Maps an expression to the maximum depth at which it was reached. */
  std::unordered_map<Node, uint32_t> d_alreadyFound;
  std::vector<Entry> d_todo;
  /**
   * An approximation of the case split factor, saturating rather than
   * overflowing. This is Z3's approx_nat.
   */
  uint64_t d_caseSplitFactor;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIER_STAT_H */

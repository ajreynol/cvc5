/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inline single-constructor datatypes.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__DT_ELIM_H
#define CVC5__PREPROCESSING__PASSES__DT_ELIM_H

#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * Eliminate product datatypes by translating each type/term to a vector of
 * component types/terms. For example, for D = C(Int, Bool), x : D becomes
 * (x_0 : Int, x_1 : Bool), and f : D -> D becomes two functions with domain
 * Int x Bool. A datatype with a single nullary constructor becomes the empty
 * vector, including in function domains and ranges.
 *
 * Other datatypes are rebuilt when their fields change. Recursive references
 * are resolved together, after inlining product fields. Parametric datatypes
 * are translated at each concrete instantiation.
 *
 * Quantifier annotations are translated with the body. Components of a pattern
 * term remain together in a multi-pattern; separate pattern alternatives are
 * preserved. No-pattern annotations exclude each component separately. Empty
 * patterns disappear when all their terms have nullary product types.
 *
 * Arrays, sets, sequences, and other type constructors cannot contain a type
 * that changes. Codatatypes requiring translation, nested recursive datatypes,
 * and unsupported operators on translated types raise LogicException.
 * Model reconstruction is not supported.
 */
class DtElim : public PreprocessingPass
{
 public:
  DtElim(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(AssertionPipeline* assertions) override;

 private:
  using Types = std::vector<TypeNode>;
  using Terms = std::vector<Node>;

  /** Get the component types, discovering and rebuilding datatypes as needed.
   */
  const Types& convertType(TypeNode tn);
  /** Flatten types after installing placeholders for remaining datatypes. */
  const Types& flattenType(TypeNode tn, std::unordered_set<TypeNode>& active);
  /** Does translating tn change its representation? */
  bool changesType(TypeNode tn);
  /** Translate n and its subterms, with a shared cache. */
  const Terms& convert(Node n);
  /** Translate n assuming its children (and UF operator) are cached. */
  Terms convertNode(Node n);
  /** Flatten the translations of children [begin, end). */
  Terms children(Node n, size_t begin, size_t end) const;
  /** Component equality, including equality of empty products. */
  Node equal(const Terms& a, const Terms& b) const;
  /** Get the interval of components for a constructor field. */
  std::pair<size_t, size_t> fieldRange(TypeNode tn, size_t ci, size_t si);

  /**
   * These caches are independent of assertions and persist across push/pop.
   * In particular, a symbol must keep the same components across check-sat.
   */
  std::unordered_map<TypeNode, Types> d_types;
  std::unordered_map<Node, Terms> d_terms;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif

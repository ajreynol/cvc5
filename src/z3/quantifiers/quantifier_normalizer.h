/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The quantified variables of the ported Z3 core.
 *
 * The ported core uses cvc5's Node as its AST; there is no port of Z3's
 * ast_manager. Z3 quantifier bodies use de Bruijn variables, and mam.cpp
 * binds pattern variables by index. cvc5 uses named bound variables, so two
 * quantifiers whose patterns are identical up to renaming would compile to
 * distinct E-matching code trees and lose all sharing. QuantifierNormalizer
 * rewrites quantifiers over a canonical pool of placeholder variables indexed
 * by de Bruijn *level*, which is both alpha-invariant (restoring Z3's sharing)
 * and capture-free.
 *
 * The other part of Z3's term representation without a direct cvc5
 * counterpart, its congruence keys, is getDecl in enode.h.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__QUANTIFIERS__QUANTIFIER_NORMALIZER_H
#define CVC5__Z3__QUANTIFIERS__QUANTIFIER_NORMALIZER_H

#include <unordered_map>
#include <vector>

#include "expr/attribute.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace z3 {

/**
 * Attribute holding one plus the de Bruijn level of a canonical quantified
 * variable. Zero (the default) means the node is not one.
 */
struct QuantVarLevelTag
{
};
using QuantVarLevelAttr = expr::Attribute<QuantVarLevelTag, uint64_t>;

/** True if n is a canonical quantified variable. This is Z3's is_var. */
inline bool isVar(TNode n)
{
  return n.getKind() == Kind::BOUND_VARIABLE
         && n.getAttribute(QuantVarLevelAttr()) != 0;
}

/** The de Bruijn level of a canonical quantified variable. */
inline uint32_t varIndex(TNode n)
{
  Assert(isVar(n));
  return static_cast<uint32_t>(n.getAttribute(QuantVarLevelAttr()) - 1);
}

/** True if n is a quantifier. This is Z3's is_quantifier. */
inline bool isQuantifier(TNode n)
{
  Kind k = n.getKind();
  return k == Kind::FORALL || k == Kind::EXISTS;
}

/**
 * True if n is a term the core may build an enode for: anything that is
 * neither a quantified variable nor a quantifier. Note that, as in Z3, leaves
 * count as nullary applications.
 */
inline bool isApp(TNode n) { return !isQuantifier(n) && !isVar(n); }

/**
 * Rewrites quantifiers into the canonical de Bruijn-level form the core and
 * the E-matching engine expect. See the comment at the top of this file.
 */
class QuantifierNormalizer
{
 public:
  QuantifierNormalizer(NodeManager* nm);

  /**
   * Return n with every quantifier subterm rewritten over canonical
   * quantified variables. Alpha-equivalent quantifiers are mapped to the same
   * node.
   */
  Node normalize(TNode n);

  /** The canonical quantified variable for de Bruijn level idx and type tn. */
  Node mkVar(uint32_t idx, const TypeNode& tn);

 private:
  /**
   * Normalize n, which sits under depth enclosing canonical binders, under the
   * substitution subs mapping the bound variables of those binders to their
   * canonical replacements.
   */
  Node normalizeRec(TNode n,
                    uint32_t depth,
                    std::unordered_map<Node, Node>& subs);

  /** Normalize the pattern list child of a quantifier. */
  Node normalizePatternList(TNode ipl,
                            uint32_t depth,
                            std::unordered_map<Node, Node>& subs);

  NodeManager* d_nm;
  /** Memoization of normalize, which is applied to whole assertions. */
  std::unordered_map<Node, Node> d_cache;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIERS__QUANTIFIER_NORMALIZER_H */

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The bridge between cvc5's Node and the term interface the ported Z3 core is
 * written against.
 *
 * The ported core uses cvc5's Node as its AST; there is no port of Z3's
 * ast_manager. Only two aspects of Z3's term representation have no direct
 * cvc5 counterpart, and they are handled here:
 *
 * (1) Congruence keys. Z3 keys congruence closure on func_decl*. cvc5 splits
 *     that information between the Kind and, for parameterized kinds, an
 *     operator node. getDecl() recovers a single node that plays the role of
 *     Z3's func_decl*.
 *
 * (2) Quantified variables. Z3 quantifier bodies use de Bruijn variables, and
 *     mam.cpp binds pattern variables by index. cvc5 uses named bound
 *     variables, so two quantifiers whose patterns are identical up to
 *     renaming would compile to distinct E-matching code trees and lose all
 *     sharing. QuantifierNormalizer rewrites quantifiers over a canonical
 *     pool of placeholder variables indexed by de Bruijn *level*, which is
 *     both alpha-invariant (restoring Z3's sharing) and capture-free.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__AST_H
#define CVC5__Z3__AST_H

#include <unordered_map>
#include <vector>

#include "expr/attribute.h"
#include "expr/node.h"
#include "z3/types.h"

namespace cvc5::internal {

class Env;
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

/** True if n is an equality. */
inline bool isEq(TNode n) { return n.getKind() == Kind::EQUAL; }

/**
 * The congruence key of n: the node that stands in for Z3's func_decl*. For
 * parameterized kinds this is the operator, for kinds with a built-in operator
 * it is that operator, and for leaves it is n itself (a leaf is congruent to
 * nothing but itself).
 */
TNode getDecl(TNode n);

/**
 * The theory that owns n's operator, playing the role of Z3's
 * func_decl::get_family_id(). Uninterpreted functions and sorts are owned by
 * THEORY_UF, whose congruence reasoning the core performs itself.
 */
TheoryId familyIdOf(TNode n);

/**
 * True if n is a binary application of a commutative operator, in which case
 * the congruence table normalizes the argument order.
 */
bool isCommutative(TNode n);

/** The number of variables bound by quantifier q. */
inline size_t getNumDecls(TNode q)
{
  Assert(isQuantifier(q));
  return q[0].getNumChildren();
}

/** The body of quantifier q. */
inline TNode getQuantBody(TNode q)
{
  Assert(isQuantifier(q));
  return q[1];
}

/** True if quantifier q carries an explicit pattern annotation. */
bool hasPatterns(TNode q);

/**
 * The explicit patterns of q, each as the vector of terms of a (possibly
 * multi-) pattern. Empty if q has no pattern annotation.
 */
void getPatterns(TNode q, std::vector<std::vector<Node>>& patterns);

/** The ":no-pattern" annotations of q. */
void getNoPatterns(TNode q, std::vector<Node>& noPatterns);

/**
 * The instantiation weight of q, from its ":weight" annotation, defaulting to
 * zero as in Z3. The weight is a term of the quantifier instantiation cost
 * function.
 */
/** Z3's default quantifier weight. */
constexpr uint32_t s_defaultWeight = 1;

uint32_t getWeight(TNode q);

/**
 * Set the weight of q, as Z3's pattern inference does for the quantifiers
 * whose only usable pattern contains arithmetic.
 */
void setWeight(TNode q, uint32_t w);

/** The ":qid" of q as a string, or the empty string if it has none. */
std::string getQid(TNode q);

/** Attribute holding one plus the weight of a quantifier. */
struct QuantWeightTag
{
};
using QuantWeightAttr = expr::Attribute<QuantWeightTag, uint64_t>;

/**
 * Attribute caching the term depth, so that the internalizer's check for
 * "deep" terms is constant time as it is in Z3. Zero means not computed yet;
 * a leaf has depth one.
 */
struct TermDepthTag
{
};
using TermDepthAttr = expr::Attribute<TermDepthTag, uint64_t>;

/** The depth of n: one for a leaf, and one more than its deepest child. */
uint32_t getDepth(TNode n);

/**
 * Rewrites quantifiers into the canonical de Bruijn-level form the core and
 * the E-matching engine expect. See the comment at the top of this file.
 */
/**
 * Rewrites the Boolean connectives Z3's rewriter eliminates before
 * internalization: (=> a b) becomes (or (not a) b), and (xor a b) becomes
 * (not (= a b)). The internalizer's notion of a "gate" is Z3's, which does
 * not cover these two, so they have to be gone by the time it runs.
 */
class ConnectiveNormalizer
{
 public:
  ConnectiveNormalizer(NodeManager* nm, bool eliminateAnd)
      : d_nm(nm), d_eliminateAnd(eliminateAnd)
  {
  }

  Node normalize(TNode n);

 private:
  NodeManager* d_nm;
  /** Whether a conjunction is rewritten as a negated disjunction. */
  bool d_eliminateAnd;
  std::unordered_map<Node, Node> d_cache;
};

/**
 * Runs the rewriter over an assertion, which is Z3's
 * asserted_formulas::m_reduce_asserted_formulas. Z3's reduce() applies it
 * twice -- immediately after NNF and again after pattern inference -- and
 * nnf_cnf applies it to every formula it produces before pushing it. Without
 * it the structure that NNF and skolemization build is never simplified: a
 * disjunct that is itself a disjunction stays nested and costs the core an
 * auxiliary Boolean variable and a gate, a conjunct of a conjunction likewise,
 * and nothing that has become constant is folded away.
 *
 * The ground parts go to cvc5's rewriter. A quantifier is rebuilt from its
 * rewritten body rather than handed to the rewriter whole, because cvc5's
 * quantifiers rewriter restructures quantifiers -- miniscoping, variable
 * elimination, prenexing -- and in Z3 that is the job of separate passes of
 * reduce(), each with its own parameter, not of the rewriter.
 */
class AssertionRewriter
{
 public:
  AssertionRewriter(Env& env) : d_env(env) {}

  Node rewrite(TNode n);

 private:
  Env& d_env;
  std::unordered_map<Node, Node> d_cache;
};

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
  /** Canonical variables, indexed by de Bruijn level then by type. */
  std::vector<std::unordered_map<TypeNode, Node>> d_vars;
  /** Memoization of normalize, which is applied to whole assertions. */
  std::unordered_map<Node, Node> d_cache;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__AST_H */

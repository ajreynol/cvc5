/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The datatypes plugin of the ported Z3 SMT core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), files
 * src/smt/theory_datatype.{h,cpp}, and recast in cvc5 style.
 *
 * Deliberately not ported:
 * - Z3's subterm predicate (a ⊑ b), which has no cvc5counterpart.
 * - The occurs check through arrays, sequences and finite sets. A datatype
 *   whose constructors nest one of those over a datatype marks the search as
 *   model-unsound instead, so a missed cycle never turns into a wrong "sat".
 * - Model value construction via Z3's datatype_factory; getValue builds the
 *   constructor term directly when the class has one.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__THEORY_DATATYPE_H
#define CVC5__Z3__THEORY_DATATYPE_H

#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "z3/theory.h"
#include "z3/util/trail.h"
#include "z3/util/union_find.h"

namespace cvc5::internal {

class DType;
class DTypeConstructor;

namespace z3 {

class TheoryDatatype : public Theory
{
 public:
  TheoryDatatype(SmtContext& ctx);
  ~TheoryDatatype() override;

  const char* getName() const override { return "datatype"; }

  void print(std::ostream& out) const override;

  bool getValue(ENode* n, Node& r) override;

  TrailStack& getTrailStack() { return d_trailStack; }

  // ------------------------------------------- union-find callbacks
  /** v1 is the new root. */
  void mergeEh(TheoryVar v1, TheoryVar v2, TheoryVar, TheoryVar);

  static void afterMergeEh(TheoryVar, TheoryVar, TheoryVar, TheoryVar) {}

  void unmergeEh(TheoryVar, TheoryVar) {}

 protected:
  TheoryVar mkVar(ENode* n) override;
  bool internalizeAtom(TNode atom, bool gateCtx) override;
  bool internalizeTerm(TNode term) override;
  void applySortCnstr(ENode* n, const TypeNode& s) override;
  void newEqEh(TheoryVar v1, TheoryVar v2) override;
  bool useDiseqs() const override { return false; }
  void newDiseqEh(TheoryVar v1, TheoryVar v2) override;
  void assignEh(BoolVar v, bool isTrue) override;
  void relevantEh(TNode n) override;
  void pushScopeEh() override;
  void popScopeEh(size_t numScopes) override;
  FinalCheckStatus finalCheckEh(size_t level) override;
  void resetEh() override;
  bool isShared(TheoryVar v) const override { return false; }

 private:
  /** The state the theory keeps for one equivalence class. */
  struct VarData
  {
    VarData() : d_constructor(nullptr) {}

    /** the recognizers of this class that are being watched */
    std::vector<ENode*> d_recognizers;
    /** the constructor of this class, or null if the class has none */
    ENode* d_constructor;
  };

  static bool isConstructor(TNode n)
  {
    return n.getKind() == Kind::APPLY_CONSTRUCTOR;
  }
  static bool isRecognizer(TNode n)
  {
    return n.getKind() == Kind::APPLY_TESTER;
  }
  static bool isAccessor(TNode n)
  {
    return n.getKind() == Kind::APPLY_SELECTOR;
  }
  static bool isUpdateField(TNode n)
  {
    return n.getKind() == Kind::APPLY_UPDATER;
  }
  static bool isConstructor(const ENode* n)
  {
    return isConstructor(n->getExpr());
  }
  static bool isRecognizer(const ENode* n)
  {
    return isRecognizer(n->getExpr());
  }
  static bool isAccessor(const ENode* n) { return isAccessor(n->getExpr()); }
  static bool isUpdateField(const ENode* n)
  {
    return isUpdateField(n->getExpr());
  }

  /** The index of the constructor of the application n. */
  static size_t constructorIdx(TNode n);
  /** The index of the constructor the tester n recognizes. */
  static size_t recognizerIdx(TNode n);

  /** True if the datatype s mentions itself, possibly through a chain. */
  bool isRecursiveDatatype(const TypeNode& s);
  /** True if s has infinitely many values. */
  static bool isInfinite(const TypeNode& s);
  /** The index of a constructor of s that leads out of the recursion. */
  size_t nonRecConstructorIdx(const TypeNode& s);
  /**
   * Note whether a constructor of s nests a datatype under a collection sort,
   * which the ported occurs check does not follow.
   */
  void checkUnsupportedNesting(const TypeNode& s);

  /** Assert the axiom (antecedent => lhs = rhs); antecedent may be null. */
  void assertEqAxiom(ENode* lhs, TNode rhs, Literal antecedent);
  /**
   * Assert (= n (c (acc_1 n) ... (acc_m n))), where acc_i are the accessors
   * of the constructor with the given index.
   */
  void assertIsConstructorAxiom(ENode* n, size_t cidx, Literal antecedent);
  /**
   * Given a constructor n := (c a_1 ... a_m), assert (= (acc_i n) a_i) for
   * every i.
   */
  void assertAccessorAxioms(ENode* n);
  void assertUpdateFieldAxioms(ENode* n);
  void addRecognizer(TheoryVar v, ENode* recognizer);
  /** Propagate a recognizer that was assigned false. */
  void propagateRecognizer(TheoryVar v, ENode* r);
  /** Sign a conflict for r := is_c(a), c := c(...), not r, and c == a. */
  void signRecognizerConflict(ENode* c, ENode* r);
  void mkSplit(TheoryVar v);

  void clearMark();
  void ocMarkOnStack(ENode* n);
  bool ocOnStack(ENode* n) const { return n->getRoot()->isMarked(); }
  void ocMarkCycleFree(ENode* n);
  bool ocCycleFree(ENode* n) const { return n->getRoot()->isMarked2(); }
  void ocPushStack(ENode* n);
  /** The constructor of the class of n, or null if it has none. */
  ENode* ocGetCstor(ENode* n);
  /**
   * True if n can be reached from n by following equalities and
   * constructors, e.g. in a1 = cons(v1, a2), a2 = cons(v2, a1).
   */
  bool occursCheck(ENode* n);
  bool occursCheckEnter(ENode* n);
  void occursCheckExplain(ENode* app, ENode* root);
  void explainIsChild(ENode* parent, ENode* child);

  void printVar(std::ostream& out, TheoryVar v) const;

  /** Reset the marks left by a final check. */
  class FinalCheckGuard
  {
   public:
    FinalCheckGuard(TheoryDatatype* th);
    ~FinalCheckGuard();

   private:
    TheoryDatatype* d_th;
  };

  enum StackOp
  {
    ENTER,
    EXIT
  };

  std::vector<VarData*> d_varData;
  UnionFind<TheoryDatatype> d_find;
  TrailStack d_trailStack;

  std::vector<ENode*> d_toUnmark;
  std::vector<ENode*> d_toUnmark2;
  /** the conflict, if any */
  ENodePairVector d_usedEqs;
  /** the parent explanation of the occurs check */
  std::unordered_map<ENode*, ENode*> d_parent;
  /** the DFS stack of the occurs check */
  std::vector<std::pair<StackOp, ENode*>> d_stack;

  /** the memoized answers of isRecursiveDatatype */
  std::unordered_map<TypeNode, bool> d_isRecursive;
  /** the types checkUnsupportedNesting has already seen */
  std::unordered_set<TypeNode> d_nestingChecked;

  struct Statistics
  {
    uint64_t d_occursCheck = 0;
    uint64_t d_splits = 0;
    uint64_t d_assertCnstr = 0;
    uint64_t d_assertAccessor = 0;
    uint64_t d_assertUpdateField = 0;
  };
  Statistics d_dtStats;
};

Theory* mkTheoryDatatype(SmtContext& ctx);

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__THEORY_DATATYPE_H */

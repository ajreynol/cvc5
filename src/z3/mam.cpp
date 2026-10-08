/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The Matching Abstract Machine: Z3's E-matching engine.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/mam.cpp, and recast in cvc5 style.
 *
 * STATUS: the code trees are not ported yet. This implementation accepts
 * patterns but never produces a match, so no instantiation is performed by
 * E-matching. Because that drops deductions rather than adding them, "unsat"
 * stays sound; a satisfying assignment is reported as "unknown", which is
 * arranged by marking the context model-unsound as soon as a pattern is
 * registered.
 */

#include "z3/mam.h"

#include "z3/ast.h"
#include "z3/enode.h"
#include "z3/quantifier_manager.h"
#include "z3/smt_context.h"

namespace cvc5::internal {
namespace z3 {

namespace {

class MamImpl : public Mam
{
 public:
  MamImpl(SmtContext& ctx) : Mam(ctx) {}

  void addPattern(TNode q, TNode mp) override
  {
    // No code tree is built, so this pattern will never fire.
    d_context.markModelUnsound(theory::THEORY_QUANTIFIERS);
  }

  void pushScope() override {}

  void popScope(size_t numScopes) override {}

  void match() override {}

  void rematch(bool useIrrelevant) override {}

  bool hasWork() const override { return false; }

  void relevantEh(ENode* n, bool lazy) override {}

  void addEqEh(ENode* r1, ENode* r2) override {}

  void reset() override {}

  void print(std::ostream& out) override
  {
    out << "mam: the code trees are not ported yet\n";
  }

  void onMatch(TNode q,
               TNode pat,
               size_t numBindings,
               ENode* const* bindings,
               uint32_t maxGeneration,
               std::vector<std::pair<ENode*, ENode*>>& usedENodes) override
  {
  }

  bool isShared(ENode* n) const override { return false; }
};

}  // namespace

Mam* mkMam(SmtContext& ctx) { return new MamImpl(ctx); }

}  // namespace z3
}  // namespace cvc5::internal

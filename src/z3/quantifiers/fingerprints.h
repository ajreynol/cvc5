/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Fingerprints: the record of quantifier instantiations already made.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * files src/smt/fingerprints.h and src/smt/fingerprints.cpp, recast in cvc5
 * style.
 *
 * A fingerprint is a key (the id of a quantifier, or a theory axiom id)
 * together with a tuple of enodes. Lookup is modulo the current equivalence
 * classes, which is what stops the same instantiation being produced again
 * after the E-graph has merged the bindings.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__QUANTIFIERS__FINGERPRINTS_H
#define CVC5__Z3__QUANTIFIERS__FINGERPRINTS_H

#include <ostream>
#include <unordered_set>
#include <vector>

#include "z3/quantifiers/enode.h"
#include "z3/util/trail.h"

namespace cvc5::internal {
namespace z3 {

class FingerprintSet;

class Fingerprint
{
 public:
  Fingerprint(
      TrailStack& r, uint64_t d, uint32_t dHash, size_t n, ENode* const* args);

  uint64_t getData() const { return d_data; }
  uint32_t getDataHash() const { return d_dataHash; }
  size_t getNumArgs() const { return d_numArgs; }
  ENode* const* getArgs() const { return d_args; }
  ENode* getArg(size_t idx) const
  {
    Assert(idx < d_numArgs);
    return d_args[idx];
  }

 protected:
  uint64_t d_data = 0;
  uint32_t d_dataHash = 0;
  size_t d_numArgs = 0;
  ENode** d_args = nullptr;

  friend class FingerprintSet;
  Fingerprint() = default;
};

std::ostream& operator<<(std::ostream& out, const Fingerprint& f);

class FingerprintSet
{
  struct FingerprintHashProc
  {
    size_t operator()(const Fingerprint* f) const { return f->getDataHash(); }
  };

  struct FingerprintEqProc
  {
    bool operator()(const Fingerprint* f1, const Fingerprint* f2) const;
  };

  using Set =
      std::unordered_set<Fingerprint*, FingerprintHashProc, FingerprintEqProc>;

 public:
  FingerprintSet(TrailStack& t) : d_trailStack(t) {}

  /**
   * Record the fingerprint if it is new, returning it; return null if an
   * equivalent fingerprint was already recorded.
   */
  Fingerprint* insert(uint64_t data,
                      uint32_t dataHash,
                      size_t numArgs,
                      ENode* const* args);

  size_t size() const { return d_fingerprints.size(); }

  void pushScope();
  void popScope(size_t numScopes);

 private:
  Fingerprint* mkDummy(uint64_t data,
                       uint32_t dataHash,
                       size_t numArgs,
                       ENode* const* args);

  TrailStack& d_trailStack;
  Set d_set;
  std::vector<Fingerprint*> d_fingerprints;
  std::vector<size_t> d_scopes;
  ENodeVector d_tmp;
  Fingerprint d_dummy;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__QUANTIFIERS__FINGERPRINTS_H */

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
 * Ported from Z3: src/smt/fingerprints.h, src/smt/fingerprints.cpp.
 * Z3 is Copyright (c) Microsoft Corporation and licensed under the MIT
 * License, see licenses/z3-LICENSE.
 *
 * A fingerprint is a key (the id of a quantifier, or a theory axiom id)
 * together with a tuple of enodes. Lookup is modulo the current equivalence
 * classes, which is what stops the same instantiation being produced again
 * after the E-graph has merged the bindings.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__FINGERPRINTS_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__FINGERPRINTS_H

#include <ostream>
#include <unordered_set>
#include <vector>

#include "context/cdlist.h"
#include "theory/quantifiers/eager/enode.h"
#include "theory/quantifiers/eager/trail.h"

namespace cvc5::internal {
namespace theory::quantifiers::eager {

class FingerprintSet;

/** The record of one instantiation: a quantifier and its bindings. */
class Fingerprint
{
 public:
  /**
   * A fingerprint of q with data hash dHash and the n bindings args, which
   * are copied into the memory of the trail stack r.
   */
  Fingerprint(
      TrailStack& r, TNode q, uint32_t dHash, size_t n, ENode* const* args);

  /** The quantifier the bindings are for. */
  TNode getQuantifier() const { return d_quant; }
  /** The hash of the quantifier and of the bindings as passed to insert. */
  uint32_t getDataHash() const { return d_dataHash; }
  /** The number of bindings. */
  size_t getNumArgs() const { return d_numArgs; }
  /** The bindings, as the roots of their classes when recorded. */
  ENode* const* getArgs() const { return d_args; }
  /** The idx-th binding. */
  ENode* getArg(size_t idx) const
  {
    Assert(idx < d_numArgs);
    return d_args[idx];
  }

 protected:
  /**
   * Not reference counted, since a fingerprint is never destroyed: the
   * quantifier manager keeps the quantifier.
   */
  TNode d_quant;
  /** The hash, see getDataHash. */
  uint32_t d_dataHash = 0;
  /** The number of bindings. */
  size_t d_numArgs = 0;
  /** The bindings, in the memory of the trail stack (d_tmp for the dummy). */
  ENode** d_args = nullptr;

  friend class FingerprintSet;
  Fingerprint() = default;
};

/** The fingerprints recorded so far, backtracked with the trail stack. */
class FingerprintSet
{
  /** Hashes a fingerprint by its data hash. */
  struct FingerprintHashProc
  {
    /** The data hash of f. */
    size_t operator()(const Fingerprint* f) const { return f->getDataHash(); }
  };

  /** Equality of fingerprints: same quantifier and identical bindings. */
  struct FingerprintEqProc
  {
    /** True if f1 and f2 have the same quantifier and binding enodes. */
    bool operator()(const Fingerprint* f1, const Fingerprint* f2) const;
  };

  using Set =
      std::unordered_set<Fingerprint*, FingerprintHashProc, FingerprintEqProc>;

  /** Erases a fingerprint from the set when it is popped. */
  struct EraseCleanup
  {
    /** The set to erase from. */
    Set* d_set;
    /** Erase f from the set. */
    void operator()(Fingerprint* f) { d_set->erase(f); }
  };

 public:
  /**
   * The fingerprints live in the memory of the trail stack t, and are erased
   * when its scopes are popped.
   */
  FingerprintSet(TrailStack& t);

  /**
   * Record the fingerprint if it is new, returning it; return null if an
   * equivalent fingerprint was already recorded.
   */
  Fingerprint* insert(TNode q, size_t numArgs, ENode* const* args);

  /** The number of fingerprints recorded. */
  size_t size() const { return d_fingerprints.size(); }

 private:
  /**
   * Make the reusable d_dummy stand for q, dataHash and a copy of args
   * (in d_tmp), for a lookup that allocates nothing; returns it.
   */
  Fingerprint* mkDummy(TNode q,
                       uint32_t dataHash,
                       size_t numArgs,
                       ENode* const* args);

  /** The trail stack, whose memory holds the fingerprints. */
  TrailStack& d_trailStack;
  /** The fingerprints recorded, for lookup. */
  Set d_set;
  /** The fingerprints of d_set, in the context of the trail stack. */
  context::CDList<Fingerprint*, EraseCleanup> d_fingerprints;
  /** The storage of the bindings of d_dummy. */
  ENodeVector d_tmp;
  /** The reusable fingerprint of lookups; see mkDummy. */
  Fingerprint d_dummy;
};

}  // namespace theory::quantifiers::eager
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER__FINGERPRINTS_H */

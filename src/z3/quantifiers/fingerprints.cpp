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
 * file src/smt/fingerprints.cpp, and recast in cvc5 style.
 */

#include "z3/quantifiers/fingerprints.h"

#include <cstring>

#include "util/hash.h"

namespace cvc5::internal {
namespace z3 {

Fingerprint::Fingerprint(
    TrailStack& r, uint64_t d, uint32_t dH, size_t n, ENode* const* args)
    : d_data(d), d_dataHash(dH), d_numArgs(n), d_args(nullptr)
{
  d_args = static_cast<ENode**>(r.allocate(sizeof(ENode*) * n));
  std::memcpy(d_args, args, sizeof(ENode*) * n);
}

FingerprintSet::FingerprintSet(TrailStack& t)
    : d_trailStack(t),
      d_fingerprints(t.getContext(), true, EraseCleanup{&d_set})
{
}

bool FingerprintSet::FingerprintEqProc::operator()(const Fingerprint* f1,
                                                   const Fingerprint* f2) const
{
  if (f1->getData() != f2->getData())
  {
    return false;
  }
  if (f1->getNumArgs() != f2->getNumArgs())
  {
    return false;
  }
  size_t n = f1->getNumArgs();
  for (size_t i = 0; i < n; ++i)
  {
    if (f1->getArg(i) != f2->getArg(i))
    {
      return false;
    }
  }
  return true;
}

Fingerprint* FingerprintSet::mkDummy(uint64_t data,
                                     uint32_t dataHash,
                                     size_t numArgs,
                                     ENode* const* args)
{
  d_tmp.clear();
  d_tmp.insert(d_tmp.end(), args, args + numArgs);
  d_dummy.d_data = data;
  d_dummy.d_dataHash = dataHash;
  d_dummy.d_numArgs = numArgs;
  d_dummy.d_args = d_tmp.data();
  return &d_dummy;
}

Fingerprint* FingerprintSet::insert(uint64_t data,
                                    uint32_t dataHash,
                                    size_t numArgs,
                                    ENode* const* args)
{
  uint64_t h = fnv1a::fnv1a_64(dataHash);
  for (size_t i = 0; i < numArgs; ++i)
  {
    h = fnv1a::fnv1a_64(args[i]->hash(), h);
  }
  dataHash = static_cast<uint32_t>(h);

  Fingerprint* d = mkDummy(data, dataHash, numArgs, args);
  if (d_set.count(d) != 0)
  {
    return nullptr;
  }
  // Retry modulo the current equivalence classes.
  for (size_t i = 0; i < numArgs; ++i)
  {
    d->d_args[i] = d->d_args[i]->getRoot();
  }
  if (d_set.count(d) != 0)
  {
    return nullptr;
  }
  Fingerprint* f = new (d_trailStack)
      Fingerprint(d_trailStack, data, dataHash, numArgs, d->d_args);
  d_fingerprints.push_back(f);
  d_set.insert(f);
  return f;
}

}  // namespace z3
}  // namespace cvc5::internal

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

#include "z3/fingerprints.h"

#include <cstring>

#include "z3/util/hash.h"

namespace cvc5::internal {
namespace z3 {

Fingerprint::Fingerprint(
    Region& r, uint64_t d, uint32_t dH, size_t n, ENode* const* args)
    : d_data(d), d_dataHash(dH), d_numArgs(n), d_args(nullptr)
{
  d_args = static_cast<ENode**>(r.allocate(sizeof(ENode*) * n));
  std::memcpy(d_args, args, sizeof(ENode*) * n);
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

std::ostream& operator<<(std::ostream& out, const Fingerprint& f)
{
  out << f.getDataHash() << " "
      << " num_args " << f.getNumArgs() << " ";
  for (const ENode* arg : f)
  {
    out << " " << arg->getOwnerId();
  }
  out << "\n";
  return out;
}

namespace {

struct ArgData
{
  uint32_t d_dataHash;
  ENode* const* d_args;
};

struct KHash
{
  uint32_t operator()(const ArgData& d) const { return d.d_dataHash; }
};

struct ArgHash
{
  uint32_t operator()(const ArgData& d, size_t i) const
  {
    return static_cast<uint32_t>(d.d_args[i]->hash());
  }
};

}  // namespace

Fingerprint* FingerprintSet::insert(uint64_t data,
                                    uint32_t dataHash,
                                    size_t numArgs,
                                    ENode* const* args)
{
  ArgData argData{dataHash, args};
  dataHash = getCompositeHash(argData, numArgs, KHash(), ArgHash());

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
  Fingerprint* f =
      new (d_region) Fingerprint(d_region, data, dataHash, numArgs, d->d_args);
  d_fingerprints.push_back(f);
  d_set.insert(f);
  return f;
}

bool FingerprintSet::contains(uint64_t data,
                              uint32_t dataHash,
                              size_t numArgs,
                              ENode* const* args)
{
  Fingerprint* d = mkDummy(data, dataHash, numArgs, args);
  if (d_set.count(d) != 0)
  {
    return true;
  }
  for (size_t i = 0; i < numArgs; ++i)
  {
    d->d_args[i] = d->d_args[i]->getRoot();
  }
  return d_set.count(d) != 0;
}

void FingerprintSet::reset()
{
  d_set.clear();
  d_fingerprints.clear();
}

void FingerprintSet::pushScope() { d_scopes.push_back(d_fingerprints.size()); }

void FingerprintSet::popScope(size_t numScopes)
{
  size_t lvl = d_scopes.size();
  Assert(numScopes <= lvl);
  size_t newLvl = lvl - numScopes;
  size_t oldSize = d_scopes[newLvl];
  size_t size = d_fingerprints.size();
  if (oldSize == 0 && size > 0)
  {
    d_set.clear();
  }
  else
  {
    for (size_t i = oldSize; i < size; ++i)
    {
      d_set.erase(d_fingerprints[i]);
    }
  }
  d_fingerprints.resize(oldSize);
  d_scopes.resize(newLvl);
}

void FingerprintSet::print(std::ostream& out) const
{
  out << "fingerprints:\n";
  for (const Fingerprint* f : d_fingerprints)
  {
    out << f->getData() << " " << *f;
  }
}

bool FingerprintSet::slowContains(uint64_t data,
                                  uint32_t /*dataHash*/,
                                  size_t numArgs,
                                  ENode* const* args) const
{
  for (const Fingerprint* f : d_fingerprints)
  {
    if (f->getData() != data)
    {
      continue;
    }
    if (f->getNumArgs() != numArgs)
    {
      continue;
    }
    size_t i = 0;
    for (; i < numArgs; ++i)
    {
      if (f->getArg(i)->getRoot() != args[i]->getRoot())
      {
        break;
      }
    }
    if (i == numArgs)
    {
      return true;
    }
  }
  return false;
}

}  // namespace z3
}  // namespace cvc5::internal

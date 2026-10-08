/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Tagged pointers.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/util/tptr.h, and recast in cvc5 style.
 *
 * The Z3 core packs a small tag into the low bits of a pointer, or boxes a
 * small integer alongside such a tag, so that its pervasive justification
 * objects stay one word wide. Everything allocated here is at least
 * four-byte aligned, which leaves the low two bits free.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__UTIL__TAGGED_PTR_H
#define CVC5__Z3__UTIL__TAGGED_PTR_H

#include <cstddef>
#include <cstdint>

#include "base/check.h"

namespace cvc5::internal {
namespace z3 {

/** The number of low bits of a pointer available for tagging. */
constexpr uintptr_t s_tagBits = 2;

/** Mask selecting the tag bits. */
constexpr uintptr_t s_tagMask = (uintptr_t(1) << s_tagBits) - 1;

/** Mask selecting the pointer bits. */
constexpr uintptr_t s_ptrMask = ~s_tagMask;

/** A pointer with a tag in its low bits, plus the ability to box an integer. */
class TaggedPtr
{
 public:
  TaggedPtr() : d_data(0) {}

  /** Tag a pointer. */
  template <typename T>
  static TaggedPtr tag(T* p, uintptr_t t)
  {
    Assert(t <= s_tagMask);
    Assert((reinterpret_cast<uintptr_t>(p) & s_tagMask) == 0)
        << "tagged pointer is not sufficiently aligned";
    TaggedPtr r;
    r.d_data = reinterpret_cast<uintptr_t>(p) | t;
    return r;
  }

  /** Box a small integer with a tag. */
  static TaggedPtr boxInt(uint32_t val, uintptr_t t)
  {
    Assert(t <= s_tagMask);
    TaggedPtr r;
    r.d_data = (static_cast<uintptr_t>(val) << s_tagBits) | t;
    return r;
  }

  uintptr_t getTag() const { return d_data & s_tagMask; }

  template <typename T>
  T* untag() const
  {
    return reinterpret_cast<T*>(d_data & s_ptrMask);
  }

  uint32_t unboxInt() const
  {
    return static_cast<uint32_t>(d_data >> s_tagBits);
  }

  uintptr_t raw() const { return d_data; }

  bool operator==(const TaggedPtr& other) const
  {
    return d_data == other.d_data;
  }

  bool operator!=(const TaggedPtr& other) const
  {
    return d_data != other.d_data;
  }

 private:
  uintptr_t d_data;
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__UTIL__TAGGED_PTR_H */

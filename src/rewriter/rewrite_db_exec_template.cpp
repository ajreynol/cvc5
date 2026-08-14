/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The executable rewrite database.
 *
 * This is the template of rewrite_db_exec.cpp. Everything but the body marked
 * below is written by hand and is *not* regenerated: only the implementation
 * of the :exec rules is, by `-o rare-db-exec`, which contrib/install-rare-
 * rewrites substitutes into this template.
 */

#include "rewriter/rewrite_db_exec.h"

#include "expr/aci_norm.h"
#include "expr/nary_term_util.h"
#include "expr/node_manager.h"
#include "theory/builtin/generic_op.h"
#include "util/bitvector.h"
#include "util/rational.h"
#include "util/string.h"

namespace cvc5::internal {
namespace rewriter {

Node RewriteDbExec::mkListArg(const Node& n, size_t start, size_t end) const
{
  Assert(start <= end && end <= n.getNumChildren());
  std::vector<Node> children(n.begin() + start, n.begin() + end);
  return d_nm->mkNode(Kind::SEXPR, children);
}

Node RewriteDbExec::mkNary(Kind k,
                           const std::vector<Node>& children,
                           const TypeNode& tn) const
{
  if (children.empty())
  {
    // all children came from :list variables bound to the empty sequence
    return expr::getNullTerminator(d_nm, k, tn);
  }
  if (children.size() == 1)
  {
    return children[0];
  }
  return d_nm->mkNode(k, children);
}

// The implementation of the :exec rules below is generated, see the note at
// the top of this file.
// clang-format off
${exec_impl}$
// clang-format on

}  // namespace rewriter
}  // namespace cvc5::internal

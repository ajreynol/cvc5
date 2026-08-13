/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Printer for the compiled implementation of the executable rewrite rules.
 */

#include "cvc5_private.h"

#ifndef CVC5__REWRITER__REWRITE_DB_EXEC_PRINTER__H
#define CVC5__REWRITER__REWRITE_DB_EXEC_PRINTER__H

#include <iosfwd>

#include "rewriter/rewrite_db_exec.h"

namespace cvc5::internal {
namespace rewriter {

/**
 * Print to os the C++ implementation of the single step rewrite given by the
 * :exec rules of db, that is, the contents of rewrite_db_exec_compiled.cpp.
 *
 * The printed implementation tests the shape of a term with straight-line code
 * instead of traversing the match trie of db, but is otherwise equivalent to
 * it: it computes the same matches, in the same order, and instantiates the
 * conditions and right-hand side of a match on demand.
 *
 * This is invoked by `-o rare-db-exec`, and its output is installed by
 * contrib/install-rare-rewrites.
 */
void printRewriteDbExecCompiled(std::ostream& os, const RewriteDbExec& db);

}  // namespace rewriter
}  // namespace cvc5::internal

#endif /* CVC5__REWRITER__REWRITE_DB_EXEC_PRINTER__H */

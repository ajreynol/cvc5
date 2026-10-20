/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for printing the proofs of an incremental run as a proof script.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__INCREMENTAL_PROOF_PRINTER_H
#define CVC5__PROOF__INCREMENTAL_PROOF_PRINTER_H

#include <iosfwd>
#include <memory>

#include "proof/eo/eo_node_converter.h"
#include "proof/eo/eo_print_channel.h"
#include "proof/eo/eo_printer.h"
#include "proof/proof_node.h"
#include "smt/env_obj.h"
#include "util/result.h"

namespace cvc5::internal {

namespace rewriter {
class RewriteDb;
}

namespace proof {

/**
 * Prints the final proofs of the unsat responses of an incremental run as a
 * single CPC proof script. The user push and pop commands are mirrored as
 * (push 1) and (pop 1) commands in the script, where the entire script is
 * additionally enclosed in a scope, which is popped on reset-assertions.
 *
 * The proof of each unsat response is printed as with get-proof, except that
 * the declarations, definitions, assumptions and term bindings that were
 * printed by a previous proof in the current scope of the script are not
 * printed again. Each check-sat response is additionally marked by
 * (echo "sat"), (echo "unsat") or (echo "unknown").
 */
class IncrementalProofPrinter : protected EnvObj
{
 public:
  IncrementalProofPrinter(Env& env,
                          std::ostream& out,
                          rewriter::RewriteDb* rdb);
  ~IncrementalProofPrinter();
  /** Notify that the user pushed a context. */
  void notifyPush();
  /** Notify that the user popped a context. */
  void notifyPop();
  /** Notify that the user reset the assertions. */
  void notifyResetAssertions();
  /**
   * Notify that a check-sat command returned result r. If r is unsat, pfn is
   * its final proof, with scopes for definitions and assertions. Otherwise,
   * pfn is null.
   */
  void notifyCheckSatResult(const Result& r, std::shared_ptr<ProofNode> pfn);

 private:
  /** Ensure the scopes of the script match the user context. */
  void ensureScopes();
  /** Push a scope of the script */
  void pushScope();
  /** Pop a scope of the script */
  void popScope();
  /** The output stream */
  std::ostream& d_out;
  /** The node converter */
  EoNodeConverter d_atp;
  /** The printer */
  EoPrinter d_eop;
  /** The print channel */
  EoPrintChannelOut d_eout;
  /** The number of user contexts pushed and not popped */
  uint32_t d_userLevel;
  /**
   * The number of scopes pushed and not popped in the script, which is either
   * zero if nothing has been printed, or d_userLevel+1.
   */
  uint32_t d_scriptLevel;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif /* CVC5__PROOF__INCREMENTAL_PROOF_PRINTER_H */

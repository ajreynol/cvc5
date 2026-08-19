/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A utility for converting proofs to ones where define-fun are macros.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__MACRO_DEF_PROOF_CONVERTER_H
#define CVC5__PROOF__MACRO_DEF_PROOF_CONVERTER_H

#include "expr/beta_reduce_converter.h"
#include "expr/node.h"
#include "proof/proof_node_converter.h"
#include "smt/env_obj.h"
#include "theory/substitutions.h"

namespace cvc5::internal {

class ProofChecker;

/**
 * A callback class for converting proofs to ones where the given definitions
 * are treated as macros. Given definitions (= f (lambda X t)), we update all
 * proofs proving F to those proving the form of F where the applications of f
 * are replaced by t. In other words, we eliminate the defined functions from
 * the proof, which is what would be obtained if the definitions had been
 * expanded in the input.
 *
 * The definitions themselves become trivial in the converted proof: an
 * assumption (= f (lambda X t)) is converted to (= (lambda X t) (lambda X t)),
 * which is proven by REFL. Hence the converted proof no longer depends on
 * them.
 *
 * As an example, the proof
 *
 *                      ------------------------- ASSUME
 *   ---------- ASSUME  (= f (lambda ((x Int)) (+ x 1)))    -------- REFL
 *   (< (f a) a)        --------------------------------------------- HO_CONG
 *                      (= (f a) ((lambda ((x Int)) (+ x 1)) a))
 *                      ... (= (< (f a) a) false)
 *   -------------------------------------------------------- EQ_RESOLVE
 *   false
 *
 * is converted to a proof of false from the assumption (< (+ a 1) a), where
 * the applications of the HO_CONG and beta reduction steps above are trivial.
 *
 * This is used for printing proofs in a format where define-fun are macros
 * (e.g. Eunoia), where the assumption (< (+ a 1) a) can be printed as
 * (< (f a) a), that is, in the form it had in the input.
 */
class MacroDefConverterCallback : public ProofNodeConverterCallback,
                                  protected EnvObj
{
 public:
  /**
   * @param env Reference to the environment.
   * @param defs The definitions to treat as macros, which are equalities of
   * the form (= f t).
   */
  MacroDefConverterCallback(Env& env, const std::vector<Node>& defs);
  virtual ~MacroDefConverterCallback() {}
  /**
   * Convert the term n, which expands the definitions in n and eliminates the
   * beta redexes this introduces. Returns n if it does not contain any of the
   * defined functions.
   */
  Node convertTerm(const Node& n);
  /**
   * Expand the definitions in n, without eliminating the beta redexes this
   * introduces.
   */
  Node expandTerm(const Node& n);
  /**
   * Return true if expanding the definitions in n coincides with expanding
   * them as macros, that is, with replacing their applications by their
   * bodies.
   *
   * This is false e.g. for (P f), where f is a defined function that is
   * passed as a higher-order argument, since expanding f there requires
   * replacing it by a lambda term. In such cases, the converted form of n
   * cannot be printed as n.
   *
   * @param n The node to check.
   * @return true if expanding the definitions in n is macro expansion.
   */
  bool isMacroExpansion(const Node& n) const;
  /** Should we convert the given proof node? True if it mentions a definition
   */
  bool shouldConvert(std::shared_ptr<ProofNode> pn) override;
  /**
   * This converts all proofs of formulas F to proofs of convertTerm(F).
   *
   * We first check the cases where the step became trivial, that is, where its
   * conclusion is now an equality between identical terms, or where it is now
   * proven by one of its premises. Otherwise, we apply the original rule to
   * the converted premises and arguments. If this does not prove what is
   * required, which is the case e.g. for congruence over an application of a
   * defined function, we connect what it proves to what is required via beta
   * reduction steps.
   */
  Node convert(Node res,
               ProofRule id,
               const std::vector<Node>& children,
               const std::vector<Node>& args,
               CDProof* cdp) override;

 private:
  /** Return true if n is a definition treated as a macro that has parameters */
  bool isMacroWithParams(TNode n) const;
  /**
   * Try to apply the rule id to children/args. If this proves expected, we add
   * the step to cdp and return true. Otherwise, newRes is set to what the rule
   * proves, or null if the rule does not apply.
   */
  bool tryWith(ProofRule id,
               const std::vector<Node>& children,
               const std::vector<Node>& args,
               const Node& expected,
               Node& newRes,
               CDProof* cdp);
  /**
   * Connect what the rule id proves for the given premises and arguments to
   * the conclusion resc that is required, where the two are related by beta
   * reduction. Returns false if this is not the case.
   */
  bool bridgeBeta(ProofRule id,
                  const std::vector<Node>& children,
                  const std::vector<Node>& args,
                  const Node& newRes,
                  const Node& resc,
                  CDProof* cdp);
  /**
   * Prove (= a b), where b is expected to be the result of beta reducing a.
   * Returns false if this is not the case.
   */
  bool proveBeta(const Node& a, const Node& b, CDProof* cdp);
  /** The definitions, as a substitution from defined functions to their bodies
   */
  theory::SubstitutionMap d_subs;
  /** Utility for eliminating the beta redexes introduced by the substitution */
  BetaReduceNodeConverter d_brc;
  /** Cache for convertTerm */
  std::unordered_map<Node, Node> d_cache;
  /** Cache for expandTerm */
  std::unordered_map<Node, Node> d_ecache;
  /** The proof checker of the environment */
  ProofChecker* d_pc;
};

}  // namespace cvc5::internal

#endif

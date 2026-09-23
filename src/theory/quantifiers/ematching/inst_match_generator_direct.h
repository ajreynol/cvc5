/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Direct inst match generator for nested single triggers.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INST_MATCH_GENERATOR_DIRECT_H
#define CVC5__THEORY__QUANTIFIERS__INST_MATCH_GENERATOR_DIRECT_H

#include <map>
#include <memory>
#include <vector>

#include "expr/node.h"
#include "theory/quantifiers/ematching/im_generator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

/**
 * A standalone matcher for a restricted class of non-simple single triggers.
 *
 * This class is intended for patterns like f(g(x)) where all non-ground
 * subterms are ordinary atomic trigger applications. It does not reuse the
 * linked-list decomposition used by InstMatchGenerator. Instead, it compiles a
 * tree for the trigger and matches it directly against ground terms.
 */
class InstMatchGeneratorDirect : public IMGenerator
{
 public:
  InstMatchGeneratorDirect(Env& env, Trigger* tparent, Node q, Node pat);

  void resetInstantiationRound() override;
  bool reset(Node eqc) override;
  int getNextMatch(InstMatch& m) override;
  uint64_t addInstantiations(InstMatch& m) override;
  int getActiveScore() override;
  InferenceId getInferenceId() override
  {
    return InferenceId::QUANTIFIERS_INST_E_MATCHING;
  }

  void setActiveAdd(bool val) { d_activeAdd = val; }
  void excludeMatch(Node n) { d_excludedMatches[n] = true; }
  Node getCurrentMatch() const { return d_currMatched; }
  void setIndependent() { d_independentGen = true; }

  /** Returns true if this class can handle pat for quantified formula q. */
  static bool isApplicable(Node q, Node pat);

 private:
  enum class PatternKind
  {
    VARIABLE,
    GROUND,
    APP,
  };

  struct PatternNode
  {
    PatternNode(Node pat, PatternKind kind) : d_pattern(pat), d_kind(kind) {}
    Node d_pattern;
    PatternKind d_kind;
    Node d_op;
    int d_varNum = -1;
    std::vector<std::unique_ptr<PatternNode>> d_children;
  };

  struct MatchResult
  {
    std::vector<Node> d_vals;
    Node d_matched;
  };

  struct CandidateKey
  {
    Node d_eqc;
    Node d_op;
    bool operator<(const CandidateKey& other) const;
  };

  struct SubMatchKey
  {
    Node d_pattern;
    Node d_eqc;
    bool operator<(const SubMatchKey& other) const;
  };

  static bool isApplicableInternal(Node q, Node pat, bool isRoot);
  std::unique_ptr<PatternNode> compile(Node pat) const;
  Node getEqcKey(Node n) const;
  bool isGoodCandidate(TNode n, bool requireCurrent) const;
  const std::vector<Node>& getCandidates(Node eqc, Node op);
  std::vector<MatchResult> computeSubMatches(const PatternNode& pat,
                                             Node target);
  const std::vector<MatchResult>& getSubMatches(const PatternNode& pat,
                                                Node target);
  void addApplicationMatches(const PatternNode& pat,
                             TNode cand,
                             std::vector<MatchResult>& out);
  void combineChildMatches(const PatternNode& pat,
                           TNode cand,
                           size_t index,
                           std::vector<Node>& current,
                           std::vector<MatchResult>& out);
  bool mergeMatch(std::vector<Node>& current,
                  const std::vector<Node>& delta,
                  std::vector<size_t>& touched) const;
  void undoMerge(std::vector<Node>& current,
                 const std::vector<size_t>& touched) const;
  bool restoreFromPrefix(const std::vector<Node>& prefix,
                         const std::vector<Node>& vals,
                         InstMatch& m) const;
  bool advanceToNextRoot();

  /** The quantified formula for this trigger. */
  Node d_quant;
  /** The original trigger term. */
  Node d_pattern;
  /** The compiled trigger tree. */
  std::unique_ptr<PatternNode> d_root;
  /** Whether getNextMatch should actively enqueue instantiations. */
  bool d_activeAdd = true;
  /**
   * Whether failed root candidates should be excluded for the rest of a round.
   */
  bool d_independentGen = false;
  /** Whether reset() must be called before the next query. */
  bool d_needsReset = true;
  /** The equivalence class restriction for the current search. */
  Node d_eqc;
  /** The current root term matched by this generator. */
  Node d_currMatched;
  /** Root matches that should be skipped for the remainder of the round. */
  std::map<Node, bool> d_excludedMatches;
  /** The current root candidates for this search. */
  std::vector<Node> d_rootCandidates;
  /** The next root candidate to process. */
  size_t d_rootIndex = 0;
  /** The matches for the current root candidate. */
  std::vector<MatchResult> d_rootMatches;
  /** The next root match to process. */
  size_t d_rootMatchIndex = 0;
  /** Cached candidate lists, indexed by match operator and equivalence class.
   */
  std::map<CandidateKey, std::vector<Node>> d_candidateCache;
  /** Cached matches for nested application subpatterns. */
  std::map<SubMatchKey, std::vector<MatchResult>> d_subMatchCache;
};

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif

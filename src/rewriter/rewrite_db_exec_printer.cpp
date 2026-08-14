/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Printer for the implementation of the executable rewrite database.
 */

#include "rewriter/rewrite_db_exec_printer.h"

#include <map>
#include <ostream>
#include <sstream>
#include <string>
#include <vector>

#include "expr/nary_term_util.h"
#include "expr/node_algorithm.h"
#include "rewriter/rewrites.h"
#include "theory/builtin/generic_op.h"
#include "util/bitvector.h"
#include "util/rational.h"
#include "util/string.h"

namespace cvc5::internal {
namespace rewriter {

namespace {

/** The C++ enumeration member name of a RARE rule, e.g. ARITH_SINE_DOUBLE. */
std::string getRuleEnum(ProofRewriteRule id)
{
  std::stringstream ss;
  ss << id;
  std::string name = ss.str();
  for (char& c : name)
  {
    c = (c == '-') ? '_' : std::toupper(static_cast<unsigned char>(c));
  }
  return name;
}

/** The C++ enumeration member name of a kind, e.g. Kind::SINE. */
std::string getKindEnum(Kind k) { return "Kind::" + kind::kindToString(k); }

/**
 * The state of one printing run. Holds the constants that the generated code
 * refers to via its d_consts member, in the order they are constructed.
 */
class ExecCompiler
{
 public:
  ExecCompiler() {}

  /** Begin compiling a rule, resetting the reasons recorded for it. */
  void beginRule()
  {
    d_skipReason.clear();
    d_approxReason.clear();
  }
  /** Record why we cannot compile the current rule. */
  void setSkipReason(const std::string& r) { d_skipReason = r; }
  /** Why we could not compile the current rule. */
  const std::string& getSkipReason() const { return d_skipReason; }
  /**
   * Record that the current rule is compiled only approximately, i.e. the
   * generated code does not recognize all the terms its left-hand side
   * matches. Note this is sound: the code still only reports genuine matches.
   */
  void setApprox(const std::string& r) { d_approxReason = r; }
  /** Why the current rule is approximate, empty if it is not. */
  const std::string& getApproxReason() const { return d_approxReason; }

  /**
   * Register c as a constant of the generated implementation and return the
   * C++ expression the generated code uses to refer to it. Returns the empty
   * string if we do not know how to construct c.
   */
  std::string mkConstRef(const Node& c)
  {
    std::map<Node, size_t>::const_iterator it = d_constIndex.find(c);
    if (it == d_constIndex.end())
    {
      std::string mk = mkConstCode(c);
      if (mk.empty())
      {
        return "";
      }
      size_t index = d_constCode.size();
      d_constCode.push_back(mk);
      d_constPrint.push_back(c);
      d_constIndex[c] = index;
      it = d_constIndex.find(c);
    }
    return "d_consts[" + std::to_string(it->second) + "]";
  }

  /**
   * Register tn as a type of the generated implementation and return the C++
   * expression the generated code uses to refer to it. Returns the empty
   * string if we do not know how to construct tn.
   */
  std::string mkTypeRef(const TypeNode& tn)
  {
    std::map<TypeNode, size_t>::const_iterator it = d_typeIndex.find(tn);
    if (it == d_typeIndex.end())
    {
      std::string mk = mkTypeCode(tn);
      if (mk.empty())
      {
        return "";
      }
      size_t index = d_typeCode.size();
      d_typeCode.push_back(mk);
      d_typePrint.push_back(tn);
      d_typeIndex[tn] = index;
      it = d_typeIndex.find(tn);
    }
    return "d_types[" + std::to_string(it->second) + "]";
  }

  /** Print the body of the constructor, which fills d_consts and d_types. */
  void printConstants(std::ostream& os) const
  {
    for (size_t i = 0, ntypes = d_typeCode.size(); i < ntypes; i++)
    {
      os << "  // " << d_typePrint[i] << std::endl;
      os << "  d_types.push_back(" << d_typeCode[i] << ");" << std::endl;
    }
    for (size_t i = 0, nconsts = d_constCode.size(); i < nconsts; i++)
    {
      os << "  // " << d_constPrint[i] << std::endl;
      os << "  d_consts.push_back(" << d_constCode[i] << ");" << std::endl;
    }
  }

  /**
   * Compute the variables of pattern p, in the order they first occur in a
   * left-to-right traversal. This fixes the order of the substitution that the
   * generated code computes for a match of p.
   */
  static void getVarOrder(const Node& p, std::vector<Node>& vars)
  {
    if (p.getKind() == Kind::BOUND_VARIABLE)
    {
      if (std::find(vars.begin(), vars.end(), p) == vars.end())
      {
        vars.push_back(p);
      }
      return;
    }
    for (const Node& pc : p)
    {
      getVarOrder(pc, vars);
    }
  }

  /**
   * Return the C++ expression that constructs the instance of pattern p, where
   * the variables in vars are taken from the substitution of the match. Returns
   * the empty string if we do not know how to construct p.
   */
  std::string mkTermCode(const Node& p, const std::vector<Node>& vars)
  {
    if (p.getKind() == Kind::BOUND_VARIABLE)
    {
      std::vector<Node>::const_iterator it =
          std::find(vars.begin(), vars.end(), p);
      if (it == vars.end())
      {
        // a variable that does not occur in the left-hand side is not bound by
        // the match, hence the instance cannot be constructed
        d_skipReason = "the variable " + p.toString()
                       + " is not bound by its left-hand side";
        return "";
      }
      return "m.d_subs[" + std::to_string(std::distance(vars.begin(), it))
             + "]";
    }
    if (p.getNumChildren() == 0)
    {
      return mkConstRef(p);
    }
    std::stringstream ss;
    ss << "d_nm->mkNode(";
    if (p.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      std::string oref = mkConstRef(p.getOperator());
      if (oref.empty())
      {
        d_skipReason =
            "we cannot construct the operator " + p.getOperator().toString();
        return "";
      }
      ss << oref;
    }
    else
    {
      ss << getKindEnum(p.getKind());
    }
    ss << ", {";
    for (size_t i = 0, nchild = p.getNumChildren(); i < nchild; i++)
    {
      std::string cc = mkTermCode(p[i], vars);
      if (cc.empty())
      {
        return "";
      }
      ss << (i == 0 ? "" : ", ") << cc;
    }
    ss << "})";
    return ss.str();
  }

 private:
  /** The C++ expression constructing each registered constant. */
  std::string mkConstCode(const Node& c) const
  {
    std::stringstream ss;
    if (!c.isConst() && c.getMetaKind() != kind::metakind::NULLARY_OPERATOR
        && c.getMetaKind() != kind::metakind::VARIABLE)
    {
      // A nullary term that is not a constant, e.g. re.allchar. Note we build
      // these once as well, since they are shared by all rules that use them.
      ss << "d_nm->mkNode(" << getKindEnum(c.getKind()) << ")";
      return ss.str();
    }
    switch (c.getKind())
    {
      case Kind::CONST_BOOLEAN:
        ss << "d_nm->mkConst(" << (c.getConst<bool>() ? "true" : "false")
           << ")";
        break;
      case Kind::CONST_INTEGER:
        ss << "d_nm->mkConstInt(Rational(\"" << c.getConst<Rational>()
           << "\"))";
        break;
      case Kind::CONST_RATIONAL:
        ss << "d_nm->mkConstReal(Rational(\"" << c.getConst<Rational>()
           << "\"))";
        break;
      case Kind::CONST_BITVECTOR:
      {
        const BitVector& bv = c.getConst<BitVector>();
        ss << "d_nm->mkConst(BitVector(" << bv.getSize() << ", Integer(\""
           << bv.getValue() << "\")))";
      }
      break;
      case Kind::CONST_STRING:
        ss << "d_nm->mkConst(String(\"" << c.getConst<String>().toString()
           << "\", true))";
        break;
      default:
        // We do not know how to construct this constant, e.g. it is a nullary
        // operator such as real.pi, or a constant of a theory that no :exec
        // rule used so far.
        return "";
    }
    return ss.str();
  }
  /** The C++ expression constructing each constant, indexed as in d_consts. */
  std::vector<std::string> d_constCode;
  /** The constant itself, printed as a comment in the generated code. */
  std::vector<Node> d_constPrint;
  /** The C++ expression constructing each type, or "" if we cannot. */
  std::string mkTypeCode(const TypeNode& tn) const
  {
    std::stringstream ss;
    if (tn.isBoolean())
    {
      ss << "d_nm->booleanType()";
    }
    else if (tn.isInteger())
    {
      ss << "d_nm->integerType()";
    }
    else if (tn.isReal())
    {
      ss << "d_nm->realType()";
    }
    else if (tn.isString())
    {
      ss << "d_nm->stringType()";
    }
    else if (tn.isRegExp())
    {
      ss << "d_nm->regExpType()";
    }
    else if (tn.isRoundingMode())
    {
      ss << "d_nm->roundingModeType()";
    }
    else if (tn.isBitVector())
    {
      ss << "d_nm->mkBitVectorType(" << tn.getBitVectorSize() << ")";
    }
    else if (tn.isAbstract())
    {
      // an abstract type, e.g. ?BitVec, which the RARE rules use for the
      // variables that may have any type of a given kind
      ss << "d_nm->mkAbstractType(" << getKindEnum(tn.getAbstractedKind())
         << ")";
    }
    else
    {
      // We do not know how to construct this type, e.g. it is parametric or
      // abstract. Note a rule over such a type is not compiled at all, rather
      // than compiled without its type test.
      return "";
    }
    return ss.str();
  }
  /** The C++ expression constructing each type, indexed as in d_types. */
  std::vector<std::string> d_typeCode;
  /** The type itself, printed as a comment in the generated code. */
  std::vector<TypeNode> d_typePrint;
  /** Maps a type to its index in d_types. */
  std::map<TypeNode, size_t> d_typeIndex;
  /** Maps a constant to its index in d_consts. */
  std::map<Node, size_t> d_constIndex;
  /** Why we could not compile the rule currently being compiled. */
  std::string d_skipReason;
  /** Why the rule currently being compiled is approximate. */
  std::string d_approxReason;
};

/**
 * The kinds of step of the compilation trie below. A step consumes the current
 * symbol and introduces a fixed number of new ones, which is what makes the
 * trie a plain prefix tree over left-hand sides: unlike expr::NaryMatchTrie it
 * needs neither null terminators nor an enumeration of :list variable lengths.
 */
enum class StepKind
{
  /** An application whose operator is determined by its kind. */
  APP,
  /** An application with an explicit operator, e.g. a datatype constructor. */
  APP_OP,
  /**
   * An application of an indexed operator, which the RARE rules state as an
   * APPLY_INDEXED_SYMBOLIC term. Its symbols are the indices of the operator
   * followed by the arguments of the application. Note the rewriter never
   * builds a term of that kind, hence we compile a test of the kind that is
   * actually applied instead, which is what avoids having to run the encoding
   * transform on the terms we match.
   */
  APP_INDEXED,
  /**
   * An n-ary application (f t1 s t2), where t1 and t2 are :list variables and
   * s is the needle. This is atomic: its only symbol is the needle, and the
   * list variables are bound to the children before and after it.
   */
  APP_SANDWICH,
  /** A ground term, which the current symbol must be equal to. */
  TERM,
  /** A variable, which binds the current symbol. */
  VAR
};

/** A step of the compilation trie. */
struct Step
{
  StepKind d_sk = StepKind::TERM;
  /** The kind that is applied, for the APP_ steps. */
  Kind d_kind = Kind::UNDEFINED_KIND;
  /** The operator (APP_OP) or the ground term (TERM). */
  Node d_node;
  /** The number of symbols this step introduces. */
  size_t d_nsyms = 0;
  /** The number of indices of the operator, for APP_INDEXED. */
  size_t d_nindices = 0;
  /**
   * The expression for the type the symbol must be comparable to, for VAR.
   * Note we key a variable step on its type and not on the variable itself,
   * so that rules whose variables differ only in name share the same step.
   */
  std::string d_type;

  bool operator<(const Step& s) const
  {
    if (d_sk != s.d_sk) return d_sk < s.d_sk;
    if (d_kind != s.d_kind) return d_kind < s.d_kind;
    if (d_node != s.d_node) return d_node < s.d_node;
    if (d_nsyms != s.d_nsyms) return d_nsyms < s.d_nsyms;
    if (d_nindices != s.d_nindices) return d_nindices < s.d_nindices;
    return d_type < s.d_type;
  }
};

/**
 * The compilation trie: a prefix tree over the steps of the left-hand sides of
 * the rules, which the generated code traverses once for all of them.
 */
struct CompileTrie
{
  /** The children of this node, one per step. */
  std::map<Step, CompileTrie> d_children;
  /** The rules whose left-hand side ends at this node. */
  std::vector<size_t> d_rules;
};

/**
 * Is p a sandwich, i.e. an n-ary application (f t1 s t2) where t1 and t2 are
 * distinct :list variables and the needle s contains none? This is the only
 * shape in which :list variables may occur, see validate_exec_rule.
 */
bool isSandwich(const Node& p)
{
  if (p.getNumChildren() != 3 || !NodeManager::isNAryKind(p.getKind()))
  {
    return false;
  }
  return expr::isListVar(p[0]) && expr::isListVar(p[2]) && p[0] != p[2];
}

/** The rules of the database that we were able to compile. */
struct CompiledRule
{
  ProofRewriteRule d_id;
  Node d_lhs;
  /** The variables of d_lhs, in the order they first occur. */
  std::vector<Node> d_vars;
  /** The C++ expression constructing each condition, and the right-hand side.
   */
  std::vector<std::string> d_conds;
  std::string d_rhs;
};

/**
 * Compute the step for pattern p, appending the sub-patterns it introduces to
 * subs. Returns false if we cannot compile p, in which case ec records why.
 */
bool mkStep(const Node& p, ExecCompiler& ec, Step& s, std::vector<Node>& subs)
{
  if (p.getKind() == Kind::BOUND_VARIABLE)
  {
    if (expr::isListVar(p))
    {
      // A :list variable is bound by the sandwich it occurs in, hence reaching
      // one here means it occurs elsewhere, which validate_exec_rule forbids.
      ec.setSkipReason("the :list variable " + p.toString()
                       + " does not occur in an (f t1 s t2) group");
      return false;
    }
    s.d_sk = StepKind::VAR;
    s.d_type = ec.mkTypeRef(p.getType());
    if (s.d_type.empty())
    {
      ec.setSkipReason("we cannot construct the type " + p.getType().toString()
                       + " of " + p.toString());
      return false;
    }
    return true;
  }
  if (p.getNumChildren() == 0)
  {
    s.d_sk = StepKind::TERM;
    s.d_node = p;
    if (ec.mkConstRef(p).empty())
    {
      ec.setSkipReason("we cannot construct the term " + p.toString());
      return false;
    }
    return true;
  }
  if (isSandwich(p))
  {
    s.d_sk = StepKind::APP_SANDWICH;
    s.d_kind = p.getKind();
    s.d_nsyms = 1;
    subs.push_back(p[1]);
    return true;
  }
  if (p.getKind() == Kind::APPLY_INDEXED_SYMBOLIC)
  {
    Node op = p.getOperator();
    Assert(op.getKind() == Kind::APPLY_INDEXED_SYMBOLIC_OP);
    Kind ak = op.getConst<GenericOp>().getKind();
    size_t nindices = 0;
    if (!GenericOp::getNumIndicesForOperator(ak, nindices))
    {
      ec.setSkipReason("the number of indices of " + std::string(toString(ak))
                       + " is not determined by its kind");
      return false;
    }
    if (nindices > p.getNumChildren())
    {
      ec.setSkipReason("the indexed operator " + p.toString()
                       + " has too few arguments");
      return false;
    }
    s.d_sk = StepKind::APP_INDEXED;
    s.d_kind = ak;
    s.d_nindices = nindices;
    s.d_nsyms = p.getNumChildren();
    subs.insert(subs.end(), p.begin(), p.end());
    return true;
  }
  s.d_kind = p.getKind();
  s.d_nsyms = p.getNumChildren();
  if (p.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    s.d_sk = StepKind::APP_OP;
    s.d_node = p.getOperator();
    if (ec.mkConstRef(s.d_node).empty())
    {
      ec.setSkipReason("we cannot construct the operator "
                       + s.d_node.toString());
      return false;
    }
  }
  else
  {
    s.d_sk = StepKind::APP;
  }
  subs.insert(subs.end(), p.begin(), p.end());
  // A left-hand side that RewriteDbNodeConverter encoded is compiled as it
  // stands, which is sound but may not recognize the terms the rewriter
  // actually builds. We note the cases where this is so.
  if (p.getKind() == Kind::MULT)
  {
    ec.setApprox("a MULT pattern does not match a NONLINEAR_MULT term");
  }
  else if (p.getKind() == Kind::STRING_CONCAT)
  {
    ec.setApprox(
        "a STRING_CONCAT pattern is stated over the encoding of string "
        "constants as concatenations of single characters");
  }
  else if (p.getKind() == Kind::HO_APPLY)
  {
    ec.setApprox("an HO_APPLY pattern does not match an APPLY_UF term");
  }
  return true;
}

/** Add the left-hand side of rule r to the compilation trie t. */
bool addPattern(CompileTrie& t, const Node& p, size_t r, ExecCompiler& ec)
{
  // The steps of p, in the pre-order the generated code consumes them in.
  std::vector<Step> steps;
  std::vector<Node> visit{p};
  while (!visit.empty())
  {
    Node cn = visit.back();
    visit.pop_back();
    Step s;
    std::vector<Node> subs;
    if (!mkStep(cn, ec, s, subs))
    {
      return false;
    }
    steps.push_back(s);
    visit.insert(visit.end(), subs.rbegin(), subs.rend());
  }
  CompileTrie* curr = &t;
  for (const Step& s : steps)
  {
    curr = &curr->d_children[s];
  }
  curr->d_rules.push_back(r);
  return true;
}

/**
 * Bind the variables of the left-hand side p, given the terms varPos that the
 * variable steps along the trie path bound, and the (application, index)
 * pairs listPos that its sandwich steps bound. Equality tests for the
 * variables that occur more than once are appended to eqTests.
 */
void bindRuleVars(
    const Node& p,
    const std::vector<std::string>& varPos,
    const std::vector<std::pair<std::string, std::string>>& listPos,
    std::map<Node, std::string>& binding,
    std::vector<std::string>& eqTests)
{
  size_t vi = 0;
  size_t li = 0;
  std::vector<Node> visit{p};
  while (!visit.empty())
  {
    Node cn = visit.back();
    visit.pop_back();
    if (cn.getKind() == Kind::BOUND_VARIABLE)
    {
      Assert(vi < varPos.size());
      const std::string& e = varPos[vi];
      vi++;
      std::map<Node, std::string>::const_iterator it = binding.find(cn);
      if (it == binding.end())
      {
        binding[cn] = e;
      }
      else
      {
        // the variable occurs more than once, the two terms must be equal
        eqTests.push_back(e + " == " + it->second);
      }
      continue;
    }
    if (cn.getNumChildren() == 0)
    {
      continue;
    }
    if (isSandwich(cn))
    {
      Assert(li < listPos.size());
      const std::string& app = listPos[li].first;
      const std::string& idx = listPos[li].second;
      li++;
      binding[cn[0]] = "mkListArg(" + app + ", 0, " + idx + ")";
      binding[cn[2]] = "mkListArg(" + app + ", " + idx + " + 1, " + app
                       + ".getNumChildren())";
      visit.push_back(cn[1]);
      continue;
    }
    visit.insert(visit.end(), cn.rbegin(), cn.rend());
  }
}

/** Emits the traversal of the compilation trie. */
class TrieEmitter
{
 public:
  TrieEmitter(std::ostream& os,
              ExecCompiler& ec,
              const std::vector<CompiledRule>& rules)
      : d_os(os), d_ec(ec), d_rules(rules)
  {
  }

  /**
   * Emit the code for trie node t, where syms are the symbols that remain to
   * be matched (the last is the next one), varPos and listPos are what the
   * steps along the path to t bound, and ind is the current indentation.
   */
  void emit(const CompileTrie& t,
            const std::vector<std::string>& syms,
            const std::vector<std::string>& varPos,
            const std::vector<std::pair<std::string, std::string>>& listPos,
            size_t ind)
  {
    if (syms.empty())
    {
      for (size_t r : t.d_rules)
      {
        emitMatch(r, varPos, listPos, ind);
      }
      return;
    }
    std::string cur = syms.back();
    std::vector<std::string> rest(syms.begin(), syms.end() - 1);
    for (const std::pair<const Step, CompileTrie>& c : t.d_children)
    {
      emitStep(c.first, c.second, cur, rest, varPos, listPos, ind);
    }
  }

 private:
  /** The indentation of level n. */
  static std::string sp(size_t n) { return std::string(2 * n, ' '); }
  /** Append the children i of app, for i in [start, end), in reverse. */
  static void pushChildren(std::vector<std::string>& syms,
                           const std::string& app,
                           size_t start,
                           size_t end)
  {
    for (size_t i = end; i > start; i--)
    {
      syms.push_back(app + "[" + std::to_string(i - 1) + "]");
    }
  }

  /** Emit the code for one step of the trie. */
  void emitStep(const Step& s,
                const CompileTrie& t,
                const std::string& cur,
                const std::vector<std::string>& rest,
                const std::vector<std::string>& varPos,
                const std::vector<std::pair<std::string, std::string>>& listPos,
                size_t ind)
  {
    std::vector<std::string> syms = rest;
    std::vector<std::string> vp = varPos;
    std::vector<std::pair<std::string, std::string>> lp = listPos;
    switch (s.d_sk)
    {
      case StepKind::APP:
      case StepKind::APP_OP:
      {
        d_os << sp(ind) << "if (" << cur
             << ".getKind() == " << getKindEnum(s.d_kind);
        if (s.d_sk == StepKind::APP_OP)
        {
          d_os << std::endl
               << sp(ind + 2) << "&& " << cur
               << ".getOperator() == " << d_ec.mkConstRef(s.d_node);
        }
        d_os << std::endl
             << sp(ind + 2) << "&& " << cur
             << ".getNumChildren() == " << s.d_nsyms << ")" << std::endl;
        d_os << sp(ind) << "{" << std::endl;
        pushChildren(syms, cur, 0, s.d_nsyms);
        emit(t, syms, vp, lp, ind + 1);
        d_os << sp(ind) << "}" << std::endl;
      }
      break;
      case StepKind::APP_INDEXED:
      {
        // The rewriter builds an application of the indexed kind itself, not
        // the APPLY_INDEXED_SYMBOLIC term the rule is stated over, hence we
        // test that kind and read the indices off its operator.
        std::string iv = "idx" + std::to_string(d_nextId++);
        size_t nargs = s.d_nsyms - s.d_nindices;
        d_os << sp(ind) << "if (" << cur
             << ".getKind() == " << getKindEnum(s.d_kind) << std::endl;
        d_os << sp(ind + 2) << "&& " << cur << ".getNumChildren() == " << nargs
             << ")" << std::endl;
        d_os << sp(ind) << "{" << std::endl;
        d_os << sp(ind + 1) << "std::vector<Node> " << iv
             << " = GenericOp::getIndicesForOperator(" << getKindEnum(s.d_kind)
             << ", " << cur << ".getOperator());" << std::endl;
        d_os << sp(ind + 1) << "if (" << iv << ".size() == " << s.d_nindices
             << ")" << std::endl;
        d_os << sp(ind + 1) << "{" << std::endl;
        // the symbols are the indices followed by the arguments
        pushChildren(syms, cur, 0, nargs);
        for (size_t i = s.d_nindices; i > 0; i--)
        {
          syms.push_back(iv + "[" + std::to_string(i - 1) + "]");
        }
        emit(t, syms, vp, lp, ind + 2);
        d_os << sp(ind + 1) << "}" << std::endl;
        d_os << sp(ind) << "}" << std::endl;
      }
      break;
      case StepKind::APP_SANDWICH:
      {
        std::string iv = "i" + std::to_string(d_nextId++);
        std::string nv = "nc" + std::to_string(d_nextId++);
        d_os << sp(ind) << "if (" << cur
             << ".getKind() == " << getKindEnum(s.d_kind) << ")" << std::endl;
        d_os << sp(ind) << "{" << std::endl;
        d_os << sp(ind + 1) << "for (size_t " << iv << " = 0, " << nv << " = "
             << cur << ".getNumChildren(); " << iv << " < " << nv << "; " << iv
             << "++)" << std::endl;
        d_os << sp(ind + 1) << "{" << std::endl;
        syms.push_back(cur + "[" + iv + "]");
        lp.push_back({cur, iv});
        emit(t, syms, vp, lp, ind + 2);
        d_os << sp(ind + 1) << "}" << std::endl;
        d_os << sp(ind) << "}" << std::endl;
      }
      break;
      case StepKind::TERM:
      {
        d_os << sp(ind) << "if (" << cur << " == " << d_ec.mkConstRef(s.d_node)
             << ")" << std::endl;
        d_os << sp(ind) << "{" << std::endl;
        emit(t, syms, vp, lp, ind + 1);
        d_os << sp(ind) << "}" << std::endl;
      }
      break;
      case StepKind::VAR:
      {
        d_os << sp(ind) << "if (" << cur << ".getType().isComparableTo("
             << s.d_type << "))" << std::endl;
        d_os << sp(ind) << "{" << std::endl;
        vp.push_back(cur);
        emit(t, syms, vp, lp, ind + 1);
        d_os << sp(ind) << "}" << std::endl;
      }
      break;
    }
  }

  /** Emit the code reporting a match of rule r. */
  void emitMatch(
      size_t r,
      const std::vector<std::string>& varPos,
      const std::vector<std::pair<std::string, std::string>>& listPos,
      size_t ind)
  {
    const CompiledRule& cr = d_rules[r];
    std::map<Node, std::string> binding;
    std::vector<std::string> eqTests;
    bindRuleVars(cr.d_lhs, varPos, listPos, binding, eqTests);
    size_t bind = ind;
    if (!eqTests.empty())
    {
      d_os << sp(ind) << "if (";
      for (size_t i = 0, ntests = eqTests.size(); i < ntests; i++)
      {
        d_os << (i == 0 ? "" : "\n" + sp(ind + 2) + "&& ") << eqTests[i];
      }
      d_os << ")" << std::endl;
      d_os << sp(ind) << "{" << std::endl;
      bind++;
    }
    d_os << sp(bind) << "// " << cr.d_id << ": " << cr.d_lhs << std::endl;
    d_os << sp(bind) << "matches.push_back(ExecMatch{" << std::endl;
    d_os << sp(bind + 2) << "ProofRewriteRule::" << getRuleEnum(cr.d_id)
         << ", {";
    for (size_t i = 0, nvars = cr.d_vars.size(); i < nvars; i++)
    {
      Assert(binding.find(cr.d_vars[i]) != binding.end());
      d_os << (i == 0 ? "" : ", ") << binding[cr.d_vars[i]];
    }
    d_os << "}});" << std::endl;
    if (!eqTests.empty())
    {
      d_os << sp(ind) << "}" << std::endl;
    }
  }

  std::ostream& d_os;
  ExecCompiler& d_ec;
  const std::vector<CompiledRule>& d_rules;
  /** Counter for generating fresh names in the emitted code. */
  size_t d_nextId = 0;
};

void printHeader(std::ostream& os)
{
  os << "// This implementation of the :exec RARE rules is generated by"
     << std::endl;
  os << "// `-o rare-db-exec` and substituted into" << std::endl;
  os << "// rewriter/rewrite_db_exec_template.cpp by" << std::endl;
  os << "// contrib/install-rare-rewrites. Do not edit it by hand; edit the"
     << std::endl;
  os << "// RARE rules marked with :exec and regenerate it." << std::endl;
  os << std::endl;
}

void printFooter(CVC5_UNUSED std::ostream& os) {}

}  // namespace

void ExecRuleIndex::addRule(ProofRewriteRule id,
                            const std::vector<Node>& conds,
                            const Node& lhs,
                            const Node& rhs)
{
  // Note that several rules may have the same left-hand side, which is not
  // ambiguous when they are conditional: the generated implementation returns
  // a match for each, and the caller tries them in the order they are added
  // here, applying the first whose conditions hold.
  d_rules.push_back(ExecRule{id, lhs, conds, rhs});
}

void printRewriteDbExec(std::ostream& os, NodeManager* nm)
{
  // Index the :exec rules. Note this index is local to this method: it is the
  // input to the code generation below, and is not used while solving.
  ExecRuleIndex index;
  addRewriteExecRules(nm, index);

  ExecCompiler ec;
  std::vector<CompiledRule> crules;
  CompileTrie trie;
  std::vector<std::pair<ProofRewriteRule, std::string>> skipped;
  std::vector<std::pair<ProofRewriteRule, std::string>> approx;
  // Compile each rule of the index into the trie. Note we do this before
  // printing anything, since compiling a rule registers the constants and
  // types it refers to, which are printed in the constructor first.
  for (const ExecRule& r : index.getRules())
  {
    ec.beginRule();
    CompiledRule cr;
    cr.d_id = r.d_id;
    cr.d_lhs = r.d_lhs;
    ExecCompiler::getVarOrder(cr.d_lhs, cr.d_vars);
    bool success = true;
    {
      for (const Node& c : r.d_conds)
      {
        std::string cc = ec.mkTermCode(c, cr.d_vars);
        if (cc.empty())
        {
          success = false;
          break;
        }
        cr.d_conds.push_back(cc);
      }
    }
    if (success)
    {
      cr.d_rhs = ec.mkTermCode(r.d_rhs, cr.d_vars);
      success = !cr.d_rhs.empty();
    }
    // Note we add the pattern to the trie only now, since it is indexed by
    // the position the rule takes in crules below, which a rule we fail to
    // compile must not consume.
    if (success)
    {
      success = addPattern(trie, cr.d_lhs, crules.size(), ec);
    }
    if (!success)
    {
      skipped.emplace_back(cr.d_id, ec.getSkipReason());
      continue;
    }
    if (!ec.getApproxReason().empty())
    {
      approx.emplace_back(cr.d_id, ec.getApproxReason());
    }
    crules.push_back(cr);
  }

  printHeader(os);
  if (!skipped.empty())
  {
    os << "// WARNING: the following :exec rules could not be compiled and are"
       << std::endl;
    os << "// NOT implemented below:" << std::endl;
    for (const std::pair<ProofRewriteRule, std::string>& sk : skipped)
    {
      os << "//   " << sk.first << ", since " << sk.second << std::endl;
    }
    os << std::endl;
  }
  if (!approx.empty())
  {
    os << "// WARNING: the following :exec rules are compiled only"
       << std::endl;
    os << "// approximately, i.e. a match reported below is always correct,"
       << std::endl;
    os << "// but some of the terms they match are not recognized:"
       << std::endl;
    for (const std::pair<ProofRewriteRule, std::string>& ap : approx)
    {
      os << "//   " << ap.first << ", since " << ap.second << std::endl;
    }
    os << std::endl;
  }

  // the constructor, which builds the constants and types the code below uses
  os << "RewriteDbExec::RewriteDbExec(NodeManager* nm) : d_nm(nm)" << std::endl;
  os << "{" << std::endl;
  ec.printConstants(os);
  os << "}" << std::endl;
  os << std::endl;

  os << "bool RewriteDbExec::empty() const { return "
     << (crules.empty() ? "true" : "false") << "; }" << std::endl;
  os << std::endl;

  bool hasRules = !crules.empty();
  bool hasConds = false;
  for (const CompiledRule& cr : crules)
  {
    hasConds = hasConds || !cr.d_conds.empty();
  }
  const char* unused = "CVC5_UNUSED ";
  // The matching routine, which is a single traversal of the compilation trie
  // and hence tests the left-hand sides of all rules at once, sharing the
  // tests they have in common.
  os << "void RewriteDbExec::getMatches(" << std::endl;
  os << "    " << (hasRules ? "" : unused) << "const Node& n," << std::endl;
  os << "    " << (hasRules ? "" : unused)
     << "std::vector<ExecMatch>& matches) const" << std::endl;
  os << "{" << std::endl;
  if (!hasRules)
  {
    os << "  // there are no :exec rules" << std::endl;
  }
  else
  {
    TrieEmitter te(os, ec, crules);
    te.emit(trie, {"n"}, {}, {}, 1);
  }
  os << "}" << std::endl;
  os << std::endl;

  // the number of conditions of each rule
  os << "size_t RewriteDbExec::getNumConditions(" << std::endl;
  os << "    " << (hasConds ? "" : unused) << "const ExecMatch& m) const"
     << std::endl;
  os << "{" << std::endl;
  os << "  switch (m.d_id)" << std::endl;
  os << "  {" << std::endl;
  for (const CompiledRule& cr : crules)
  {
    if (!cr.d_conds.empty())
    {
      os << "    case ProofRewriteRule::" << getRuleEnum(cr.d_id) << ": return "
         << cr.d_conds.size() << ";" << std::endl;
    }
  }
  os << "    default: break;" << std::endl;
  os << "  }" << std::endl;
  os << "  return 0;" << std::endl;
  os << "}" << std::endl;
  os << std::endl;

  // the conditions of each rule, instantiated on demand
  os << "Node RewriteDbExec::getCondition(" << std::endl;
  os << "    " << (hasConds ? "" : unused) << "const ExecMatch& m,"
     << std::endl;
  os << "    " << (hasConds ? "" : unused) << "size_t i) const" << std::endl;
  os << "{" << std::endl;
  os << "  switch (m.d_id)" << std::endl;
  os << "  {" << std::endl;
  for (const CompiledRule& cr : crules)
  {
    if (cr.d_conds.empty())
    {
      continue;
    }
    os << "    case ProofRewriteRule::" << getRuleEnum(cr.d_id) << ":"
       << std::endl;
    os << "      switch (i)" << std::endl;
    os << "      {" << std::endl;
    for (size_t c = 0, nconds = cr.d_conds.size(); c < nconds; c++)
    {
      os << "        case " << c << ": return " << cr.d_conds[c] << ";"
         << std::endl;
    }
    os << "        default: break;" << std::endl;
    os << "      }" << std::endl;
    os << "      break;" << std::endl;
  }
  os << "    default: break;" << std::endl;
  os << "  }" << std::endl;
  os << "  return Node::null();" << std::endl;
  os << "}" << std::endl;
  os << std::endl;

  // the right-hand side of each rule, instantiated on demand
  os << "Node RewriteDbExec::getResult(" << std::endl;
  os << "    " << (hasRules ? "" : unused) << "const ExecMatch& m) const"
     << std::endl;
  os << "{" << std::endl;
  os << "  switch (m.d_id)" << std::endl;
  os << "  {" << std::endl;
  for (const CompiledRule& cr : crules)
  {
    os << "    case ProofRewriteRule::" << getRuleEnum(cr.d_id) << ":"
       << std::endl;
    os << "      return " << cr.d_rhs << ";" << std::endl;
  }
  os << "    default: break;" << std::endl;
  os << "  }" << std::endl;
  os << "  return Node::null();" << std::endl;
  os << "}" << std::endl;
  os << std::endl;

  printFooter(os);
}

}  // namespace rewriter
}  // namespace cvc5::internal

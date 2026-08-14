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

  /** Begin compiling a rule, resetting the reason we may fail to do so. */
  void beginRule() { d_skipReason.clear(); }
  /** Why we could not compile the current rule. */
  const std::string& getSkipReason() const { return d_skipReason; }

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
   * Compute the tests that hold exactly when pattern p matches the term
   * denoted by the C++ expression path, appending them to tests. The terms the
   * variables of p are bound to are recorded in varPath. Returns false if we
   * do not know how to compile p.
   */
  bool getMatchTests(const Node& p,
                     const std::string& path,
                     std::vector<std::string>& tests,
                     std::map<Node, std::string>& varPath)
  {
    if (p.getKind() == Kind::BOUND_VARIABLE)
    {
      // A :list variable stands for a sequence of children of the application
      // it occurs in, which the generated code would have to search for. This
      // is not supported yet; such rules are reported as skipped below.
      if (expr::isListVar(p))
      {
        d_skipReason = "it uses the :list variable " + p.toString();
        return false;
      }
      std::map<Node, std::string>::const_iterator it = varPath.find(p);
      if (it == varPath.end())
      {
        // First occurrence, the variable is bound to this position. Note a
        // variable only matches a term whose type is comparable to its own,
        // which matters for the operators permissive for subtyping.
        std::string tref = mkTypeRef(p.getType());
        if (tref.empty())
        {
          d_skipReason = "we cannot construct the type "
                         + p.getType().toString() + " of " + p.toString();
          return false;
        }
        tests.push_back(path + ".getType().isComparableTo(" + tref + ")");
        varPath[p] = path;
        return true;
      }
      // a repeated variable, the two positions must be the same term
      tests.push_back(path + " == " + it->second);
      return true;
    }
    if (p.getNumChildren() == 0)
    {
      std::string cref = mkConstRef(p);
      if (cref.empty())
      {
        d_skipReason = "we cannot construct the term " + p.toString();
        return false;
      }
      tests.push_back(path + " == " + cref);
      return true;
    }
    tests.push_back(path + ".getKind() == " + getKindEnum(p.getKind()));
    if (p.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      std::string oref = mkConstRef(p.getOperator());
      if (oref.empty())
      {
        d_skipReason =
            "we cannot construct the operator " + p.getOperator().toString();
        return false;
      }
      tests.push_back(path + ".getOperator() == " + oref);
    }
    tests.push_back(
        path + ".getNumChildren() == " + std::to_string(p.getNumChildren()));
    for (size_t i = 0, nchild = p.getNumChildren(); i < nchild; i++)
    {
      if (!getMatchTests(
              p[i], path + "[" + std::to_string(i) + "]", tests, varPath))
      {
        return false;
      }
    }
    return true;
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
};

/** The rules of the database that we were able to compile. */
struct CompiledRule
{
  ProofRewriteRule d_id;
  Node d_lhs;
  std::vector<Node> d_vars;
  /** The tests that hold exactly when d_lhs matches the term n. */
  std::vector<std::string> d_tests;
  /** The C++ expression for the term each variable is bound to. */
  std::vector<std::string> d_subs;
  /** The C++ expression constructing each condition, and the right-hand side.
   */
  std::vector<std::string> d_conds;
  std::string d_rhs;
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
  std::vector<std::pair<ProofRewriteRule, std::string>> skipped;
  // Compile each rule of the index. Note we do this before printing anything,
  // since compiling a rule registers the constants it refers to, which are
  // printed in the constructor first.
  for (const ExecRule& r : index.getRules())
  {
    ec.beginRule();
    CompiledRule cr;
    cr.d_id = r.d_id;
    cr.d_lhs = r.d_lhs;
    ExecCompiler::getVarOrder(cr.d_lhs, cr.d_vars);
    std::map<Node, std::string> varPath;
    bool success = ec.getMatchTests(cr.d_lhs, "n", cr.d_tests, varPath);
    if (success)
    {
      // the term each variable is bound to, in the order fixed above
      for (const Node& v : cr.d_vars)
      {
        Assert(varPath.find(v) != varPath.end());
        cr.d_subs.push_back(varPath[v]);
      }
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
    if (!success)
    {
      skipped.emplace_back(cr.d_id, ec.getSkipReason());
      continue;
    }
    crules.push_back(cr);
  }
  // Group the rules by the kind of their left-hand side, which the generated
  // code dispatches on. Note the tests of the rules of one kind are checked
  // simultaneously, i.e. all matches of a term are computed by a single pass.
  std::map<Kind, std::vector<size_t>> rulesForKind;
  for (size_t i = 0, nrules = crules.size(); i < nrules; i++)
  {
    rulesForKind[crules[i].d_lhs.getKind()].push_back(i);
  }

  printHeader(os);
  if (!skipped.empty())
  {
    os << "// WARNING: the following :exec rules could not be compiled and are"
       << std::endl;
    os << "// NOT implemented below, hence this implementation is not yet"
       << std::endl;
    os << "// equivalent to the executable rewrite trie:" << std::endl;
    for (const std::pair<ProofRewriteRule, std::string>& s : skipped)
    {
      os << "//   " << s.first << ", since " << s.second << std::endl;
    }
    os << std::endl;
  }

  // the constructor, which builds the constants the code below refers to
  os << "RewriteDbExec::RewriteDbExec(NodeManager* nm) "
        ": d_nm(nm)"
     << std::endl;
  os << "{" << std::endl;
  ec.printConstants(os);
  os << "}" << std::endl;
  os << std::endl;

  os << "bool RewriteDbExec::empty() const { return "
     << (crules.empty() ? "true" : "false") << "; }" << std::endl;
  os << std::endl;

  // the matching routine
  bool hasRules = !crules.empty();
  bool hasConds = false;
  for (const CompiledRule& cr : crules)
  {
    hasConds = hasConds || !cr.d_conds.empty();
  }
  const char* unused = "CVC5_UNUSED ";
  os << "void RewriteDbExec::getMatches(" << std::endl;
  os << "    " << (hasRules ? "" : unused) << "const Node& n," << std::endl;
  os << "    " << (hasRules ? "" : unused)
     << "std::vector<ExecMatch>& matches) const" << std::endl;
  os << "{" << std::endl;
  if (rulesForKind.empty())
  {
    os << "  // there are no :exec rules" << std::endl;
  }
  else
  {
    os << "  switch (n.getKind())" << std::endl;
    os << "  {" << std::endl;
    for (const std::pair<const Kind, std::vector<size_t>>& rk : rulesForKind)
    {
      os << "    case " << getKindEnum(rk.first) << ":" << std::endl;
      for (size_t i : rk.second)
      {
        const CompiledRule& cr = crules[i];
        os << "      // " << cr.d_id << ": " << cr.d_lhs << std::endl;
        os << "      if (";
        // the kind was already tested by the switch above
        bool firstTest = true;
        for (size_t t = 1, ntests = cr.d_tests.size(); t < ntests; t++)
        {
          os << (firstTest ? "" : "\n          && ") << cr.d_tests[t];
          firstTest = false;
        }
        if (firstTest)
        {
          os << "true";
        }
        os << ")" << std::endl;
        os << "      {" << std::endl;
        os << "        matches.push_back(ExecMatch{" << std::endl;
        os << "            ProofRewriteRule::" << getRuleEnum(cr.d_id) << ", {";
        for (size_t s = 0, nsubs = cr.d_subs.size(); s < nsubs; s++)
        {
          os << (s == 0 ? "" : ", ") << cr.d_subs[s];
        }
        os << "}});" << std::endl;
        os << "      }" << std::endl;
      }
      os << "      break;" << std::endl;
    }
    os << "    default: break;" << std::endl;
    os << "  }" << std::endl;
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

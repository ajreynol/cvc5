/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cost function of quantifier instantiation.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), files
 * src/parsers/util/cost_parser.cpp and src/ast/cost_evaluator.cpp.
 */

#include "z3/cost_function.h"

#include <cctype>
#include <cstdlib>

#include "base/output.h"

namespace cvc5::internal {
namespace z3 {

struct CostFunction::Expr
{
  enum Kind
  {
    NUM,
    VAR,
    TRUE_,
    FALSE_,
    NOT,
    AND,
    OR,
    IMPLIES,
    ITE,
    EQ,
    XOR,
    ADD,
    SUB,
    MUL,
    DIV,
    UMINUS,
    LE,
    GE,
    LT,
    GT
  };
  Kind d_kind;
  float d_num = 0.0f;
  size_t d_var = 0;
  std::vector<std::unique_ptr<Expr>> d_args;
};

namespace {

/** A recursive descent parser for Z3's prefix cost expressions. */
class Parser
{
 public:
  Parser(const std::string& s) : d_s(s), d_pos(0) {}

  std::unique_ptr<CostFunction::Expr> parse()
  {
    std::unique_ptr<CostFunction::Expr> r = parseExpr();
    skipWs();
    if (r == nullptr || d_pos != d_s.size())
    {
      return nullptr;
    }
    return r;
  }

 private:
  using Expr = CostFunction::Expr;

  void skipWs()
  {
    while (d_pos < d_s.size()
           && std::isspace(static_cast<unsigned char>(d_s[d_pos])))
    {
      d_pos++;
    }
  }

  std::unique_ptr<Expr> parseExpr()
  {
    skipWs();
    if (d_pos >= d_s.size())
    {
      return nullptr;
    }
    if (d_s[d_pos] == '(')
    {
      d_pos++;
      skipWs();
      std::string op = parseToken();
      std::vector<std::unique_ptr<Expr>> args;
      while (true)
      {
        skipWs();
        if (d_pos < d_s.size() && d_s[d_pos] == ')')
        {
          d_pos++;
          break;
        }
        std::unique_ptr<Expr> a = parseExpr();
        if (a == nullptr)
        {
          return nullptr;
        }
        args.push_back(std::move(a));
      }
      return mkOp(op, std::move(args));
    }
    std::string tok = parseToken();
    if (tok.empty())
    {
      return nullptr;
    }
    return mkAtom(tok);
  }

  std::string parseToken()
  {
    skipWs();
    size_t start = d_pos;
    while (d_pos < d_s.size() && d_s[d_pos] != '(' && d_s[d_pos] != ')'
           && !std::isspace(static_cast<unsigned char>(d_s[d_pos])))
    {
      d_pos++;
    }
    return d_s.substr(start, d_pos - start);
  }

  std::unique_ptr<Expr> mkAtom(const std::string& tok)
  {
    std::unique_ptr<Expr> e(new Expr());
    if (tok == "true")
    {
      e->d_kind = Expr::TRUE_;
      return e;
    }
    if (tok == "false")
    {
      e->d_kind = Expr::FALSE_;
      return e;
    }
    size_t var;
    if (lookupVar(tok, var))
    {
      e->d_kind = Expr::VAR;
      e->d_var = var;
      return e;
    }
    // a numeral
    char* end = nullptr;
    double d = std::strtod(tok.c_str(), &end);
    if (end == nullptr || *end != '\0' || end == tok.c_str())
    {
      return nullptr;
    }
    e->d_kind = Expr::NUM;
    e->d_num = static_cast<float>(d);
    return e;
  }

  static bool lookupVar(const std::string& name, size_t& var)
  {
    if (name == "cost") { var = CV_COST; }
    else if (name == "min_top_generation") { var = CV_MIN_TOP_GENERATION; }
    else if (name == "max_top_generation") { var = CV_MAX_TOP_GENERATION; }
    else if (name == "instances") { var = CV_INSTANCES; }
    else if (name == "size") { var = CV_SIZE; }
    else if (name == "depth") { var = CV_DEPTH; }
    else if (name == "generation") { var = CV_GENERATION; }
    else if (name == "quant_generation") { var = CV_QUANT_GENERATION; }
    else if (name == "weight") { var = CV_WEIGHT; }
    else if (name == "vars") { var = CV_VARS; }
    else if (name == "pattern_width") { var = CV_PATTERN_WIDTH; }
    else if (name == "total_instances") { var = CV_TOTAL_INSTANCES; }
    else if (name == "scope") { var = CV_SCOPE; }
    else if (name == "nested_quantifiers") { var = CV_NESTED_QUANTIFIERS; }
    else if (name == "cs_factor") { var = CV_CS_FACTOR; }
    else { return false; }
    return true;
  }

  std::unique_ptr<Expr> mkOp(const std::string& op,
                             std::vector<std::unique_ptr<Expr>>&& args)
  {
    Expr::Kind k;
    size_t minArgs = 2;
    if (op == "not") { k = Expr::NOT; minArgs = 1; }
    else if (op == "and") { k = Expr::AND; }
    else if (op == "or") { k = Expr::OR; }
    else if (op == "implies") { k = Expr::IMPLIES; }
    else if (op == "ite") { k = Expr::ITE; minArgs = 3; }
    else if (op == "=" || op == "iff") { k = Expr::EQ; }
    else if (op == "xor") { k = Expr::XOR; }
    else if (op == "+") { k = Expr::ADD; }
    else if (op == "*") { k = Expr::MUL; }
    else if (op == "-") { k = args.size() == 1 ? Expr::UMINUS : Expr::SUB;
                          minArgs = args.size() == 1 ? 1 : 2; }
    else if (op == "/") { k = Expr::DIV; }
    else if (op == "<=") { k = Expr::LE; }
    else if (op == ">=") { k = Expr::GE; }
    else if (op == "<") { k = Expr::LT; }
    else if (op == ">") { k = Expr::GT; }
    else { return nullptr; }
    if (args.size() < minArgs)
    {
      return nullptr;
    }
    std::unique_ptr<Expr> e(new Expr());
    e->d_kind = k;
    e->d_args = std::move(args);
    return e;
  }

  const std::string& d_s;
  size_t d_pos;
};

float eval(const CostFunction::Expr* f, const std::vector<float>& vals)
{
  using Expr = CostFunction::Expr;
  switch (f->d_kind)
  {
    case Expr::NUM: return f->d_num;
    case Expr::VAR:
      return f->d_var < vals.size() ? vals[f->d_var] : 1.0f;
    case Expr::TRUE_: return 1.0f;
    case Expr::FALSE_: return 0.0f;
    case Expr::NOT:
      return eval(f->d_args[0].get(), vals) == 0.0f ? 1.0f : 0.0f;
    case Expr::AND:
      for (const std::unique_ptr<Expr>& a : f->d_args)
      {
        if (eval(a.get(), vals) == 0.0f)
        {
          return 0.0f;
        }
      }
      return 1.0f;
    case Expr::OR:
      for (const std::unique_ptr<Expr>& a : f->d_args)
      {
        if (eval(a.get(), vals) != 0.0f)
        {
          return 1.0f;
        }
      }
      return 0.0f;
    case Expr::IMPLIES:
      if (eval(f->d_args[0].get(), vals) == 0.0f)
      {
        return 1.0f;
      }
      return eval(f->d_args[1].get(), vals) != 0.0f ? 1.0f : 0.0f;
    case Expr::ITE:
      return eval(f->d_args[0].get(), vals) != 0.0f
                 ? eval(f->d_args[1].get(), vals)
                 : eval(f->d_args[2].get(), vals);
    case Expr::EQ:
      return eval(f->d_args[0].get(), vals)
                     == eval(f->d_args[1].get(), vals)
                 ? 1.0f
                 : 0.0f;
    case Expr::XOR:
      return eval(f->d_args[0].get(), vals)
                     != eval(f->d_args[1].get(), vals)
                 ? 1.0f
                 : 0.0f;
    case Expr::LE:
      return eval(f->d_args[0].get(), vals)
                     <= eval(f->d_args[1].get(), vals)
                 ? 1.0f
                 : 0.0f;
    case Expr::GE:
      return eval(f->d_args[0].get(), vals)
                     >= eval(f->d_args[1].get(), vals)
                 ? 1.0f
                 : 0.0f;
    case Expr::LT:
      return eval(f->d_args[0].get(), vals)
                     < eval(f->d_args[1].get(), vals)
                 ? 1.0f
                 : 0.0f;
    case Expr::GT:
      return eval(f->d_args[0].get(), vals)
                     > eval(f->d_args[1].get(), vals)
                 ? 1.0f
                 : 0.0f;
    case Expr::ADD:
    {
      float r = 0.0f;
      for (const std::unique_ptr<Expr>& a : f->d_args)
      {
        r += eval(a.get(), vals);
      }
      return r;
    }
    case Expr::MUL:
    {
      float r = 1.0f;
      for (const std::unique_ptr<Expr>& a : f->d_args)
      {
        r *= eval(a.get(), vals);
      }
      return r;
    }
    case Expr::SUB:
      return eval(f->d_args[0].get(), vals)
             - eval(f->d_args[1].get(), vals);
    case Expr::UMINUS: return -eval(f->d_args[0].get(), vals);
    case Expr::DIV:
    {
      float q = eval(f->d_args[1].get(), vals);
      if (q == 0.0f)
      {
        Warning() << "z3: cost function division by zero" << std::endl;
        return 1.0f;
      }
      return eval(f->d_args[0].get(), vals) / q;
    }
  }
  return 1.0f;
}

}  // namespace

CostFunction::CostFunction() {}

CostFunction::~CostFunction() {}

bool CostFunction::parse(const std::string& s)
{
  Parser p(s);
  std::unique_ptr<Expr> e = p.parse();
  if (e == nullptr)
  {
    return false;
  }
  d_expr = std::move(e);
  return true;
}

float CostFunction::operator()(const std::vector<float>& vals) const
{
  if (d_expr == nullptr)
  {
    return 1.0f;
  }
  return eval(d_expr.get(), vals);
}

}  // namespace z3
}  // namespace cvc5::internal

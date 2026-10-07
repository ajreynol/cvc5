/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The matching abstract machine (MAM) for eager E-matching.
 */

#include "theory/quantifiers/eager/mam.h"

#include <algorithm>
#include <ostream>

#include "expr/node_algorithm.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

namespace {

/** The arity implied by an INIT opcode, 0 for INITN */
size_t initArity(Opcode op)
{
  return op == Opcode::INITN
             ? 0
             : static_cast<size_t>(op) - static_cast<size_t>(Opcode::INIT1) + 1;
}

/** The opcode for an instruction family with the given arity */
Opcode opcodeFor(Opcode base, Opcode nary, size_t numArgs)
{
  Assert(numArgs >= 1);
  return numArgs <= 6
             ? static_cast<Opcode>(static_cast<size_t>(base) + numArgs - 1)
             : nary;
}

void displayNumArgs(std::ostream& out, size_t numArgs)
{
  if (numArgs <= 6)
  {
    out << numArgs;
  }
  else
  {
    out << "N";
  }
}

}  // namespace

std::ostream& operator<<(std::ostream& out, const Instruction& i)
{
  switch (i.d_opcode)
  {
    case Opcode::INIT1:
    case Opcode::INIT2:
    case Opcode::INIT3:
    case Opcode::INIT4:
    case Opcode::INIT5:
    case Opcode::INIT6: out << "(INIT" << initArity(i.d_opcode) << ")"; break;
    case Opcode::INITN:
      out << "(INITN " << static_cast<const InitN&>(i).d_numArgs << ")";
      break;
    case Opcode::BIND1:
    case Opcode::BIND2:
    case Opcode::BIND3:
    case Opcode::BIND4:
    case Opcode::BIND5:
    case Opcode::BIND6:
    case Opcode::BINDN:
    {
      const Bind& b = static_cast<const Bind&>(i);
      out << "(BIND";
      displayNumArgs(out, b.d_numArgs);
      out << " " << b.d_label << " " << b.d_ireg << " " << b.d_oreg << ")";
    }
    break;
    case Opcode::YIELD1:
    case Opcode::YIELD2:
    case Opcode::YIELD3:
    case Opcode::YIELD4:
    case Opcode::YIELD5:
    case Opcode::YIELD6:
    case Opcode::YIELDN:
    {
      const Yield& y = static_cast<const Yield&>(i);
      out << "(YIELD";
      displayNumArgs(out, y.d_bindings.size());
      out << " #" << y.d_quant.getId();
      for (size_t r : y.d_bindings)
      {
        out << " " << r;
      }
      out << ")";
    }
    break;
    case Opcode::COMPARE:
      out << "(COMPARE " << static_cast<const Compare&>(i).d_reg1 << " "
          << static_cast<const Compare&>(i).d_reg2 << ")";
      break;
    case Opcode::CHECK:
      out << "(CHECK " << static_cast<const Check&>(i).d_reg << " "
          << *static_cast<const Check&>(i).d_enode << ")";
      break;
    case Opcode::FILTER:
    case Opcode::CFILTER:
    case Opcode::PFILTER:
      out << "("
          << (i.d_opcode == Opcode::FILTER
                  ? "FILTER"
                  : (i.d_opcode == Opcode::CFILTER ? "CFILTER" : "PFILTER"))
          << " " << static_cast<const Filter&>(i).d_reg << " "
          << static_cast<const Filter&>(i).d_lblSet << ")";
      break;
    case Opcode::CHOOSE: out << "(CHOOSE)"; break;
    case Opcode::NOOP: out << "(NOOP)"; break;
    case Opcode::CONTINUE:
    {
      const Continue& c = static_cast<const Continue&>(i);
      out << "(CONTINUE " << c.d_label << " " << c.d_numArgs << " " << c.d_oreg
          << " " << c.d_lblSet << " (";
      bool first = true;
      for (const Joint& j : c.d_joints)
      {
        out << (first ? "" : " ");
        first = false;
        switch (j.d_kind)
        {
          case Joint::Kind::NONE: out << "nil"; break;
          case Joint::Kind::GROUND_TERM: out << *j.d_enode; break;
          case Joint::Kind::VAR: out << j.d_reg; break;
          case Joint::Kind::NESTED_VAR:
            out << "(" << j.d_label << " " << j.d_argPos << " " << j.d_reg
                << ")";
            break;
        }
      }
      out << "))";
    }
    break;
    case Opcode::GET_ENODE:
      out << "(GET_ENODE " << static_cast<const GetENode&>(i).d_oreg << " "
          << *static_cast<const GetENode&>(i).d_enode << ")";
      break;
    case Opcode::GET_CGR1:
    case Opcode::GET_CGR2:
    case Opcode::GET_CGR3:
    case Opcode::GET_CGR4:
    case Opcode::GET_CGR5:
    case Opcode::GET_CGR6:
    case Opcode::GET_CGRN:
    {
      const GetCgr& c = static_cast<const GetCgr&>(i);
      out << "(GET_CGR";
      displayNumArgs(out, c.d_iregs.size());
      out << " " << c.d_label << " " << c.d_oreg;
      for (size_t r : c.d_iregs)
      {
        out << " " << r;
      }
      out << ")";
    }
    break;
    case Opcode::IS_CGR:
    {
      const IsCgr& c = static_cast<const IsCgr&>(i);
      out << "(IS_CGR " << c.d_label << " " << c.d_ireg;
      for (size_t r : c.d_iregs)
      {
        out << " " << r;
      }
      out << ")";
    }
    break;
  }
  return out;
}

//-------------------------------------------------------------------- CodeTree

CodeTree::CodeTree(Node rootLabel, size_t numArgs, bool filterCandidates)
    : d_rootLabel(rootLabel),
      d_numArgs(numArgs),
      d_filterCandidates(filterCandidates),
      d_numRegs(numArgs + 1),
      d_numChoices(0),
      d_root(nullptr)
{
}

void CodeTree::displaySeq(std::ostream& out,
                          Instruction* head,
                          size_t indent) const
{
  Instruction* curr = head;
  while (curr != nullptr)
  {
    for (size_t i = 0; i < indent; i++)
    {
      out << "    ";
    }
    out << *curr << std::endl;
    curr = curr->d_next;
    if (curr != nullptr
        && (curr->d_opcode == Opcode::CHOOSE || curr->d_opcode == Opcode::NOOP))
    {
      displayChildren(out, static_cast<Choose*>(curr), indent + 1);
      return;
    }
  }
}

void CodeTree::displayChildren(std::ostream& out,
                               Choose* firstChild,
                               size_t indent) const
{
  Choose* curr = firstChild;
  while (curr != nullptr)
  {
    displaySeq(out, curr, indent);
    curr = curr->d_alt;
  }
}

void CodeTree::display(std::ostream& out) const
{
  out << "code-tree for " << d_rootLabel << "/" << d_numArgs << " ("
      << d_patterns.size() << " patterns, " << d_numRegs << " registers, "
      << d_numChoices << " choices, " << d_candidates.size()
      << " pending candidates)" << std::endl;
  displaySeq(out, d_root, 1);
}

//------------------------------------------------------------- CodeTreeManager

CodeTreeManager::CodeTreeManager(EGraph& eg, Trail& trail)
    : d_egraph(eg), d_trail(trail)
{
}

CodeTreeManager::~CodeTreeManager() {}

CodeTree* CodeTreeManager::mkCodeTree(Node label,
                                      size_t numArgs,
                                      bool filterCandidates)
{
  d_trees.emplace_back(new CodeTree(label, numArgs, filterCandidates));
  CodeTree* t = d_trees.back().get();
  t->d_root = mkInit(numArgs);
  return t;
}

Instruction* CodeTreeManager::mkInit(size_t numArgs)
{
  Assert(numArgs >= 1);
  if (numArgs > 6)
  {
    return own(new InitN(numArgs));
  }
  return own(new Instruction(
      static_cast<Opcode>(static_cast<size_t>(Opcode::INIT1) + numArgs - 1)));
}

Compare* CodeTreeManager::mkCompare(size_t reg1, size_t reg2)
{
  return own(new Compare(reg1, reg2));
}

Check* CodeTreeManager::mkCheck(size_t reg, ENode* e)
{
  return own(new Check(reg, e));
}

Filter* CodeTreeManager::mkFilter(size_t reg, ApproxSet s)
{
  return own(new Filter(Opcode::FILTER, reg, s));
}

Filter* CodeTreeManager::mkPFilter(size_t reg, ApproxSet s)
{
  return own(new Filter(Opcode::PFILTER, reg, s));
}

Filter* CodeTreeManager::mkCFilter(size_t reg, ApproxSet s)
{
  return own(new Filter(Opcode::CFILTER, reg, s));
}

GetENode* CodeTreeManager::mkGetENode(size_t oreg, ENode* e)
{
  return own(new GetENode(oreg, e));
}

Choose* CodeTreeManager::mkChoose(Choose* alt)
{
  return own(new Choose(Opcode::CHOOSE, alt));
}

Choose* CodeTreeManager::mkNoop()
{
  return own(new Choose(Opcode::NOOP, nullptr));
}

Bind* CodeTreeManager::mkBind(Node label,
                              size_t numArgs,
                              size_t ireg,
                              size_t oreg)
{
  return own(new Bind(opcodeFor(Opcode::BIND1, Opcode::BINDN, numArgs),
                      label,
                      numArgs,
                      ireg,
                      oreg));
}

GetCgr* CodeTreeManager::mkGetCgr(Node label,
                                  size_t oreg,
                                  const std::vector<size_t>& iregs)
{
  ApproxSet s(d_egraph.getLabelHash(label));
  GetCgr* r = own(
      new GetCgr(opcodeFor(Opcode::GET_CGR1, Opcode::GET_CGRN, iregs.size()),
                 label,
                 s,
                 oreg));
  r->d_iregs = iregs;
  return r;
}

IsCgr* CodeTreeManager::mkIsCgr(Node label,
                                size_t ireg,
                                const std::vector<size_t>& iregs)
{
  IsCgr* r = own(new IsCgr(label, ireg));
  r->d_iregs = iregs;
  return r;
}

Yield* CodeTreeManager::mkYield(Node q,
                                Node pat,
                                const std::vector<size_t>& bindings)
{
  Assert(!bindings.empty());
  Yield* y = own(new Yield(
      opcodeFor(Opcode::YIELD1, Opcode::YIELDN, bindings.size()), q, pat));
  y->d_bindings = bindings;
  return y;
}

Continue* CodeTreeManager::mkCont(Node label,
                                  size_t numArgs,
                                  size_t oreg,
                                  ApproxSet s,
                                  const std::vector<Joint>& joints)
{
  Continue* c = own(new Continue(label, numArgs, oreg, s));
  c->d_joints = joints;
  return c;
}

void CodeTreeManager::setNext(Instruction* instr, Instruction* next)
{
  Instruction* old = instr->d_next;
  d_trail.onPop([instr, old]() { instr->d_next = old; });
  instr->d_next = next;
}

void CodeTreeManager::saveNumRegs(CodeTree* tree)
{
  size_t old = tree->d_numRegs;
  d_trail.onPop([tree, old]() { tree->d_numRegs = old; });
}

void CodeTreeManager::saveNumChoices(CodeTree* tree)
{
  size_t old = tree->d_numChoices;
  d_trail.onPop([tree, old]() { tree->d_numChoices = old; });
}

void CodeTreeManager::insertNewLblHash(Filter* instr, size_t h)
{
  ApproxSet old = instr->d_lblSet;
  d_trail.onPop([instr, old]() { instr->d_lblSet = old; });
  instr->d_lblSet.insert(h);
}

//-------------------------------------------------------------------- PathTree

PathTree::PathTree(const Path& p, size_t labelHash)
    : d_label(p.d_label),
      d_argIdx(p.d_argIdx),
      d_groundArgIdx(p.d_groundArgIdx),
      d_groundArg(p.d_groundArg),
      d_code(nullptr),
      d_filter(labelHash),
      d_sibling(nullptr),
      d_firstChild(nullptr),
      d_todoActive(false)
{
}

void PathTree::display(std::ostream& out, size_t indent) const
{
  const PathTree* curr = this;
  while (curr != nullptr)
  {
    for (size_t i = 0; i < indent; i++)
    {
      out << "  ";
    }
    out << curr->d_label << ":" << curr->d_argIdx;
    if (curr->d_groundArg != nullptr)
    {
      out << ":" << *curr->d_groundArg << ":" << curr->d_groundArgIdx;
    }
    out << " " << curr->d_filter << (curr->d_code == nullptr ? "" : " *")
        << std::endl;
    if (curr->d_firstChild != nullptr)
    {
      curr->d_firstChild->display(out, indent + 1);
    }
    curr = curr->d_sibling;
  }
}

//-------------------------------------------------------------------- Compiler

Compiler::Compiler(Env& env, EGraph& eg, CodeTreeManager& ctm, bool useFilters)
    : EnvObj(env),
      d_egraph(eg),
      d_ctm(ctm),
      d_useFilters(useFilters),
      d_tree(nullptr),
      d_numChoices(0),
      d_isTmpTree(false),
      d_failed(false)
{
}

void Compiler::setRegister(size_t reg, TNode p)
{
  if (reg >= d_registers.size())
  {
    d_registers.resize(reg + 1);
  }
  d_registers[reg] = p;
}

TNode Compiler::getRegister(size_t reg) const
{
  static Node nullNode;
  return reg < d_registers.size() ? d_registers[reg] : nullNode;
}

Compiler::CheckMark Compiler::getCheckMark(size_t reg) const
{
  return reg < d_mark.size() ? d_mark[reg] : CheckMark::NOT_CHECKED;
}

void Compiler::setCheckMark(size_t reg, CheckMark cm)
{
  if (reg >= d_mark.size())
  {
    d_mark.resize(reg + 1, CheckMark::NOT_CHECKED);
  }
  d_mark[reg] = cm;
}

bool Compiler::isPatVar(TNode n, size_t& varId) const
{
  std::map<Node, size_t>::const_iterator it = d_varIndex.find(n);
  if (it == d_varIndex.end())
  {
    return false;
  }
  varId = it->second;
  return true;
}

bool Compiler::isGround(TNode n) { return !expr::hasBoundVar(n); }

ENode* Compiler::mkENode(TNode n)
{
  ENode* e = d_egraph.addTerm(n);
  if (e == nullptr)
  {
    Trace("eager-mam") << "Mam: cannot compile, no enode for " << n
                       << std::endl;
    d_failed = true;
  }
  return e;
}

void Compiler::init(CodeTree* t, TNode q, TNode mp, size_t firstIdx)
{
  d_tree = t;
  d_quant = q;
  d_mp = mp;
  d_numChoices = 0;
  d_failed = false;
  d_todo.clear();
  std::fill(d_registers.begin(), d_registers.end(), Node::null());
  std::fill(d_mark.begin(), d_mark.end(), CheckMark::NOT_CHECKED);
  d_varIndex.clear();
  for (size_t i = 0, nvars = q[0].getNumChildren(); i < nvars; i++)
  {
    d_varIndex[q[0][i]] = i;
  }
  TNode p = mp[firstIdx];
  Assert(t->getRootLabel() == p.getOperator());
  for (size_t i = 0, nargs = p.getNumChildren(); i < nargs; i++)
  {
    setRegister(i + 1, p[i]);
    d_todo.push_back(i + 1);
  }
  d_vars.assign(q[0].getNumChildren(), -1);
}

bool Compiler::allArgsAreBoundVars(TNode n) const
{
  for (const Node& arg : n)
  {
    size_t varId;
    if (!isPatVar(arg, varId) || d_vars[varId] == -1)
    {
      return false;
    }
  }
  return true;
}

void Compiler::getStatsCore(TNode n, size_t& sz, size_t& numUnboundVars) const
{
  sz++;
  if (isGround(n))
  {
    return;
  }
  for (const Node& arg : n)
  {
    size_t varId;
    if (isPatVar(arg, varId))
    {
      sz++;
      if (d_vars[varId] == -1)
      {
        numUnboundVars++;
      }
    }
    else
    {
      getStatsCore(arg, sz, numUnboundVars);
    }
  }
}

void Compiler::getStats(TNode n, size_t& sz, size_t& numUnboundVars) const
{
  sz = 0;
  numUnboundVars = 0;
  getStatsCore(n, sz, numUnboundVars);
}

size_t Compiler::getNumBoundVarsCore(TNode n, bool& hasUnboundVars) const
{
  if (isGround(n))
  {
    return 0;
  }
  size_t r = 0;
  for (const Node& arg : n)
  {
    size_t varId;
    if (isPatVar(arg, varId))
    {
      if (d_vars[varId] != -1)
      {
        r++;
      }
      else
      {
        hasUnboundVars = true;
      }
    }
    else
    {
      r += getNumBoundVarsCore(arg, hasUnboundVars);
    }
  }
  return r;
}

size_t Compiler::getNumBoundVars(TNode n, bool& hasUnboundVars) const
{
  hasUnboundVars = false;
  return getNumBoundVarsCore(n, hasUnboundVars);
}

void Compiler::lineariseCore()
{
  // z3: compiler::linearise_core
  d_aux.clear();
  Node firstApp;
  bool hasFirstApp = false;
  size_t firstAppReg = 0;
  size_t firstAppSz = 0;
  size_t firstAppNumUnboundVars = 0;
  // generate the non-BIND operations first
  for (size_t reg : d_todo)
  {
    Node p = getRegister(reg);
    Assert(!p.isNull());
    size_t varId;
    if (isPatVar(p, varId))
    {
      if (d_vars[varId] != -1)
      {
        d_seq.push_back(
            d_ctm.mkCompare(static_cast<size_t>(d_vars[varId]), reg));
      }
      else
      {
        d_vars[varId] = static_cast<int64_t>(reg);
      }
      continue;
    }
    if (isGround(p))
    {
      // ground applications are viewed as constants and converted to enodes
      ENode* e = mkENode(p);
      if (e == nullptr)
      {
        return;
      }
      d_seq.push_back(d_ctm.mkCheck(reg, e));
      setCheckMark(reg, CheckMark::NOT_CHECKED);
      continue;
    }
    if (!p.hasOperator())
    {
      // a bound variable of an enclosing quantifier, which we cannot match on
      Trace("eager-mam") << "Mam: cannot compile pattern term " << p
                         << std::endl;
      d_failed = true;
      return;
    }
    std::map<Node, size_t>::const_iterator itm = d_matchedExprs.find(p);
    if (itm != d_matchedExprs.end() && itm->second != reg)
    {
      d_seq.push_back(d_ctm.mkCompare(itm->second, reg));
      setCheckMark(reg, CheckMark::NOT_CHECKED);
      continue;
    }
    d_matchedExprs[p] = reg;
    if (d_useFilters && getCheckMark(reg) != CheckMark::CHECK_SINGLETON)
    {
      ApproxSet s(d_egraph.getLabelHash(p.getOperator()));
      d_seq.push_back(d_ctm.mkFilter(reg, s));
      setCheckMark(reg, CheckMark::CHECK_SINGLETON);
    }
    if (hasFirstApp)
    {
      // try to select the best first application
      if (firstAppNumUnboundVars == 0)
      {
        d_aux.push_back(reg);
      }
      else
      {
        size_t sz;
        size_t numUnboundVars;
        getStats(p, sz, numUnboundVars);
        if (numUnboundVars == 0 || sz > firstAppSz
            || (sz == firstAppSz && numUnboundVars < firstAppNumUnboundVars))
        {
          d_aux.push_back(firstAppReg);
          firstApp = p;
          firstAppReg = reg;
          firstAppSz = sz;
          firstAppNumUnboundVars = numUnboundVars;
        }
        else
        {
          d_aux.push_back(reg);
        }
      }
    }
    else
    {
      firstApp = p;
      hasFirstApp = true;
      firstAppReg = reg;
      getStats(firstApp, firstAppSz, firstAppNumUnboundVars);
    }
  }

  if (hasFirstApp)
  {
    Node lbl = firstApp.getOperator();
    size_t numArgs = firstApp.getNumChildren();
    if (allArgsAreBoundVars(firstApp))
    {
      // all arguments are already bound, so the application can be looked up
      // rather than enumerated
      std::vector<size_t> iregs;
      for (const Node& arg : firstApp)
      {
        size_t varId;
        bool isv = isPatVar(arg, varId);
        Assert(isv && d_vars[varId] != -1);
        iregs.push_back(static_cast<size_t>(d_vars[varId]));
      }
      d_seq.push_back(d_ctm.mkIsCgr(lbl, firstAppReg, iregs));
    }
    else
    {
      size_t oreg = d_tree->d_numRegs;
      d_tree->d_numRegs += numArgs;
      for (size_t j = 0; j < numArgs; j++)
      {
        setRegister(oreg + j, firstApp[j]);
        d_aux.push_back(oreg + j);
      }
      d_seq.push_back(d_ctm.mkBind(lbl, numArgs, firstAppReg, oreg));
      d_numChoices++;
    }
    setCheckMark(firstAppReg, CheckMark::NOT_CHECKED);
  }
  d_todo.swap(d_aux);
}

size_t Compiler::genMpFilter(TNode n)
{
  // z3: compiler::gen_mp_filter
  if (isGround(n))
  {
    size_t oreg = d_tree->d_numRegs;
    d_tree->d_numRegs += 1;
    ENode* e = mkENode(n);
    if (e != nullptr)
    {
      d_seq.push_back(d_ctm.mkGetENode(oreg, e));
    }
    return oreg;
  }
  std::vector<size_t> iregs;
  for (const Node& arg : n)
  {
    size_t varId;
    if (isPatVar(arg, varId))
    {
      if (d_vars[varId] == -1)
      {
        d_failed = true;
        return 0;
      }
      iregs.push_back(static_cast<size_t>(d_vars[varId]));
    }
    else
    {
      iregs.push_back(genMpFilter(arg));
    }
  }
  size_t oreg = d_tree->d_numRegs;
  d_tree->d_numRegs += 1;
  if (!n.hasOperator())
  {
    d_failed = true;
    return oreg;
  }
  d_seq.push_back(d_ctm.mkGetCgr(n.getOperator(), oreg, iregs));
  return oreg;
}

void Compiler::lineariseMultiPattern(size_t firstIdx)
{
  // z3: compiler::linearise_multi_pattern
  size_t numPats = d_mp.getNumChildren();
  for (size_t i = 1; i < numPats; i++)
  {
    // select the pattern term with the most bound variables, preferring one
    // all of whose variables are already bound
    Node best;
    size_t bestNumBvars = 0;
    size_t bestJ = 0;
    bool foundBoundedMp = false;
    for (size_t j = 0; j < numPats; j++)
    {
      if (d_mpAlreadyProcessed[j])
      {
        continue;
      }
      Node p = d_mp[j];
      bool hasUnboundVars = false;
      size_t numBvars = getNumBoundVars(p, hasUnboundVars);
      if (!hasUnboundVars)
      {
        best = p;
        bestJ = j;
        foundBoundedMp = true;
        break;
      }
      if (best.isNull() || numBvars > bestNumBvars)
      {
        best = p;
        bestNumBvars = numBvars;
        bestJ = j;
      }
    }
    if (best.isNull())
    {
      continue;
    }
    d_mpAlreadyProcessed[bestJ] = true;
    Node p = best;
    if (!p.hasOperator())
    {
      d_failed = true;
      return;
    }
    Node lbl = p.getOperator();
    size_t numArgs = p.getNumChildren();
    ApproxSet s;
    if (d_useFilters)
    {
      s.insert(d_egraph.getLabelHash(lbl));
    }
    if (foundBoundedMp)
    {
      genMpFilter(p);
      if (d_failed)
      {
        return;
      }
      continue;
    }
    // CONTINUE: the pattern term still has unbound variables, so applications
    // of its top symbol have to be enumerated
    size_t oreg = d_tree->d_numRegs;
    d_tree->d_numRegs += numArgs;
    std::vector<Joint> joints;
    bool hasDepth1Joint = false;
    for (size_t j = 0; j < numArgs; j++)
    {
      Node curr = p[j];
      setRegister(oreg + j, curr);
      d_todo.push_back(oreg + j);
      size_t varId;
      if ((isPatVar(curr, varId) && d_vars[varId] >= 0) || isGround(curr))
      {
        hasDepth1Joint = true;
      }
    }
    if (hasDepth1Joint)
    {
      for (size_t j = 0; j < numArgs; j++)
      {
        Node curr = p[j];
        Joint joint;
        size_t varId;
        if (isPatVar(curr, varId))
        {
          if (d_vars[varId] >= 0)
          {
            joint.d_kind = Joint::Kind::VAR;
            joint.d_reg = static_cast<size_t>(d_vars[varId]);
          }
        }
        else if (isGround(curr))
        {
          ENode* e = mkENode(curr);
          if (e != nullptr)
          {
            joint.d_kind = Joint::Kind::GROUND_TERM;
            joint.d_enode = e;
          }
        }
        joints.push_back(joint);
      }
    }
    else
    {
      // depth 2 joints are only tried if there is no depth 1 joint
      for (size_t j = 0; j < numArgs; j++)
      {
        Node curr = p[j];
        Joint joint;
        size_t varIdIgnored;
        if (!isPatVar(curr, varIdIgnored) && curr.hasOperator())
        {
          size_t numArgs2 = curr.getNumChildren();
          for (size_t k = 0; k < numArgs2; k++)
          {
            size_t varId;
            if (!isPatVar(curr[k], varId) || d_vars[varId] < 0)
            {
              continue;
            }
            joint.d_kind = Joint::Kind::NESTED_VAR;
            joint.d_label = curr.getOperator();
            joint.d_argPos = k;
            joint.d_reg = static_cast<size_t>(d_vars[varId]);
            break;
          }
        }
        joints.push_back(joint);
      }
    }
    Assert(joints.size() == numArgs);
    d_seq.push_back(d_ctm.mkCont(lbl, numArgs, oreg, s, joints));
    d_numChoices++;
    while (!d_todo.empty())
    {
      lineariseCore();
      if (d_failed)
      {
        return;
      }
    }
  }
}

void Compiler::linearise(Instruction* head, size_t firstIdx)
{
  // z3: compiler::linearise
  d_seq.clear();
  d_matchedExprs.clear();
  while (!d_todo.empty())
  {
    lineariseCore();
    if (d_failed)
    {
      return;
    }
  }
  if (d_mp.getNumChildren() > 1)
  {
    d_mpAlreadyProcessed.assign(d_mp.getNumChildren(), false);
    d_mpAlreadyProcessed[firstIdx] = true;
    lineariseMultiPattern(firstIdx);
    if (d_failed)
    {
      return;
    }
  }
  // if the pattern does not capture all variables, it is not usable
  size_t numDecls = d_quant[0].getNumChildren();
  for (size_t i = 0; i < numDecls; i++)
  {
    if (d_vars[i] == -1)
    {
      Trace("eager-mam") << "Mam: pattern " << d_mp
                         << " does not bind all variables of " << d_quant
                         << std::endl;
      return;
    }
  }
  Assert(head->d_next == nullptr);
  std::vector<size_t> varRegs;
  for (size_t i = 0; i < numDecls; i++)
  {
    varRegs.push_back(static_cast<size_t>(d_vars[i]));
  }
  d_seq.push_back(d_ctm.mkYield(d_quant, d_mp, varRegs));
  for (Instruction* curr : d_seq)
  {
    head->d_next = curr;
    head = curr;
  }
}

void Compiler::setNext(Instruction* instr, Instruction* next)
{
  if (d_isTmpTree)
  {
    instr->d_next = next;
  }
  else
  {
    d_ctm.setNext(instr, next);
  }
}

/**
 * The number of simple alternatives find_best_child will look at before giving
 * up. z3: FIND_BEST_CHILD_THRESHOLD.
 */
static const size_t s_findBestChildThreshold = 64;
/**
 * The length below which a code sequence without branching is considered too
 * simple to be worth comparing. z3: SIMPLE_SEQ_THRESHOLD.
 */
static const size_t s_simpleSeqThreshold = 4;

Choose* Compiler::findBestChild(Choose* firstChild)
{
  // z3: compiler::find_best_child
  size_t numTooSimple = 0;
  Choose* bestChild = nullptr;
  size_t maxCompatibility = 0;
  Choose* currChild = firstChild;
  while (currChild != nullptr)
  {
    bool simple = false;
    size_t currCompatibility = getCompatibilityMeasure(currChild, simple);
    if (simple)
    {
      numTooSimple++;
      if (numTooSimple > s_findBestChildThreshold)
      {
        return nullptr;
      }
    }
    if (currCompatibility > maxCompatibility)
    {
      bestChild = currChild;
      maxCompatibility = currCompatibility;
    }
    currChild = currChild->d_alt;
  }
  return bestChild;
}

size_t Compiler::getPatLblHash(size_t reg)
{
  // z3: compiler::get_pat_lbl_hash
  Node p = getRegister(reg);
  Assert(!p.isNull());
  if (isGround(p))
  {
    ENode* e = mkENode(p);
    if (e == nullptr)
    {
      return 0;
    }
    if (!e->hasLblHash())
    {
      d_egraph.setLblHash(e, d_egraph.getLabelHashForTerm(p));
    }
    return e->getLblHash();
  }
  return d_egraph.getLabelHash(p.getOperator());
}

bool Compiler::isCompatible(Bind* instr)
{
  Node n = getRegister(instr->d_ireg);
  // a BIND of a ground term would be wasteful, and the rest of the code
  // assumes it does not happen
  return !n.isNull() && n.hasOperator() && !isGround(n)
         && n.getOperator() == instr->d_label
         && n.getNumChildren() == instr->d_numArgs;
}

bool Compiler::isCompatible(Compare* instr)
{
  Node n1 = getRegister(instr->d_reg1);
  return !n1.isNull() && n1 == getRegister(instr->d_reg2);
}

bool Compiler::isCompatible(Check* instr)
{
  Node n = getRegister(instr->d_reg);
  if (n.isNull() || !isGround(n))
  {
    return false;
  }
  ENode* e = mkENode(n);
  if (e == nullptr)
  {
    return false;
  }
  // it is safe to compare the representatives because the modifications of a
  // code tree are chronological
  return instr->d_enode->getRoot() == e->getRoot();
}

bool Compiler::isSemiCompatible(Check* instr)
{
  size_t reg = instr->d_reg;
  if (instr->d_enode != nullptr && !instr->d_enode->hasLblHash())
  {
    d_egraph.setLblHash(
        instr->d_enode,
        d_egraph.getLabelHashForTerm(instr->d_enode->getNode()));
  }
  Node n = getRegister(reg);
  return !n.isNull() && getCheckMark(reg) == CheckMark::NOT_CHECKED
         && isGround(n) && instr->d_enode != nullptr
         && getPatLblHash(reg) == instr->d_enode->getLblHash();
}

bool Compiler::isCompatible(Filter* instr)
{
  // FILTER is not compatible with ground terms, CFILTER is the filter for them
  size_t reg = instr->d_reg;
  Node n = getRegister(reg);
  if (!n.isNull() && n.hasOperator() && !isGround(n))
  {
    return instr->d_lblSet.mayContain(getPatLblHash(reg));
  }
  return false;
}

bool Compiler::isCfilterCompatible(Filter* instr)
{
  size_t reg = instr->d_reg;
  Node n = getRegister(reg);
  if (!n.isNull() && isGround(n))
  {
    return instr->d_lblSet.mayContain(getPatLblHash(reg));
  }
  return false;
}

bool Compiler::isSemiCompatible(Filter* instr)
{
  size_t reg = instr->d_reg;
  Node n = getRegister(reg);
  return !n.isNull() && getCheckMark(reg) == CheckMark::NOT_CHECKED
         && n.hasOperator() && !isGround(n);
}

bool Compiler::isCompatible(Continue* instr)
{
  for (size_t i = 0; i < instr->d_numArgs; i++)
  {
    if (!getRegister(instr->d_oreg + i).isNull())
    {
      return false;
    }
  }
  return true;
}

size_t Compiler::getCompatibilityMeasure(Choose* child, bool& simple)
{
  // z3: compiler::get_compatibility_measure
  simple = true;
  d_toReset.clear();
  size_t weight = 0;
  size_t numInstr = 0;
  Instruction* curr = child->d_next;
  while (curr != nullptr && curr->d_opcode != Opcode::CHOOSE
         && curr->d_opcode != Opcode::NOOP)
  {
    numInstr++;
    switch (curr->d_opcode)
    {
      case Opcode::BIND1:
      case Opcode::BIND2:
      case Opcode::BIND3:
      case Opcode::BIND4:
      case Opcode::BIND5:
      case Opcode::BIND6:
      case Opcode::BINDN:
      {
        Bind* b = static_cast<Bind*>(curr);
        if (isCompatible(b))
        {
          // the weight of BIND is bigger than of COMPARE and CHECK
          weight += 4;
          Node n = getRegister(b->d_ireg);
          for (size_t i = 0; i < b->d_numArgs; i++)
          {
            setRegister(b->d_oreg + i, n[i]);
            d_toReset.push_back(b->d_oreg + i);
          }
        }
      }
      break;
      case Opcode::COMPARE:
        if (isCompatible(static_cast<Compare*>(curr)))
        {
          weight += 2;
        }
        break;
      case Opcode::CHECK:
        if (isCompatible(static_cast<Check*>(curr)))
        {
          weight += 2;
        }
        else if (d_useFilters && isSemiCompatible(static_cast<Check*>(curr)))
        {
          weight += 1;
        }
        break;
      case Opcode::CFILTER:
        if (isCfilterCompatible(static_cast<Filter*>(curr)))
        {
          weight += 2;
        }
        break;
      case Opcode::FILTER:
        if (isCompatible(static_cast<Filter*>(curr)))
        {
          weight += 2;
        }
        else if (isSemiCompatible(static_cast<Filter*>(curr)))
        {
          weight += 1;
        }
        break;
      default: break;
    }
    curr = curr->d_next;
  }
  if (numInstr > s_simpleSeqThreshold
      || (curr != nullptr && curr->d_opcode == Opcode::CHOOSE))
  {
    simple = false;
  }
  for (size_t r : d_toReset)
  {
    setRegister(r, Node::null());
  }
  return weight;
}

void Compiler::insertInto(Instruction* head, size_t firstMpIdx)
{
  // z3: compiler::insert(instruction*, unsigned)
  for (;;)
  {
    d_compatible.clear();
    d_incompatible.clear();
    Instruction* curr = head->d_next;
    Instruction* last = head;
    while (curr != nullptr && curr->d_opcode != Opcode::CHOOSE
           && curr->d_opcode != Opcode::NOOP)
    {
      switch (curr->d_opcode)
      {
        case Opcode::BIND1:
        case Opcode::BIND2:
        case Opcode::BIND3:
        case Opcode::BIND4:
        case Opcode::BIND5:
        case Opcode::BIND6:
        case Opcode::BINDN:
        {
          Bind* bnd = static_cast<Bind*>(curr);
          if (isCompatible(bnd))
          {
            size_t ireg = bnd->d_ireg;
            d_todo.erase(std::remove(d_todo.begin(), d_todo.end(), ireg),
                         d_todo.end());
            setCheckMark(ireg, CheckMark::NOT_CHECKED);
            d_compatible.push_back(curr);
            Node n = getRegister(ireg);
            for (size_t i = 0; i < bnd->d_numArgs; i++)
            {
              setRegister(bnd->d_oreg + i, n[i]);
              d_todo.push_back(bnd->d_oreg + i);
            }
          }
          else
          {
            d_incompatible.push_back(curr);
          }
        }
        break;
        case Opcode::CHECK:
        {
          Check* chk = static_cast<Check*>(curr);
          if (isCompatible(chk))
          {
            d_todo.erase(std::remove(d_todo.begin(), d_todo.end(), chk->d_reg),
                         d_todo.end());
            setCheckMark(chk->d_reg, CheckMark::NOT_CHECKED);
            d_compatible.push_back(curr);
          }
          else if (d_useFilters && isSemiCompatible(chk))
          {
            // combine the two ground checks into a CFILTER
            size_t reg = chk->d_reg;
            if (!chk->d_enode->hasLblHash())
            {
              d_egraph.setLblHash(
                  chk->d_enode,
                  d_egraph.getLabelHashForTerm(chk->d_enode->getNode()));
            }
            ApproxSet s(chk->d_enode->getLblHash());
            s.insert(getPatLblHash(reg));
            Filter* newInstr = d_ctm.mkCFilter(reg, s);
            setCheckMark(reg, CheckMark::CHECK_SET);
            d_compatible.push_back(newInstr);
            d_incompatible.push_back(curr);
          }
          else
          {
            d_incompatible.push_back(curr);
          }
        }
        break;
        case Opcode::COMPARE:
        {
          Compare* cmp = static_cast<Compare*>(curr);
          if (isCompatible(cmp))
          {
            d_todo.erase(std::remove(d_todo.begin(), d_todo.end(), cmp->d_reg2),
                         d_todo.end());
            setCheckMark(cmp->d_reg2, CheckMark::NOT_CHECKED);
            size_t varId;
            if (isPatVar(getRegister(cmp->d_reg1), varId))
            {
              d_todo.erase(
                  std::remove(d_todo.begin(), d_todo.end(), cmp->d_reg1),
                  d_todo.end());
              setCheckMark(cmp->d_reg1, CheckMark::NOT_CHECKED);
              if (d_vars[varId] == -1)
              {
                d_vars[varId] = static_cast<int64_t>(cmp->d_reg1);
              }
            }
            d_compatible.push_back(curr);
          }
          else
          {
            d_incompatible.push_back(curr);
          }
        }
        break;
        case Opcode::CFILTER:
        {
          Filter* flt = static_cast<Filter*>(curr);
          Assert(d_useFilters);
          if (isCfilterCompatible(flt))
          {
            setCheckMark(flt->d_reg, CheckMark::CHECK_SINGLETON);
            d_compatible.push_back(curr);
          }
          else
          {
            d_incompatible.push_back(curr);
          }
        }
        break;
        case Opcode::FILTER:
        {
          Filter* flt = static_cast<Filter*>(curr);
          Assert(d_useFilters);
          if (isCompatible(flt))
          {
            setCheckMark(flt->d_reg,
                         flt->d_lblSet.size() == 1 ? CheckMark::CHECK_SINGLETON
                                                   : CheckMark::CHECK_SET);
            d_compatible.push_back(curr);
          }
          else if (isSemiCompatible(flt))
          {
            size_t reg = flt->d_reg;
            size_t h = getPatLblHash(reg);
            setCheckMark(reg, CheckMark::CHECK_SET);
            if (flt->d_lblSet.size() > 1)
            {
              d_ctm.insertNewLblHash(flt, h);
              d_compatible.push_back(curr);
            }
            else
            {
              ApproxSet newS(flt->d_lblSet);
              newS.insert(h);
              d_compatible.push_back(d_ctm.mkFilter(reg, newS));
              d_incompatible.push_back(curr);
            }
          }
          else
          {
            d_incompatible.push_back(curr);
          }
        }
        break;
        default: d_incompatible.push_back(curr); break;
      }
      last = curr;
      curr = curr->d_next;
    }

    if (d_incompatible.empty())
    {
      // the sequence starting at head is fully compatible
      if (curr == nullptr)
      {
        return;
      }
      Assert(curr->d_opcode == Opcode::CHOOSE);
      Choose* firstChild = static_cast<Choose*>(curr);
      Choose* bestChild = findBestChild(firstChild);
      if (bestChild == nullptr)
      {
        // no compatible alternative, add a new one:
        //   head -> c1 -> ... -> last -> newChild
        //   newChild: CHOOSE(firstChild) -> linearise
        Choose* newChild = d_ctm.mkChoose(firstChild);
        d_numChoices++;
        setNext(last, newChild);
        linearise(newChild, firstMpIdx);
        return;
      }
      head = bestChild;
      continue;
    }
    // Some instructions are incompatible. Given
    //   head -> c1 -> i1 -> c2 -> c3 -> i2 -> firstChildHead
    // the sequence becomes
    //   head -> c1 -> c2 -> c3 -> newChildHead1
    //   newChildHead1: CHOOSE(newChildHead2) -> i1 -> i2 -> firstChildHead
    //   newChildHead2: NOOP -> linearise()
    Assert(head->isInit() || !d_compatible.empty());
    Instruction* firstChildHead = curr;
    Choose* newChildHead2 = d_ctm.mkNoop();
    Choose* newChildHead1 = d_ctm.mkChoose(newChildHead2);
    d_numChoices++;
    curr = head;
    for (Instruction* instr : d_compatible)
    {
      setNext(curr, instr);
      curr = instr;
    }
    setNext(curr, newChildHead1);
    curr = newChildHead1;
    for (Instruction* inc : d_incompatible)
    {
      if (curr == newChildHead1)
      {
        // newChildHead1 is new, no undo information is needed
        curr->d_next = inc;
      }
      else
      {
        setNext(curr, inc);
      }
      curr = inc;
    }
    setNext(curr, firstChildHead);
    linearise(newChildHead2, firstMpIdx);
    return;
  }
}

CodeTree* Compiler::mkTree(TNode q,
                           TNode mp,
                           size_t firstIdx,
                           bool filterCandidates)
{
  // z3: compiler::mk_tree
  TNode p = mp[firstIdx];
  CodeTree* t =
      d_ctm.mkCodeTree(p.getOperator(), p.getNumChildren(), filterCandidates);
  t->d_patterns.push_back(mp);
  d_isTmpTree = false;
  init(t, q, mp, firstIdx);
  linearise(t->d_root, firstIdx);
  t->d_numChoices = d_numChoices;
  Trace("eager-mam-compiler") << "Mam: new tree for " << mp << ":" << std::endl;
  if (TraceIsOn("eager-mam-compiler"))
  {
    t->display(Trace("eager-mam-compiler"));
  }
  return t;
}

void Compiler::insert(
    CodeTree* t, TNode q, TNode mp, size_t firstIdx, bool isTmpTree)
{
  // z3: compiler::insert
  if (t->getExpectedNumArgs() != mp[firstIdx].getNumChildren())
  {
    // the arities differ, which can happen for n-ary operators; ignore the
    // pattern rather than risk a malformed tree
    return;
  }
  d_isTmpTree = isTmpTree;
  if (!isTmpTree)
  {
    d_ctm.saveNumRegs(t);
  }
  t->d_patterns.push_back(mp);
  init(t, q, mp, firstIdx);
  d_numChoices = t->d_numChoices;
  insertInto(t->d_root, firstIdx);
  if (d_numChoices > t->d_numChoices)
  {
    if (!isTmpTree)
    {
      d_ctm.saveNumChoices(t);
    }
    t->d_numChoices = d_numChoices;
  }
  Trace("eager-mam-compiler")
      << "Mam: tree after inserting " << mp << ":" << std::endl;
  if (TraceIsOn("eager-mam-compiler"))
  {
    t->display(Trace("eager-mam-compiler"));
  }
}

//----------------------------------------------------------------- Interpreter

Interpreter::Interpreter(Env& env, EGraph& eg, Mam& mam, bool useFilters)
    : EnvObj(env),
      d_egraph(eg),
      d_mam(mam),
      d_useFilters(useFilters),
      d_top(0),
      d_pc(nullptr),
      d_maxGeneration(0)
{
}

void Interpreter::init(CodeTree* t)
{
  if (d_registers.size() < t->getNumRegs())
  {
    d_registers.resize(t->getNumRegs(), nullptr);
  }
  if (d_bindings.size() < t->getNumRegs())
  {
    d_bindings.resize(t->getNumRegs(), nullptr);
  }
  if (d_backtrack.size() < t->getNumChoices())
  {
    d_backtrack.resize(t->getNumChoices());
  }
}

void Interpreter::updateMaxGeneration(ENode* n)
{
  d_maxGeneration = std::max(d_maxGeneration, n->getGeneration());
}

void Interpreter::getMinMaxTopGeneration(uint32_t& min, uint32_t& max)
{
  // z3: interpreter::get_min_max_top_generation
  Assert(!d_patternInstances.empty());
  if (d_minTopGeneration.empty())
  {
    min = max = d_patternInstances[0]->getGeneration();
    d_minTopGeneration.push_back(min);
    d_maxTopGeneration.push_back(max);
  }
  else
  {
    min = d_minTopGeneration.back();
    max = d_maxTopGeneration.back();
  }
  for (size_t i = d_minTopGeneration.size(); i < d_patternInstances.size(); i++)
  {
    uint32_t curr = d_patternInstances[i]->getGeneration();
    min = std::min(min, curr);
    d_minTopGeneration.push_back(min);
    max = std::max(max, curr);
    d_maxTopGeneration.push_back(max);
  }
}

ENode* Interpreter::getFirstFApp(TNode lbl, size_t numExpectedArgs, ENode* curr)
{
  // z3: interpreter::get_first_f_app
  ENode* first = curr;
  do
  {
    if (curr->getLabel() == lbl && curr->isCgr()
        && curr->getNumArgs() == numExpectedArgs)
    {
      updateMaxGeneration(curr);
      return curr;
    }
    curr = curr->getNext();
  } while (curr != first);
  return nullptr;
}

ENode* Interpreter::getNextFApp(TNode lbl,
                                size_t numExpectedArgs,
                                ENode* first,
                                ENode* curr)
{
  // z3: interpreter::get_next_f_app
  curr = curr->getNext();
  while (curr != first)
  {
    if (curr->getLabel() == lbl && curr->isCgr()
        && curr->getNumArgs() == numExpectedArgs)
    {
      updateMaxGeneration(curr);
      return curr;
    }
    curr = curr->getNext();
  }
  return nullptr;
}

bool Interpreter::execIsCgr(const IsCgr* instr)
{
  // z3: interpreter::exec_is_cgr
  size_t numArgs = instr->d_iregs.size();
  ENode* n = d_registers[instr->d_ireg];
  if (n == nullptr)
  {
    return false;
  }
  d_args.resize(numArgs);
  for (size_t i = 0; i < numArgs; i++)
  {
    ENode* a = d_registers[instr->d_iregs[i]];
    if (a == nullptr)
    {
      return false;
    }
    d_args[i] = a->getRoot();
  }
  ENode* first = n;
  do
  {
    if (n->getLabel() == instr->d_label && n->getNumArgs() == numArgs)
    {
      size_t i = 0;
      for (; i < numArgs; i++)
      {
        if (n->getArg(i)->getRoot() != d_args[i])
        {
          break;
        }
      }
      if (i == numArgs)
      {
        updateMaxGeneration(n);
        return true;
      }
    }
    n = n->getNext();
  } while (n != first);
  return false;
}

void Interpreter::mkDepth1Vector(ENode* n,
                                 TNode f,
                                 size_t i,
                                 std::vector<ENode*>& v)
{
  // z3: interpreter::mk_depth1_vector
  n = n->getRoot();
  for (ENode* p : n->getParents())
  {
    if (p->getLabel() == f && i < p->getNumArgs() && p->isCgr()
        && p->getArg(i)->getRoot() == n)
    {
      v.push_back(p);
    }
  }
}

bool Interpreter::mkDepth2Vector(const Joint& j,
                                 TNode f,
                                 size_t i,
                                 std::vector<ENode*>& v)
{
  // z3: interpreter::mk_depth2_vector
  ENode* n = d_registers[j.d_reg]->getRoot();
  if (n->getNumParents() == 0)
  {
    return false;
  }
  for (ENode* p : n->getParents())
  {
    if (p->getLabel() == j.d_label && p->getNumArgs() > j.d_argPos && p->isCgr()
        && p->getArg(j.d_argPos)->getRoot() == n)
    {
      ENode* pr = p->getRoot();
      for (ENode* p2 : pr->getParents())
      {
        if (p2->getLabel() == f && p2->isCgr() && i < p2->getNumArgs()
            && p2->getArg(i)->getRoot() == pr)
        {
          v.push_back(p2);
        }
      }
    }
  }
  return true;
}

ENode* Interpreter::initContinue(const Continue* c, size_t expectedNumArgs)
{
  // z3: interpreter::init_continue
  TNode lbl = c->d_label;
  size_t minSz = d_egraph.getNumENodesForLabel(lbl);
  size_t numArgs = c->d_numArgs;
  // quick filter: if a depth 1 joint has no parents at all, there is nothing
  // to enumerate
  for (size_t i = 0; i < numArgs; i++)
  {
    const Joint& j = c->d_joints[i];
    ENode* n = nullptr;
    if (j.d_kind == Joint::Kind::GROUND_TERM)
    {
      n = j.d_enode;
    }
    else if (j.d_kind == Joint::Kind::VAR)
    {
      n = d_registers[j.d_reg];
    }
    else
    {
      continue;
    }
    ENode* r = n->getRoot();
    if (d_useFilters && r->getPlbls().emptyIntersection(c->d_lblSet))
    {
      return nullptr;
    }
    if (r->getNumParents() == 0)
    {
      return nullptr;
    }
  }
  // traverse each joint and select the one giving the fewest candidates
  bool hasBest = false;
  std::vector<ENode*> bestV;
  for (size_t i = 0; i < numArgs; i++)
  {
    const Joint& j = c->d_joints[i];
    std::vector<ENode*> currV;
    bool hasCurr = false;
    switch (j.d_kind)
    {
      case Joint::Kind::NONE: break;
      case Joint::Kind::GROUND_TERM:
        mkDepth1Vector(j.d_enode, lbl, i, currV);
        hasCurr = true;
        break;
      case Joint::Kind::VAR:
        mkDepth1Vector(d_registers[j.d_reg], lbl, i, currV);
        hasCurr = true;
        break;
      case Joint::Kind::NESTED_VAR:
        hasCurr = mkDepth2Vector(j, lbl, i, currV);
        break;
    }
    if (hasCurr && currV.size() < minSz
        && (!hasBest || currV.size() < bestV.size()))
    {
      if (currV.empty())
      {
        return nullptr;
      }
      bestV = std::move(currV);
      hasBest = true;
    }
  }
  BacktrackPoint& bp = d_backtrack[d_top];
  bp.d_instr = c;
  bp.d_oldMaxGeneration = d_maxGeneration;
  if (hasBest)
  {
    bp.d_restOwned = std::move(bestV);
    bp.d_rest = &bp.d_restOwned;
  }
  else
  {
    bp.d_restOwned.clear();
    // The applications of a label do not change while we are matching, so it
    // is safe to point at the e-graph's list rather than copy it.
    bp.d_rest = &d_egraph.getENodesForLabel(lbl);
  }
  const std::vector<ENode*>& rest = *bp.d_rest;
  bp.d_restIdx = 0;
  for (; bp.d_restIdx < rest.size(); bp.d_restIdx++)
  {
    if (rest[bp.d_restIdx]->getNumArgs() == expectedNumArgs)
    {
      break;
    }
  }
  if (bp.d_restIdx >= rest.size())
  {
    return nullptr;
  }
  d_top++;
  updateMaxGeneration(rest[bp.d_restIdx]);
  return rest[bp.d_restIdx];
}

void Interpreter::setRegisters(size_t oreg, ENode* app, size_t numArgs)
{
  for (size_t i = 0; i < numArgs; i++)
  {
    d_registers[oreg + i] = app->getArg(i);
  }
}

bool Interpreter::backtrack()
{
  // z3: the backtrack label of interpreter::execute_core
  for (;;)
  {
    if (d_top == 0)
    {
      return false;
    }
    BacktrackPoint& bp = d_backtrack[d_top - 1];
    d_maxGeneration = bp.d_oldMaxGeneration;
    switch (bp.d_instr->d_opcode)
    {
      case Opcode::CHOOSE:
        d_pc = static_cast<const Choose*>(bp.d_instr)->d_alt;
        Assert(d_pc != nullptr);
        d_top--;
        return true;
      case Opcode::BIND1:
      case Opcode::BIND2:
      case Opcode::BIND3:
      case Opcode::BIND4:
      case Opcode::BIND5:
      case Opcode::BIND6:
      case Opcode::BINDN:
      {
        const Bind* b = static_cast<const Bind*>(bp.d_instr);
        ENode* n1 = d_registers[b->d_ireg];
        ENode* app = getNextFApp(b->d_label, b->d_numArgs, n1, bp.d_curr);
        if (app == nullptr)
        {
          d_top--;
          continue;
        }
        bp.d_curr = app;
        setRegisters(b->d_oreg, app, b->d_numArgs);
        d_pc = b->d_next;
        return true;
      }
      case Opcode::CONTINUE:
      {
        const Continue* c = static_cast<const Continue*>(bp.d_instr);
        const std::vector<ENode*>& rest = *bp.d_rest;
        bool found = false;
        for (bp.d_restIdx++; bp.d_restIdx < rest.size(); bp.d_restIdx++)
        {
          ENode* app = rest[bp.d_restIdx];
          if (app->getNumArgs() != c->d_numArgs)
          {
            continue;
          }
          // replace the top-level pattern instance of this CONTINUE
          Assert(!d_patternInstances.empty());
          if (d_patternInstances.size() == d_maxTopGeneration.size())
          {
            d_maxTopGeneration.pop_back();
            d_minTopGeneration.pop_back();
          }
          d_patternInstances.pop_back();
          d_patternInstances.push_back(app);
          updateMaxGeneration(app);
          setRegisters(c->d_oreg, app, c->d_numArgs);
          d_pc = c->d_next;
          found = true;
          break;
        }
        if (found)
        {
          return true;
        }
        d_top--;
        continue;
      }
      default: Unreachable(); return false;
    }
  }
}

bool Interpreter::executeCore(CodeTree* t, ENode* n)
{
  // z3: interpreter::execute_core
  if (t->getRoot() == nullptr)
  {
    return true;
  }
  Trace("eager-mam-exec") << "Mam: execute " << t->getRootLabel() << " on "
                          << *n << std::endl;
  d_patternInstances.clear();
  d_minTopGeneration.clear();
  d_maxTopGeneration.clear();
  d_patternInstances.push_back(n);
  d_maxGeneration = n->getGeneration();
  d_pc = t->getRoot();
  d_registers[0] = n;
  d_top = 0;

  for (;;)
  {
    if (d_pc == nullptr)
    {
      if (!backtrack())
      {
        return true;
      }
      continue;
    }
    Trace("eager-mam-exec") << "  " << *d_pc << std::endl;
    switch (d_pc->d_opcode)
    {
      case Opcode::INIT1:
      case Opcode::INIT2:
      case Opcode::INIT3:
      case Opcode::INIT4:
      case Opcode::INIT5:
      case Opcode::INIT6:
      case Opcode::INITN:
      {
        size_t numArgs = d_pc->d_opcode == Opcode::INITN
                             ? static_cast<const InitN*>(d_pc)->d_numArgs
                             : initArity(d_pc->d_opcode);
        ENode* app = d_registers[0];
        if (app->getNumArgs() != numArgs)
        {
          if (!backtrack())
          {
            return true;
          }
          continue;
        }
        setRegisters(1, app, numArgs);
        d_pc = d_pc->d_next;
      }
      break;
      case Opcode::COMPARE:
      {
        const Compare* c = static_cast<const Compare*>(d_pc);
        ENode* n1 = d_registers[c->d_reg1];
        ENode* n2 = d_registers[c->d_reg2];
        if (n1 == nullptr || n2 == nullptr || n1->getRoot() != n2->getRoot())
        {
          if (!backtrack())
          {
            return true;
          }
          continue;
        }
        d_pc = d_pc->d_next;
      }
      break;
      case Opcode::CHECK:
      {
        const Check* c = static_cast<const Check*>(d_pc);
        ENode* n1 = d_registers[c->d_reg];
        if (n1 == nullptr || c->d_enode == nullptr
            || n1->getRoot() != c->d_enode->getRoot())
        {
          if (!backtrack())
          {
            return true;
          }
          continue;
        }
        d_pc = d_pc->d_next;
      }
      break;
      // CFILTER and FILTER differ only for the compiler: the compiler never
      // merges two CFILTERs with different label sets, since CFILTER combines
      // CHECKs and FILTER combines BINDs.
      case Opcode::CFILTER:
      case Opcode::FILTER:
      {
        const Filter* f = static_cast<const Filter*>(d_pc);
        ENode* r = d_registers[f->d_reg]->getRoot();
        if (f->d_lblSet.emptyIntersection(r->getLbls()))
        {
          if (!backtrack())
          {
            return true;
          }
          continue;
        }
        d_pc = d_pc->d_next;
      }
      break;
      case Opcode::PFILTER:
      {
        const Filter* f = static_cast<const Filter*>(d_pc);
        ENode* r = d_registers[f->d_reg]->getRoot();
        if (f->d_lblSet.emptyIntersection(r->getPlbls()))
        {
          if (!backtrack())
          {
            return true;
          }
          continue;
        }
        d_pc = d_pc->d_next;
      }
      break;
      case Opcode::CHOOSE:
        d_backtrack[d_top].d_instr = d_pc;
        d_backtrack[d_top].d_oldMaxGeneration = d_maxGeneration;
        d_top++;
        d_pc = d_pc->d_next;
        break;
      case Opcode::NOOP:
        Assert(static_cast<const Choose*>(d_pc)->d_alt == nullptr);
        d_pc = d_pc->d_next;
        break;
      case Opcode::BIND1:
      case Opcode::BIND2:
      case Opcode::BIND3:
      case Opcode::BIND4:
      case Opcode::BIND5:
      case Opcode::BIND6:
      case Opcode::BINDN:
      {
        const Bind* b = static_cast<const Bind*>(d_pc);
        ENode* n1 = d_registers[b->d_ireg];
        Assert(n1 != nullptr);
        uint32_t currMaxGeneration = d_maxGeneration;
        ENode* app = getFirstFApp(b->d_label, b->d_numArgs, n1);
        if (app == nullptr)
        {
          if (!backtrack())
          {
            return true;
          }
          continue;
        }
        d_backtrack[d_top].d_instr = d_pc;
        d_backtrack[d_top].d_oldMaxGeneration = currMaxGeneration;
        d_backtrack[d_top].d_curr = app;
        d_top++;
        setRegisters(b->d_oreg, app, b->d_numArgs);
        d_pc = d_pc->d_next;
      }
      break;
      case Opcode::YIELD1:
      case Opcode::YIELD2:
      case Opcode::YIELD3:
      case Opcode::YIELD4:
      case Opcode::YIELD5:
      case Opcode::YIELD6:
      case Opcode::YIELDN:
      {
        const Yield* y = static_cast<const Yield*>(d_pc);
        size_t numBindings = y->d_bindings.size();
        d_bindings.resize(numBindings);
        for (size_t i = 0; i < numBindings; i++)
        {
          d_bindings[i] = d_registers[y->d_bindings[i]];
          Assert(d_bindings[i] != nullptr);
          d_maxGeneration =
              std::max(d_maxGeneration, d_bindings[i]->getGeneration());
        }
        uint32_t minTop = 0;
        uint32_t maxTop = 0;
        getMinMaxTopGeneration(minTop, maxTop);
        d_mam.onMatch(y->d_quant,
                      y->d_pattern,
                      d_bindings,
                      d_maxGeneration,
                      minTop,
                      maxTop);
        if (!backtrack())
        {
          return true;
        }
      }
      break;
      case Opcode::GET_ENODE:
      {
        const GetENode* g = static_cast<const GetENode*>(d_pc);
        d_registers[g->d_oreg] = g->d_enode;
        d_pc = d_pc->d_next;
      }
      break;
      case Opcode::GET_CGR1:
      case Opcode::GET_CGR2:
      case Opcode::GET_CGR3:
      case Opcode::GET_CGR4:
      case Opcode::GET_CGR5:
      case Opcode::GET_CGR6:
      case Opcode::GET_CGRN:
      {
        const GetCgr* g = static_cast<const GetCgr*>(d_pc);
        size_t numArgs = g->d_iregs.size();
        d_args.resize(numArgs);
        bool fail = false;
        for (size_t i = 0; i < numArgs; i++)
        {
          ENode* a = d_registers[g->d_iregs[i]];
          if (a == nullptr
              || (d_useFilters
                  && g->d_lblSet.emptyIntersection(a->getRoot()->getPlbls())))
          {
            fail = true;
            break;
          }
          d_args[i] = a;
        }
        ENode* n1 = fail ? nullptr : d_egraph.getENodeEqTo(g->d_label, d_args);
        if (n1 == nullptr)
        {
          if (!backtrack())
          {
            return true;
          }
          continue;
        }
        updateMaxGeneration(n1);
        d_registers[g->d_oreg] = n1;
        d_pc = d_pc->d_next;
      }
      break;
      case Opcode::IS_CGR:
        if (!execIsCgr(static_cast<const IsCgr*>(d_pc)))
        {
          if (!backtrack())
          {
            return true;
          }
          continue;
        }
        d_pc = d_pc->d_next;
        break;
      case Opcode::CONTINUE:
      {
        const Continue* c = static_cast<const Continue*>(d_pc);
        ENode* app = initContinue(c, c->d_numArgs);
        if (app == nullptr)
        {
          if (!backtrack())
          {
            return true;
          }
          continue;
        }
        d_patternInstances.push_back(app);
        setRegisters(c->d_oreg, app, c->d_numArgs);
        d_pc = d_pc->d_next;
      }
      break;
    }
  }
}

bool Interpreter::execute(CodeTree* t)
{
  // z3: interpreter::execute
  init(t);
  if (t->filterCandidates())
  {
    bool ok = true;
    for (ENode* app : t->getCandidates())
    {
      if (!app->isMarked() && app->isCgr())
      {
        if (!executeCore(t, app))
        {
          ok = false;
          break;
        }
        app->setMark(true);
      }
    }
    for (ENode* app : t->getCandidates())
    {
      if (app->isMarked())
      {
        app->setMark(false);
      }
    }
    return ok;
  }
  for (ENode* app : t->getCandidates())
  {
    if (app->isCgr() && !executeCore(t, app))
    {
      return false;
    }
  }
  return true;
}

//------------------------------------------------------------------------- Mam

Mam::Mam(Env& env, EGraph& eg, Trail& trail, bool useFilters)
    : EnvObj(env),
      d_egraph(eg),
      d_trail(trail),
      d_useFilters(useFilters),
      d_listener(nullptr),
      d_ctm(eg, trail),
      d_compiler(env, eg, d_ctm, useFilters),
      d_interpreter(env, eg, *this, useFilters),
      d_pc(ApproxSet::capacity * ApproxSet::capacity, nullptr),
      d_pp(ApproxSet::capacity * ApproxSet::capacity,
           std::pair<PathTree*, PathTree*>(nullptr, nullptr)),
      d_r1(nullptr),
      d_r2(nullptr)
{
}

Mam::~Mam() {}

CodeTree* Mam::getCodeTree(TNode label) const
{
  std::map<Node, CodeTree*>::const_iterator it = d_trees.find(label);
  return it == d_trees.end() ? nullptr : it->second;
}

void Mam::addCandidate(CodeTree* t, ENode* e)
{
  if (t == nullptr)
  {
    return;
  }
  if (!t->hasCandidates())
  {
    d_toMatch.push_back(t);
  }
  t->addCandidate(e);
  d_stats.d_numCandidates++;
  Trace("eager-mam") << "Mam: candidate " << *e << " for " << t->getRootLabel()
                     << std::endl;
}

void Mam::addCandidate(ENode* e)
{
  addCandidate(getCodeTree(e->getLabel()), e);
}

void Mam::notifyNewENode(ENode* e)
{
  // The label maintenance half of z3's mam::relevant_eh is done by the
  // e-graph, since it owns the label sets; this is the candidate half.
  if (e->getNumArgs() > 0)
  {
    addCandidate(e);
  }
}

void Mam::notifyPreMerge(ENode* r1, ENode* r2)
{
  d_stats.d_numMerges++;
  // z3: mam_impl::add_eq_eh. The label sets are unioned by the e-graph after
  // this returns; here we only look for the applications that the merge makes
  // congruent.
  d_r1 = r1;
  d_r2 = r2;
  processPc(r1, r2);
  processPc(r2, r1);
  processPp(r1, r2);
  d_r1 = nullptr;
  d_r2 = nullptr;
}

bool Mam::isEqModPending(ENode* n1, ENode* n2) const
{
  // z3: mam_impl::is_eq, equality modulo the equality being asserted
  ENode* s1 = n1->getRoot();
  ENode* s2 = n2->getRoot();
  return s1 == s2 || (s1 == d_r1 && s2 == d_r2) || (s2 == d_r1 && s1 == d_r2);
}

void Mam::processPc(ENode* r1, ENode* r2)
{
  // z3: mam_impl::process_pc
  const ApproxSet& plbls = r1->getPlbls();
  const ApproxSet& clbls = r2->getLbls();
  if (plbls.empty() || clbls.empty())
  {
    return;
  }
  for (size_t plbl1 : plbls)
  {
    for (size_t lbl2 : clbls)
    {
      collectParents(r1, d_pc[plbl1 * ApproxSet::capacity + lbl2]);
    }
  }
}

void Mam::processPp(ENode* r1, ENode* r2)
{
  // z3: mam_impl::process_pp
  const ApproxSet& plbls1 = r1->getPlbls();
  const ApproxSet& plbls2 = r2->getPlbls();
  if (plbls1.empty() || plbls2.empty())
  {
    return;
  }
  for (size_t plbl1 : plbls1)
  {
    for (size_t plbl2 : plbls2)
    {
      size_t h1 = plbl1;
      size_t h2 = plbl2;
      ENode* n1 = r1;
      ENode* n2 = r2;
      if (h1 > h2)
      {
        std::swap(h1, h2);
        std::swap(n1, n2);
      }
      const std::pair<PathTree*, PathTree*>& pt =
          d_pp[h1 * ApproxSet::capacity + h2];
      if (h1 == h2)
      {
        collectParents(n1->getNumParents() <= n2->getNumParents() ? n1 : n2,
                       pt.first);
      }
      else if (n1->getNumParents() <= n2->getNumParents())
      {
        collectParents(n1, pt.first);
      }
      else
      {
        collectParents(n2, pt.second);
      }
    }
  }
}

void Mam::collectParents(ENode* r, PathTree* t)
{
  // z3: mam_impl::collect_parents
  if (t == nullptr)
  {
    return;
  }
  std::vector<ENode*> toUnmark;
  std::vector<ENode*> toUnmark2;
  d_todo.clear();
  t->d_todo.clear();
  t->d_todo.push_back(r);
  t->d_todoActive = true;
  d_todo.push_back(t);
  for (size_t head = 0; head < d_todo.size(); head++)
  {
    PathTree* tc = d_todo[head];
    const ApproxSet& filter = tc->d_filter;
    for (ENode* n : tc->d_todo)
    {
      // Two kinds of mark are used: the first marks the parents that have been
      // processed, the second the class representatives that have been queued
      // for the next level. Using one for both makes z3 miss matches.
      ENode* currChild = n->getRoot();
      if (d_useFilters && currChild->getPlbls().emptyIntersection(filter))
      {
        continue;
      }
      for (ENode* currParent : currChild->getParents())
      {
        // equalities are never in the inverted path index
        if (currParent->getNode().getKind() == Kind::EQUAL)
        {
          continue;
        }
        TNode lbl = currParent->getLabel();
        ENode* currParentRoot = currParent->getRoot();
        ENode* currParentCg = currParent->getCgr();
        if (!filter.mayContain(d_egraph.getLabelHash(lbl))
            || currParent->isMarked()
            || !(currParentCg == currParent
                 || !isEqModPending(currParentCg, currParentRoot)))
        {
          continue;
        }
        for (PathTree* currTree = tc; currTree != nullptr;
             currTree = currTree->d_sibling)
        {
          if (currTree->d_label != lbl
              || currTree->d_argIdx >= currParent->getNumArgs()
              || currTree->d_groundArgIdx >= currParent->getNumArgs())
          {
            continue;
          }
          ENode* currParentChild =
              currParent->getArg(currTree->d_argIdx)->getRoot();
          // Filter 1: the class we came from is the argument of the parent
          if (currChild != currParentChild)
          {
            continue;
          }
          // Filter 2: the ground argument of the path, if any, matches
          if (currTree->d_groundArg != nullptr
              && !isEqModPending(currTree->d_groundArg,
                                 currParent->getArg(currTree->d_groundArgIdx)))
          {
            continue;
          }
          if (currTree->d_code != nullptr)
          {
            addCandidate(currTree->d_code, currParent);
          }
          if (currTree->d_firstChild != nullptr)
          {
            PathTree* child = currTree->d_firstChild;
            if (!child->d_todoActive)
            {
              child->d_todo.clear();
              child->d_todoActive = true;
              d_todo.push_back(child);
            }
            if (!currParentRoot->isMarked2())
            {
              child->d_todo.push_back(currParentRoot);
            }
          }
        }
        currParent->setMark(true);
        toUnmark.push_back(currParent);
        if (!currParentRoot->isMarked2())
        {
          currParentRoot->setMark2(true);
          toUnmark2.push_back(currParentRoot);
        }
      }
    }
    tc->d_todo.clear();
    tc->d_todoActive = false;
    // z3 removes both marks at the end of each level
    for (ENode* e : toUnmark)
    {
      e->setMark(false);
    }
    for (ENode* e : toUnmark2)
    {
      e->setMark2(false);
    }
    toUnmark.clear();
    toUnmark2.clear();
  }
  d_todo.clear();
}

bool Mam::hasWork() const
{
  return !d_toMatch.empty() || !d_newPatterns.empty();
}

void Mam::match()
{
  // z3: mam_impl::match
  d_stats.d_numMatchCalls++;
  for (CodeTree* t : d_toMatch)
  {
    Assert(t->hasCandidates());
    d_stats.d_numExecutions += t->getCandidates().size();
    if (!d_interpreter.execute(t))
    {
      return;
    }
    t->resetCandidates();
  }
  d_toMatch.clear();
  if (!d_newPatterns.empty())
  {
    matchNewPatterns();
    d_newPatterns.clear();
  }
}

void Mam::rematch()
{
  // z3: mam_impl::rematch
  for (const std::pair<const Node, CodeTree*>& p : d_trees)
  {
    CodeTree* t = p.second;
    d_interpreter.init(t);
    for (ENode* e : d_egraph.getENodesForLabel(t->getRootLabel()))
    {
      d_stats.d_numExecutions++;
      if (!d_interpreter.executeCore(t, e))
      {
        return;
      }
    }
  }
}

void Mam::matchNewPatterns()
{
  // z3: mam_impl::match_new_patterns. A pattern that was just added has to be
  // matched against the terms that already exist. z3 does this with a
  // throwaway code tree per top symbol, so that the permanent trees are not
  // re-run over all of their candidates.
  Trace("eager-mam") << "Mam: match " << d_newPatterns.size() << " new patterns"
                     << std::endl;
  std::map<Node, CodeTree*> tmpTrees;
  for (const std::pair<Node, Node>& qp : d_newPatterns)
  {
    TNode q = qp.first;
    TNode mp = qp.second;
    TNode p = mp[0];
    if (!p.hasOperator())
    {
      continue;
    }
    Node lbl = p.getOperator();
    if (d_egraph.getNumENodesForLabel(lbl) == 0)
    {
      continue;
    }
    std::map<Node, CodeTree*>::iterator it = tmpTrees.find(lbl);
    if (it == tmpTrees.end())
    {
      tmpTrees[lbl] = d_compiler.mkTree(q, mp, 0, false);
    }
    else
    {
      d_compiler.insert(it->second, q, mp, 0, true);
    }
  }
  for (const std::pair<const Node, CodeTree*>& kv : tmpTrees)
  {
    CodeTree* t = kv.second;
    d_interpreter.init(t);
    for (ENode* e : d_egraph.getENodesForLabel(kv.first))
    {
      d_stats.d_numExecutions++;
      if (!d_interpreter.executeCore(t, e))
      {
        return;
      }
    }
  }
}

void Mam::clearWork()
{
  // z3: mam_impl::pop_scope drops the pending candidates and patterns
  for (CodeTree* t : d_toMatch)
  {
    t->resetCandidates();
  }
  d_toMatch.clear();
  d_newPatterns.clear();
}

bool Mam::isShared(ENode* e) const
{
  return d_sharedTerms.find(e->getNode()) != d_sharedTerms.end();
}

void Mam::onMatch(TNode q,
                  TNode pat,
                  const std::vector<ENode*>& bindings,
                  uint32_t maxGeneration,
                  uint32_t minTopGeneration,
                  uint32_t maxTopGeneration)
{
  d_stats.d_numMatches++;
  if (d_listener != nullptr)
  {
    d_listener->onMatch(
        q, pat, bindings, maxGeneration, minTopGeneration, maxTopGeneration);
  }
}

void Mam::addPattern(TNode q, TNode mp)
{
  Assert(mp.getKind() == Kind::INST_PATTERN);
  // z3: mam_impl::add_pattern. Multi-patterns all of whose pattern terms are
  // ground, and multi-patterns containing a quantifier, are ignored.
  bool allGround = true;
  for (const Node& p : mp)
  {
    if (expr::hasBoundVar(p))
    {
      allGround = false;
    }
    if (expr::hasClosure(p))
    {
      Trace("eager-mam") << "Mam: skip pattern with a quantifier " << mp
                         << std::endl;
      return;
    }
  }
  if (allGround)
  {
    Trace("eager-mam") << "Mam: skip ground pattern " << mp << std::endl;
    return;
  }
  // the pattern must only use the variables of q, which the compiler assumes
  std::unordered_set<Node> fvs;
  expr::getFreeVariables(mp, fvs);
  std::unordered_set<Node> qvars(q[0].begin(), q[0].end());
  for (const Node& v : fvs)
  {
    if (qvars.find(v) == qvars.end())
    {
      Trace("eager-mam") << "Mam: skip pattern with a foreign variable " << mp
                         << std::endl;
      return;
    }
  }
  Trace("eager-mam") << "Mam: add pattern " << mp << " for " << q << std::endl;
  updateFilters(q, mp);
  collectGroundTerms(q, mp);
  d_newPatterns.emplace_back(q, mp);
  // The machine matches a multi-pattern starting from any of its pattern
  // terms, so a multi-pattern of n terms is inserted n times.
  for (size_t i = 0, npats = mp.getNumChildren(); i < npats; i++)
  {
    addPatternToTree(q, mp, i);
  }
}

void Mam::addPatternToTree(TNode q, TNode mp, size_t patIdx)
{
  // z3: code_tree_map::add_pattern
  TNode pat = mp[patIdx];
  if (!expr::hasBoundVar(pat) || !pat.hasOperator())
  {
    return;
  }
  Node label = pat.getOperator();
  CodeTree* t = getCodeTree(label);
  if (t == nullptr)
  {
    t = d_compiler.mkTree(q, mp, patIdx, false);
    d_trees[label] = t;
    d_trail.onPop([this, label]() { d_trees.erase(label); });
    return;
  }
  // the arities may differ for n-ary operators, in which case the pattern is
  // ignored by the compiler
  d_compiler.insert(t, q, mp, patIdx, false);
}

void Mam::collectGroundTerms(TNode q, TNode mp)
{
  // z3: mam_impl::collect_ground_exprs
  std::vector<TNode> todo;
  for (const Node& pat : mp)
  {
    todo.push_back(pat);
  }
  while (!todo.empty())
  {
    TNode n = todo.back();
    todo.pop_back();
    if (!expr::hasBoundVar(n))
    {
      if (d_egraph.addTerm(n) != nullptr && d_sharedTerms.insert(n).second)
      {
        Node nn = n;
        d_trail.onPop([this, nn]() { d_sharedTerms.erase(nn); });
      }
      continue;
    }
    for (const Node& nc : n)
    {
      todo.push_back(nc);
    }
  }
}

void Mam::updateFilters(TNode q, TNode mp)
{
  // z3: mam_impl::update_filters(quantifier, app)
  d_varIndex.clear();
  for (size_t i = 0, nvars = q[0].getNumChildren(); i < nvars; i++)
  {
    d_varIndex[q[0][i]] = i;
  }
  d_varPaths.clear();
  d_varPaths.resize(q[0].getNumChildren());
  d_tmpPaths.clear();
  // The filters have to be updated for each rotation of the multi-pattern,
  // since the machine may start matching from any of its pattern terms.
  for (size_t i = 0, npats = mp.getNumChildren(); i < npats; i++)
  {
    updateFilters(mp[i], nullptr, q, mp, i);
  }
}

ENode* Mam::getGroundArg(TNode pat, size_t& pos)
{
  // z3: mam_impl::get_ground_arg
  pos = 0;
  for (size_t i = 0, nargs = pat.getNumChildren(); i < nargs; i++)
  {
    if (!expr::hasBoundVar(pat[i]))
    {
      pos = i;
      return d_egraph.addTerm(pat[i]);
    }
  }
  return nullptr;
}

Path* Mam::mkPath(Node label,
                  size_t argIdx,
                  size_t groundArgIdx,
                  ENode* groundArg,
                  size_t patIdx,
                  Path* child)
{
  d_tmpPaths.emplace_back(
      new Path{label, argIdx, groundArgIdx, groundArg, patIdx, child});
  return d_tmpPaths.back().get();
}

void Mam::updateFilters(TNode pat, Path* p, TNode q, TNode mp, size_t patIdx)
{
  // z3: mam_impl::update_filters(app, path, quantifier, app, unsigned)
  if (!pat.hasOperator())
  {
    return;
  }
  size_t groundArgPos = 0;
  ENode* groundArg = getGroundArg(pat, groundArgPos);
  Node plbl = pat.getOperator();
  for (size_t i = 0, nargs = pat.getNumChildren(); i < nargs; i++)
  {
    TNode child = pat[i];
    Path* newPath = mkPath(plbl, i, groundArgPos, groundArg, patIdx, p);
    std::map<Node, size_t>::const_iterator itv = d_varIndex.find(child);
    if (itv != d_varIndex.end())
    {
      updateVars(itv->second, newPath, q, mp);
      continue;
    }
    if (!expr::hasBoundVar(child))
    {
      ENode* e = d_egraph.addTerm(child);
      if (e == nullptr)
      {
        continue;
      }
      d_egraph.markParentLabel(plbl);
      if (!e->hasLblHash())
      {
        d_egraph.setLblHash(e, d_egraph.getLabelHashForTerm(child));
      }
      updatePc(d_egraph.getLabelHash(plbl), e->getLblHash(), newPath, q, mp);
      continue;
    }
    if (!child.hasOperator())
    {
      // a bound variable of an enclosing quantifier, which addPattern rejects
      continue;
    }
    Node clbl = child.getOperator();
    d_egraph.markParentLabel(plbl);
    d_egraph.markChildLabel(clbl);
    updatePc(d_egraph.getLabelHash(plbl),
             d_egraph.getLabelHash(clbl),
             newPath,
             q,
             mp);
    updateFilters(child, newPath, q, mp, patIdx);
  }
}

void Mam::updateVars(size_t varId, Path* p, TNode q, TNode mp)
{
  // z3: mam_impl::update_vars
  std::vector<Path*>& varPaths = d_varPaths[varId];
  bool found = false;
  for (Path* curr : varPaths)
  {
    if (isEqualPath(curr, p))
    {
      found = true;
    }
    d_egraph.markParentLabel(curr->d_label);
    d_egraph.markParentLabel(p->d_label);
    updatePp(d_egraph.getLabelHash(curr->d_label),
             d_egraph.getLabelHash(p->d_label),
             curr,
             p,
             q,
             mp);
  }
  if (!found)
  {
    varPaths.push_back(p);
  }
}

bool Mam::isEqualPath(const Path* p1, const Path* p2)
{
  // z3: is_equal(path const*, path const*)
  for (;;)
  {
    if (p1->d_label != p2->d_label || p1->d_argIdx != p2->d_argIdx
        || p1->d_patternIdx != p2->d_patternIdx
        || (p1->d_child == nullptr) != (p2->d_child == nullptr))
    {
      return false;
    }
    if (p1->d_child == nullptr)
    {
      return true;
    }
    p1 = p1->d_child;
    p2 = p2->d_child;
  }
}

PathTree* Mam::mkPathTree(Path* p, TNode q, TNode mp)
{
  // z3: mam_impl::mk_path_tree
  Assert(p != nullptr);
  size_t patIdx = p->d_patternIdx;
  PathTree* head = nullptr;
  PathTree* prev = nullptr;
  PathTree* curr = nullptr;
  while (p != nullptr)
  {
    d_pathTrees.emplace_back(
        new PathTree(*p, d_egraph.getLabelHash(p->d_label)));
    curr = d_pathTrees.back().get();
    if (prev != nullptr)
    {
      prev->d_firstChild = curr;
    }
    if (head == nullptr)
    {
      head = curr;
    }
    prev = curr;
    p = p->d_child;
  }
  curr->d_code = d_compiler.mkTree(q, mp, patIdx, true);
  return head;
}

void Mam::insertPathTree(PathTree* t, Path* p, TNode q, TNode mp)
{
  // z3: mam_impl::insert(path_tree*, path*, ...)
  PathTree* head = t;
  PathTree* prevSibling = nullptr;
  bool foundLabel = false;
  while (t != nullptr)
  {
    if (t->d_label == p->d_label)
    {
      foundLabel = true;
      if (t->d_argIdx == p->d_argIdx && t->d_groundArg == p->d_groundArg
          && t->d_groundArgIdx == p->d_groundArgIdx)
      {
        // a compatible node
        if (p->d_child == nullptr)
        {
          if (t->d_code != nullptr)
          {
            d_compiler.insert(t->d_code, q, mp, p->d_patternIdx, false);
          }
          else
          {
            t->d_code = d_compiler.mkTree(q, mp, p->d_patternIdx, true);
            PathTree* tc = t;
            d_trail.onPop([tc]() { tc->d_code = nullptr; });
          }
        }
        else if (t->d_firstChild == nullptr)
        {
          t->d_firstChild = mkPathTree(p->d_child, q, mp);
          PathTree* tc = t;
          d_trail.onPop([tc]() { tc->d_firstChild = nullptr; });
        }
        else
        {
          insertPathTree(t->d_firstChild, p->d_child, q, mp);
        }
        return;
      }
    }
    prevSibling = t;
    t = t->d_sibling;
  }
  Assert(prevSibling != nullptr);
  prevSibling->d_sibling = mkPathTree(p, q, mp);
  PathTree* ps = prevSibling;
  d_trail.onPop([ps]() { ps->d_sibling = nullptr; });
  if (!foundLabel)
  {
    d_trail.restore(&head->d_filter);
    head->d_filter.insert(d_egraph.getLabelHash(p->d_label));
  }
}

void Mam::updatePc(size_t h1, size_t h2, Path* p, TNode q, TNode mp)
{
  // z3: mam_impl::update_pc
  PathTree*& slot = d_pc[h1 * ApproxSet::capacity + h2];
  if (slot != nullptr)
  {
    insertPathTree(slot, p, q, mp);
    return;
  }
  slot = mkPathTree(p, q, mp);
  PathTree** s = &slot;
  d_trail.onPop([s]() { *s = nullptr; });
}

void Mam::updatePp(size_t h1, size_t h2, Path* p1, Path* p2, TNode q, TNode mp)
{
  // z3: mam_impl::update_pp
  if (h1 == h2)
  {
    std::pair<PathTree*, PathTree*>& slot = d_pp[h1 * ApproxSet::capacity + h2];
    if (slot.first != nullptr)
    {
      insertPathTree(slot.first, p1, q, mp);
      if (!isEqualPath(p1, p2))
      {
        insertPathTree(slot.first, p2, q, mp);
      }
      return;
    }
    slot.first = mkPathTree(p1, q, mp);
    std::pair<PathTree*, PathTree*>* s = &slot;
    d_trail.onPop([s]() { s->first = nullptr; });
    insertPathTree(slot.first, p2, q, mp);
    return;
  }
  if (h1 > h2)
  {
    std::swap(h1, h2);
    std::swap(p1, p2);
  }
  std::pair<PathTree*, PathTree*>& slot = d_pp[h1 * ApproxSet::capacity + h2];
  if (slot.first != nullptr)
  {
    Assert(slot.second != nullptr);
    insertPathTree(slot.first, p1, q, mp);
    insertPathTree(slot.second, p2, q, mp);
    return;
  }
  slot.first = mkPathTree(p1, q, mp);
  slot.second = mkPathTree(p2, q, mp);
  std::pair<PathTree*, PathTree*>* s = &slot;
  d_trail.onPop([s]() {
    s->first = nullptr;
    s->second = nullptr;
  });
}

void Mam::display(std::ostream& out) const
{
  out << "mam: " << d_trees.size() << " code trees, " << d_toMatch.size()
      << " with pending candidates" << std::endl;
  for (const std::pair<const Node, CodeTree*>& p : d_trees)
  {
    p.second->display(out);
  }
  for (size_t i = 0; i < ApproxSet::capacity; i++)
  {
    for (size_t j = 0; j < ApproxSet::capacity; j++)
    {
      PathTree* pc = d_pc[i * ApproxSet::capacity + j];
      if (pc != nullptr)
      {
        out << "pc[" << i << "][" << j << "]:" << std::endl;
        pc->display(out, 1);
      }
      const std::pair<PathTree*, PathTree*>& pp =
          d_pp[i * ApproxSet::capacity + j];
      if (pp.first != nullptr)
      {
        out << "pp[" << i << "][" << j << "]:" << std::endl;
        pp.first->display(out, 1);
        if (pp.second != nullptr)
        {
          pp.second->display(out, 1);
        }
      }
    }
  }
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

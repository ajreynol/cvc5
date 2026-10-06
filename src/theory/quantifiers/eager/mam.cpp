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

#include <ostream>

#include "expr/node_algorithm.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

std::ostream& operator<<(std::ostream& out, const Instruction& i)
{
  switch (i.d_opcode)
  {
    case Opcode::INIT1:
    case Opcode::INIT2:
    case Opcode::INIT3:
    case Opcode::INIT4:
    case Opcode::INIT5:
    case Opcode::INIT6:
      out << "(INIT" << (static_cast<size_t>(i.d_opcode) + 1) << ")";
      break;
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
      out << "(BIND " << b.d_label << " " << b.d_ireg << " " << b.d_oreg << ")";
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
      out << "(YIELD " << y.d_quant.getId();
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
      out << "(CONTINUE " << static_cast<const Continue&>(i).d_label << ")";
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
      out << "(GET_CGR " << static_cast<const GetCgr&>(i).d_label << ")";
      break;
    case Opcode::IS_CGR:
      out << "(IS_CGR " << static_cast<const IsCgr&>(i).d_label << ")";
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
    if (curr->d_opcode == Opcode::CHOOSE || curr->d_opcode == Opcode::NOOP)
    {
      Choose* c = static_cast<Choose*>(curr);
      if (c->d_alt != nullptr)
      {
        displaySeq(out, c->d_alt, indent + 1);
      }
    }
    curr = curr->d_next;
  }
}

void CodeTree::display(std::ostream& out) const
{
  out << "code-tree for " << d_rootLabel << "/" << d_numArgs << " ("
      << d_patterns.size() << " patterns, " << d_numRegs << " registers, "
      << d_candidates.size() << " pending candidates)" << std::endl;
  displaySeq(out, d_root, 1);
}

//------------------------------------------------------------- CodeTreeManager

CodeTreeManager::CodeTreeManager() {}
CodeTreeManager::~CodeTreeManager() {}

CodeTree* CodeTreeManager::mkCodeTree(Node label,
                                      size_t numArgs,
                                      bool filterCandidates)
{
  d_trees.emplace_back(new CodeTree(label, numArgs, filterCandidates));
  return d_trees.back().get();
}

void CodeTreeManager::reset()
{
  d_trees.clear();
  d_instructions.clear();
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

Compiler::Compiler(Env& env, EGraph& eg, CodeTreeManager& ctm)
    : EnvObj(env), d_egraph(eg), d_ctm(ctm)
{
}

CodeTree* Compiler::mkTree(TNode q,
                           TNode mp,
                           size_t patIdx,
                           bool filterCandidates)
{
  TNode pat = mp[patIdx];
  CodeTree* t = d_ctm.mkCodeTree(
      pat.getOperator(), pat.getNumChildren(), filterCandidates);
  t->d_patterns.push_back(mp);
  // TODO: compile mp into instructions, with mp[patIdx] taken as the first
  // pattern term. z3: compiler::mk_tree, which emits
  //   INIT<n> (BIND|CHECK|COMPARE|FILTER|GET_CGR|GET_ENODE)* (CONTINUE ...)*
  //   YIELD<k>
  // See README.md section 9, step 2.
  Trace("eager-mam") << "Mam: compile (not implemented) " << mp << " from "
                     << patIdx << std::endl;
  return t;
}

void Compiler::insert(CodeTree* t,
                      TNode q,
                      TNode mp,
                      CVC5_UNUSED size_t patIdx,
                      CVC5_UNUSED bool isTmpTree)
{
  t->d_patterns.push_back(mp);
  // TODO: insert mp into t, sharing the longest compatible prefix of
  // instructions and introducing a CHOOSE where they diverge. z3:
  // compiler::insert. See README.md section 9, step 2.
  Trace("eager-mam") << "Mam: insert (not implemented) " << mp << std::endl;
}

//----------------------------------------------------------------- Interpreter

Interpreter::Interpreter(Env& env, EGraph& eg, Mam& mam)
    : EnvObj(env), d_egraph(eg), d_mam(mam), d_pc(nullptr), d_maxGeneration(0)
{
}

void Interpreter::init(CodeTree* t)
{
  d_registers.assign(t->getNumRegs(), nullptr);
  d_backtrack.assign(t->getNumChoices(), BacktrackPoint());
}

bool Interpreter::execute(CodeTree* t)
{
  init(t);
  for (ENode* c : t->getCandidates())
  {
    if (!executeCore(t, c))
    {
      return false;
    }
  }
  return true;
}

bool Interpreter::executeCore(CodeTree* t, ENode* n)
{
  Trace("eager-mam") << "Mam: execute " << t->getRootLabel() << " on " << *n
                     << std::endl;
  if (t->getRoot() == nullptr)
  {
    // the compiler has not run, there is nothing to execute
    return true;
  }
  d_patternInstances.clear();
  d_patternInstances.push_back(n);
  d_maxGeneration = n->getGeneration();
  d_registers[0] = n;
  d_pc = t->getRoot();
  // TODO: the main loop, i.e. the switch over the opcodes with the
  // backtracking stack. z3: interpreter::execute_core. See README.md section
  // 9, step 3.
  return true;
}

//------------------------------------------------------------------------- Mam

Mam::Mam(Env& env, EGraph& eg, Trail& trail, bool useFilters)
    : EnvObj(env),
      d_egraph(eg),
      d_trail(trail),
      d_useFilters(useFilters),
      d_listener(nullptr),
      d_compiler(env, eg, d_ctm),
      d_interpreter(env, eg, *this),
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
        if (!filter.mayContain(d_egraph.getLabelHash(lbl))
            || currParent->isMarked())
        {
          continue;
        }
        // z3 additionally skips parents that are congruent to another member
        // of their own class (curr_parent->get_cg()); since the mirror does
        // not maintain a congruence table, we consider them all. The
        // fingerprint set removes the resulting duplicate instances. See
        // README.md section 8.
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
      if (!d_interpreter.executeCore(t, e))
      {
        return;
      }
    }
  }
}

void Mam::matchNewPatterns()
{
  // z3: mam_impl::match_new_patterns. A new pattern must be matched against
  // the terms that already exist, which z3 does with a throwaway code tree per
  // top symbol so that the permanent trees are not re-run.
  // TODO: requires the compiler. See README.md section 9, step 2.
  Trace("eager-mam") << "Mam: match " << d_newPatterns.size()
                     << " new patterns (not implemented)" << std::endl;
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
  if (!pat.hasOperator())
  {
    Trace("eager-mam") << "Mam: skip pattern term without an operator " << pat
                       << std::endl;
    return;
  }
  Node label = pat.getOperator();
  CodeTree* t = getCodeTree(label);
  if (t == nullptr)
  {
    t = d_compiler.mkTree(q, mp, patIdx, true);
    d_trees[label] = t;
    d_trail.onPop([this, label]() { d_trees.erase(label); });
  }
  else
  {
    d_compiler.insert(t, q, mp, patIdx, false);
  }
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
        Node clblGround =
            child.hasOperator() ? child.getOperator() : Node(child);
        d_egraph.setLblHash(e, d_egraph.getLabelHash(clblGround));
      }
      updatePc(d_egraph.getLabelHash(plbl), e->getLblHash(), newPath, q, mp);
      continue;
    }
    if (!child.hasOperator())
    {
      // a bound variable of an enclosing quantifier, or a term we cannot
      // match on
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

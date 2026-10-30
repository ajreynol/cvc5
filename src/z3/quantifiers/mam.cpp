/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The Matching Abstract Machine: Z3's E-matching engine.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation),
 * file src/smt/mam.cpp, and recast in cvc5 style.
 *
 * Three data structures do the work:
 *
 * - A *code tree* per function symbol: patterns are compiled into instruction
 *   sequences that bind, compare and filter enodes, and patterns sharing a
 *   prefix share the instructions for it. The interpreter runs a tree against
 *   a candidate enode and yields every match it finds.
 * - *Label sets*: each equivalence class carries a 64-bit over-approximation
 *   of the function symbols occurring in it (`lbls`) and of those applied to
 *   it (`plbls`), so most candidates can be rejected by a bitwise test.
 * - The *inverted path index* (path trees): when two classes merge, it says
 *   which code trees could possibly fire, so that matching is incremental
 *   rather than rerun from scratch.
 *
 * Note on the binding convention. Z3 numbers quantified variables by de
 * Bruijn index, where index 0 is the *last* declared variable, and its YIELD
 * instruction reverses the registers to recover declaration order. This port
 * numbers them by de Bruijn *level*, which is already declaration order (see
 * quantifier_normalizer.h), so YIELD here does not reverse. In both cases
 * `bindings[i]` ends up being the binding of the i-th declared variable.
 */

#include "z3/quantifiers/mam.h"

#include <algorithm>
#include <cstring>
#include <deque>
#include <memory>
#include <ostream>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "base/output.h"
#include "context/cdhashset.h"
#include "expr/node_algorithm.h"
#include "expr/node_manager.h"
#include "util/hash.h"
#include "z3/quantifiers/enode.h"
#include "z3/quantifiers/quantifier_manager.h"
#include "z3/quantifiers/quantifier_normalizer.h"
#include "z3/quantifiers/smt_context.h"
#include "z3/quantifiers/statistics.h"
#include "z3/quantifiers/trail.h"

namespace cvc5::internal {
namespace z3 {

namespace {

/**
 * A pointer with a tag in its low bits, or a small integer boxed with a tag,
 * so that the joints of the matching code stay one word wide (Z3's tptr.h).
 * Everything allocated here is at least four-byte aligned, which leaves the
 * low two bits free.
 */
class TaggedPtr
{
  static constexpr uintptr_t s_tagBits = 2;
  static constexpr uintptr_t s_tagMask = (uintptr_t(1) << s_tagBits) - 1;

 public:
  TaggedPtr() : d_data(0) {}

  /** Tag a pointer. */
  template <typename T>
  static TaggedPtr tag(T* p, uintptr_t t)
  {
    Assert(t <= s_tagMask);
    Assert((reinterpret_cast<uintptr_t>(p) & s_tagMask) == 0)
        << "tagged pointer is not sufficiently aligned";
    TaggedPtr r;
    r.d_data = reinterpret_cast<uintptr_t>(p) | t;
    return r;
  }

  /** Box a small integer with a tag. */
  static TaggedPtr boxInt(uint32_t val, uintptr_t t)
  {
    Assert(t <= s_tagMask);
    TaggedPtr r;
    r.d_data = (static_cast<uintptr_t>(val) << s_tagBits) | t;
    return r;
  }

  uintptr_t getTag() const { return d_data & s_tagMask; }

  template <typename T>
  T* untag() const
  {
    return reinterpret_cast<T*>(d_data & ~s_tagMask);
  }

  uint32_t unboxInt() const
  {
    return static_cast<uint32_t>(d_data >> s_tagBits);
  }

 private:
  uintptr_t d_data;
};

/** True if the pattern subterm n contains no quantified variable. */
bool isGroundPat(TNode n) { return !expr::hasBoundVar(n); }

/** Internalize a ground pattern subterm and return its enode. */
ENode* mkPatENode(SmtContext& ctx, QuantifierManager& qm, TNode qa, TNode n)
{
  ctx.internalize(n, false, qm.getGeneration(qa));
  ENode* e = ctx.getEGraph().getENode(n);
  Assert(e != nullptr);
  return e;
}

// ---------------------------------------------------------------- auxiliary

/**
 * Maps a function symbol to a six-bit hash, which is the symbol's position in
 * the label sets carried by equivalence classes.
 */
class LabelHasher
{
 public:
  LabelHasher(EGraph& eg) : d_egraph(eg) {}

  uint8_t operator()(TNode lbl)
  {
    uint32_t lblId = d_egraph.getDeclId(lbl);
    if (lblId >= d_lbl2Hash.size())
    {
      d_lbl2Hash.resize(lblId + 1, -1);
    }
    if (d_lbl2Hash[lblId] == -1)
    {
      mkLblHash(lblId);
    }
    Assert(d_lbl2Hash[lblId] >= 0);
    return static_cast<uint8_t>(d_lbl2Hash[lblId]);
  }

 private:
  void mkLblHash(uint32_t lblId)
  {
    uint64_t h = fnv1a::fnv1a_64(lblId);
    d_lbl2Hash[lblId] = static_cast<int8_t>(h & (approxSetCapacity() - 1));
  }

  EGraph& d_egraph;
  /** Cache: declaration id to hash. */
  std::vector<int8_t> d_lbl2Hash;
};

// ------------------------------------------------------------- instructions

enum Opcode
{
  INIT = 0,
  BIND,
  YIELD,
  COMPARE,
  CHECK,
  FILTER,
  CFILTER,
  CHOOSE,
  NOOP,
  CONTINUE,
  GET_ENODE,
  GET_CGR,
  IS_CGR
};

struct Instr
{
  Opcode d_opcode;
  Instr* d_next = nullptr;
  bool isInit() const { return d_opcode == INIT; }
};

struct Compare : public Instr
{
  uint32_t d_reg1;
  uint32_t d_reg2;
};

struct Check : public Instr
{
  uint32_t d_reg;
  ENode* d_enode;
};

struct Filter : public Instr
{
  uint32_t d_reg;
  ApproxSet d_lblSet;
};

/** Copy d_enode into register d_oreg. */
struct GetENodeInstr : public Instr
{
  uint32_t d_oreg;
  ENode* d_enode;
};

struct Choose : public Instr
{
  Choose* d_alt;
};

/**
 * A depth-two joint, used by CONTINUE. A joint comes in three forms:
 *   1) a variable:       (f ... X ...)
 *   2) a ground term:    (f ... t ...)
 *   3) a depth-2 joint:  (f ... (g ... X ...) ...)
 * The third form stores g, the position of X, and the register holding X.
 * Z3 has no support for depth-three joints.
 */
struct Joint2
{
  TNode d_decl;
  uint32_t d_argPos;
  /** the register that contains the variable */
  uint32_t d_reg;
};

/** The tags of the joint array of a CONTINUE instruction. */
enum JointTag
{
  NULL_TAG = 0,
  GROUND_TERM_TAG = 1,
  VAR_TAG = 2,
  NESTED_VAR_TAG = 3
};

struct Cont : public Instr
{
  TNode d_label;
  uint16_t d_numArgs;
  uint32_t d_oreg;
  /** a singleton set containing d_label */
  ApproxSet d_lblSet;
  /**
   * An array of d_numArgs tagged words, each of which is either nothing
   * (NULL_TAG), a register holding a bound variable (VAR_TAG), an enode for a
   * ground term (GROUND_TERM_TAG), or a Joint2 (NESTED_VAR_TAG). It is stored
   * directly after this object.
   */
  TaggedPtr* jointsPtr()
  {
    return reinterpret_cast<TaggedPtr*>(reinterpret_cast<char*>(this)
                                        + sizeof(Cont));
  }
  const TaggedPtr* jointsPtr() const
  {
    return reinterpret_cast<const TaggedPtr*>(
        reinterpret_cast<const char*>(this) + sizeof(Cont));
  }
};

struct Bind : public Instr
{
  TNode d_label;
  uint16_t d_numArgs;
  uint32_t d_ireg;
  uint32_t d_oreg;
};

struct GetCgr : public Instr
{
  TNode d_label;
  ApproxSet d_lblSet;
  uint16_t d_numArgs;
  bool d_commutative;
  uint32_t d_oreg;
  uint32_t* iregsPtr()
  {
    return reinterpret_cast<uint32_t*>(reinterpret_cast<char*>(this)
                                       + sizeof(GetCgr));
  }
  const uint32_t* iregsPtr() const
  {
    return reinterpret_cast<const uint32_t*>(reinterpret_cast<const char*>(this)
                                             + sizeof(GetCgr));
  }
};

struct Yield : public Instr
{
  TNode d_qa;
  uint16_t d_numBindings;
  uint32_t* bindingsPtr()
  {
    return reinterpret_cast<uint32_t*>(reinterpret_cast<char*>(this)
                                       + sizeof(Yield));
  }
  const uint32_t* bindingsPtr() const
  {
    return reinterpret_cast<const uint32_t*>(reinterpret_cast<const char*>(this)
                                             + sizeof(Yield));
  }
};

struct IsCgr : public Instr
{
  uint32_t d_ireg;
  TNode d_label;
  uint16_t d_numArgs;
  uint32_t* iregsPtr()
  {
    return reinterpret_cast<uint32_t*>(reinterpret_cast<char*>(this)
                                       + sizeof(IsCgr));
  }
  const uint32_t* iregsPtr() const
  {
    return reinterpret_cast<const uint32_t*>(reinterpret_cast<const char*>(this)
                                             + sizeof(IsCgr));
  }
};

// --------------------------------------------------------------- code tree

class Compiler;
class CodeTreeManager;

class CodeTree
{
 public:
  CodeTree(TNode lbl, uint16_t numArgs, bool filterCandidates)
      : d_rootLbl(lbl),
        d_numArgs(numArgs),
        d_filterCandidates(filterCandidates),
        d_numRegs(numArgs + 1),
        d_numChoices(0),
        d_root(nullptr)
  {
  }

  uint32_t expectedNumArgs() const { return d_numArgs; }

  uint32_t getNumRegs() const { return d_numRegs; }

  uint32_t getNumChoices() const { return d_numChoices; }

  TNode getRootLbl() const { return d_rootLbl; }

  bool filterCandidates() const { return d_filterCandidates; }

  const Instr* getRoot() const { return d_root; }

  void addCandidate(ENode* n) { d_candidates.push_back(n); }

  /**
   * Drop the duplicate candidates once there are enough of them to be worth
   * the sweep. The threshold doubles so that the compression stays amortized.
   */
  void compressCandidates()
  {
    if (d_candidates.size() < d_candidateGcThreshold)
    {
      return;
    }
    std::unordered_set<ENode*> seen;
    size_t j = 0;
    for (ENode* n : d_candidates)
    {
      if (seen.insert(n).second)
      {
        d_candidates[j++] = n;
      }
    }
    d_candidates.resize(j);
    if (2 * d_candidates.size() > d_candidateGcThreshold)
    {
      d_candidateGcThreshold *= 2;
    }
  }

  bool hasCandidates() const { return !d_candidates.empty(); }

  void resetCandidates() { d_candidates.clear(); }

  const ENodeVector& getCandidates() const { return d_candidates; }

 private:
  friend class Compiler;
  friend class CodeTreeManager;

  TNode d_rootLbl;
  /** needed to avoid matching an n-ary application of the wrong arity */
  uint32_t d_numArgs;
  bool d_filterCandidates;
  uint32_t d_numRegs;
  uint32_t d_numChoices;
  Instr* d_root;
  ENodeVector d_candidates;
  size_t d_candidateGcThreshold = 10000;
};

// ------------------------------------------------------- code tree manager

class CodeTreeManager
{
 public:
  CodeTreeManager(LabelHasher& h, TrailStack& s)
      : d_lblHasher(h), d_trailStack(s)
  {
  }

  CodeTree* mkCodeTree(TNode lbl, uint16_t numArgs, bool filterCandidates)
  {
    CodeTree* r = new CodeTree(lbl, numArgs, filterCandidates);
    Assert(numArgs >= 1);
    r->d_root = mkInstr<Instr>(INIT, sizeof(Instr));
    return r;
  }

  Joint2* mkJoint2(TNode f, uint32_t pos, uint32_t reg)
  {
    Joint2* r = static_cast<Joint2*>(d_trailStack.allocate(sizeof(Joint2)));
    new (r) Joint2{f, pos, reg};
    return r;
  }

  Compare* mkCompare(uint32_t reg1, uint32_t reg2)
  {
    Compare* r = mkInstr<Compare>(COMPARE, sizeof(Compare));
    r->d_reg1 = reg1;
    r->d_reg2 = reg2;
    return r;
  }

  Check* mkCheck(uint32_t reg, ENode* n)
  {
    Check* r = mkInstr<Check>(CHECK, sizeof(Check));
    r->d_reg = reg;
    r->d_enode = n;
    return r;
  }

  /** A filter, for op FILTER or CFILTER. */
  Filter* mkFilter(Opcode op, uint32_t reg, ApproxSet s)
  {
    Assert(op == FILTER || op == CFILTER);
    Filter* r = mkInstr<Filter>(op, sizeof(Filter));
    r->d_reg = reg;
    r->d_lblSet = s;
    return r;
  }

  GetENodeInstr* mkGetENode(uint32_t reg, ENode* n)
  {
    GetENodeInstr* s = mkInstr<GetENodeInstr>(GET_ENODE, sizeof(GetENodeInstr));
    s->d_oreg = reg;
    s->d_enode = n;
    return s;
  }

  Choose* mkChoose(Choose* alt)
  {
    Choose* r = mkInstr<Choose>(CHOOSE, sizeof(Choose));
    r->d_alt = alt;
    return r;
  }

  Choose* mkNoop()
  {
    Choose* r = mkInstr<Choose>(NOOP, sizeof(Choose));
    r->d_alt = nullptr;
    return r;
  }

  Bind* mkBind(TNode lbl, uint16_t numArgs, uint32_t ireg, uint32_t oreg)
  {
    Assert(numArgs >= 1);
    Bind* r = mkInstr<Bind>(BIND, sizeof(Bind));
    r->d_label = lbl;
    r->d_numArgs = numArgs;
    r->d_ireg = ireg;
    r->d_oreg = oreg;
    return r;
  }

  GetCgr* mkGetCgr(TNode lbl,
                   bool commutative,
                   uint32_t oreg,
                   uint16_t numArgs,
                   const uint32_t* iregs)
  {
    Assert(numArgs >= 1);
    GetCgr* r =
        mkInstr<GetCgr>(GET_CGR, sizeof(GetCgr) + numArgs * sizeof(uint32_t));
    r->d_label = lbl;
    r->d_lblSet.insert(d_lblHasher(lbl));
    r->d_commutative = commutative;
    r->d_oreg = oreg;
    r->d_numArgs = numArgs;
    std::memcpy(r->iregsPtr(), iregs, sizeof(uint32_t) * numArgs);
    return r;
  }

  IsCgr* mkIsCgr(TNode lbl,
                 uint32_t ireg,
                 uint16_t numArgs,
                 const uint32_t* iregs)
  {
    Assert(numArgs >= 1);
    IsCgr* r =
        mkInstr<IsCgr>(IS_CGR, sizeof(IsCgr) + numArgs * sizeof(uint32_t));
    r->d_label = lbl;
    r->d_ireg = ireg;
    r->d_numArgs = numArgs;
    std::memcpy(r->iregsPtr(), iregs, sizeof(uint32_t) * numArgs);
    return r;
  }

  Yield* mkYield(TNode qa,
                 uint16_t numBindings,
                 const uint32_t* bindings)
  {
    Assert(numBindings >= 1);
    Yield* y =
        mkInstr<Yield>(YIELD, sizeof(Yield) + numBindings * sizeof(uint32_t));
    y->d_qa = qa;
    y->d_numBindings = numBindings;
    std::memcpy(y->bindingsPtr(), bindings, sizeof(uint32_t) * numBindings);
    return y;
  }

  Cont* mkCont(TNode lbl,
               uint16_t numArgs,
               uint32_t oreg,
               const ApproxSet& s,
               const TaggedPtr* joints)
  {
    Assert(numArgs >= 1);
    Cont* r =
        mkInstr<Cont>(CONTINUE, sizeof(Cont) + numArgs * sizeof(TaggedPtr));
    r->d_label = lbl;
    r->d_numArgs = numArgs;
    r->d_oreg = oreg;
    r->d_lblSet = s;
    std::memcpy(r->jointsPtr(), joints, numArgs * sizeof(TaggedPtr));
    return r;
  }

  void setNext(Instr* instr, Instr* newNext)
  {
    d_trailStack.push(ValueTrail<Instr*>(instr->d_next));
    instr->d_next = newNext;
  }

  void saveNumRegs(CodeTree* tree)
  {
    d_trailStack.push(ValueTrail<uint32_t>(tree->d_numRegs));
  }

  void saveNumChoices(CodeTree* tree)
  {
    d_trailStack.push(ValueTrail<uint32_t>(tree->d_numChoices));
  }

  void insertNewLblHash(Filter* instr, uint32_t h)
  {
    d_trailStack.push(ValueTrail<ApproxSet>(instr->d_lblSet));
    instr->d_lblSet.insert(h);
  }

 private:
  template <typename OP>
  OP* mkInstr(Opcode op, size_t size)
  {
    void* mem = d_trailStack.allocate(size);
    OP* r = new (mem) OP;
    r->d_opcode = op;
    r->d_next = nullptr;
    return r;
  }

  LabelHasher& d_lblHasher;
  TrailStack& d_trailStack;
};

// ----------------------------------------------------------------- compiler

/**
 * Compiles a pattern into a code tree, reusing as much of an existing tree as
 * it can. The registers of the compiler hold pattern subterms; the registers
 * of the interpreter hold the enodes matched against them.
 */
class Compiler
{
 public:
  Compiler(SmtContext& ctx,
           QuantifierManager& qm,
           CodeTreeManager& ctMg,
           LabelHasher& h)
      : d_context(ctx),
        d_qm(qm),
        d_ctManager(ctMg),
        d_lblHasher(h),
        d_tree(nullptr),
        d_numChoices(0),
        d_isTmpTree(false)
  {
  }

  /**
   * Create a code tree for qa using the multi-pattern mp, with mp's
   * firstIdx-th pattern as the head, i.e. the one processed first.
   */
  CodeTree* mkTree(TNode qa, TNode mp, size_t firstIdx, bool filterCandidates)
  {
    TNode p = mp[firstIdx];
    uint16_t numArgs = static_cast<uint16_t>(p.getNumChildren());
    CodeTree* r = d_ctManager.mkCodeTree(getDecl(p), numArgs, filterCandidates);
    init(r, qa, mp, firstIdx);
    linearise(r->d_root, firstIdx);
    r->d_numChoices = d_numChoices;
    return r;
  }

  /**
   * Insert a pattern into an existing code tree. If isTmpTree is false the
   * updates are recorded on the trail.
   */
  void insert(
      CodeTree* tree, TNode qa, TNode mp, size_t firstIdx, bool isTmpTree)
  {
    if (tree->expectedNumArgs() != mp[firstIdx].getNumChildren())
    {
      // The arity has to be checked because of the n-ary + and * operators:
      // the E-matching engine was built when every application of a symbol
      // had the symbol's arity. A pattern with an unexpected arity is
      // ignored, which is not ideal but avoids a crash.
      Trace("z3-mam-newpat")
          << "  ARITY MISMATCH for " << getDecl(mp[firstIdx])
          << ": tree expects " << tree->expectedNumArgs() << " but pattern has "
          << mp[firstIdx].getNumChildren() << std::endl;
      return;
    }
    d_isTmpTree = isTmpTree;
    if (!isTmpTree)
    {
      d_ctManager.saveNumRegs(tree);
    }
    init(tree, qa, mp, firstIdx);
    d_numChoices = tree->d_numChoices;
    insert(tree->d_root, firstIdx);
    if (d_numChoices > tree->d_numChoices)
    {
      if (!isTmpTree)
      {
        d_ctManager.saveNumChoices(tree);
      }
      tree->d_numChoices = d_numChoices;
    }
  }

 private:
  enum CheckMark
  {
    NOT_CHECKED,
    CHECK_SET,
    CHECK_SINGLETON
  };

  void setRegister(uint32_t reg, TNode p)
  {
    if (reg >= d_registers.size())
    {
      d_registers.resize(reg + 1, Node::null());
    }
    d_registers[reg] = Node(p);
  }

  TNode getRegister(uint32_t reg) const
  {
    return reg < d_registers.size() ? TNode(d_registers[reg]) : TNode::null();
  }

  CheckMark getCheckMark(uint32_t reg) const
  {
    return reg < d_mark.size() ? d_mark[reg] : NOT_CHECKED;
  }

  void setCheckMark(uint32_t reg, CheckMark cm)
  {
    if (reg >= d_mark.size())
    {
      d_mark.resize(reg + 1, NOT_CHECKED);
    }
    d_mark[reg] = cm;
  }

  void init(CodeTree* t, TNode qa, TNode mp, size_t firstIdx)
  {
    d_tree = t;
    d_qa = qa;
    d_mp = mp;
    d_numChoices = 0;
    d_todo.clear();
    std::fill(d_registers.begin(), d_registers.end(), Node::null());

    TNode p = mp[firstIdx];
    Assert(t->getRootLbl() == getDecl(p));
    size_t numArgs = p.getNumChildren();
    for (size_t i = 0; i < numArgs; ++i)
    {
      setRegister(i + 1, p[i]);
      d_todo.push_back(i + 1);
    }
    size_t numDecls = qa[0].getNumChildren();
    if (numDecls > d_vars.size())
    {
      d_vars.resize(numDecls, -1);
    }
    for (size_t j = 0; j < numDecls; ++j)
    {
      d_vars[j] = -1;
    }
  }

  /**
   * True if every argument of n is a variable that will already be bound at
   * this point in the code sequence.
   */
  bool allArgsAreBoundVars(TNode n)
  {
    for (const Node& arg : n)
    {
      if (!isVar(arg))
      {
        return false;
      }
      if (d_vars[varIndex(arg)] == -1)
      {
        return false;
      }
    }
    return true;
  }

  void getStatsCore(TNode n, uint32_t& sz, uint32_t& numUnboundVars)
  {
    sz++;
    if (isGroundPat(n))
    {
      return;
    }
    for (const Node& arg : n)
    {
      if (isVar(arg))
      {
        sz++;
        if (d_vars[varIndex(arg)] == -1)
        {
          numUnboundVars++;
        }
      }
      else if (isApp(arg))
      {
        getStatsCore(arg, sz, numUnboundVars);
      }
    }
  }

  /** The size and number of unbound variables of a pattern. */
  void getStats(TNode n, uint32_t& sz, uint32_t& numUnboundVars)
  {
    sz = 0;
    numUnboundVars = 0;
    getStatsCore(n, sz, numUnboundVars);
  }

  /**
   * Process the registers in d_todo. The ones that produce something other
   * than a BIND are processed first, then a single BIND is produced. On
   * return, d_todo holds the registers that still need a BIND plus the
   * registers that BIND created. The new instructions are appended to d_seq.
   */
  void lineariseCore()
  {
    d_aux.clear();
    Node firstApp;
    uint32_t firstAppReg = 0;
    uint32_t firstAppSz = 0;
    uint32_t firstAppNumUnboundVars = 0;
    // generate the non-BIND operations first
    for (uint32_t reg : d_todo)
    {
      TNode p = getRegister(reg);
      Assert(!isQuantifier(p));
      if (isVar(p))
      {
        uint32_t varId = varIndex(p);
        if (d_vars[varId] != -1)
        {
          d_seq.push_back(
              d_ctManager.mkCompare(static_cast<uint32_t>(d_vars[varId]), reg));
        }
        else
        {
          d_vars[varId] = static_cast<int32_t>(reg);
        }
        continue;
      }

      Assert(isApp(p));

      if (isGroundPat(p))
      {
        // Ground applications are constants: they are turned into enodes
        // eagerly and only have to be compared.
        ENode* e = mkPatENode(d_context, d_qm, d_qa, p);
        d_seq.push_back(d_ctManager.mkCheck(reg, e));
        // reset the mark: the register was fully processed
        setCheckMark(reg, NOT_CHECKED);
        continue;
      }

      auto itm = d_matchedExprs.find(p);
      if (itm != d_matchedExprs.end() && reg != itm->second)
      {
        d_seq.push_back(d_ctManager.mkCompare(itm->second, reg));
        setCheckMark(reg, NOT_CHECKED);
        continue;
      }
      d_matchedExprs[p] = reg;

      if (getCheckMark(reg) != CHECK_SINGLETON)
      {
        ApproxSet s(d_lblHasher(getDecl(p)));
        d_seq.push_back(d_ctManager.mkFilter(FILTER, reg, s));
        setCheckMark(reg, CHECK_SINGLETON);
      }

      if (!firstApp.isNull())
      {
        // Pick the best candidate for the single BIND: an application with no
        // unbound variables is ideal, otherwise prefer the largest one, and
        // among equally large ones the one with fewest unbound variables.
        if (firstAppNumUnboundVars == 0)
        {
          d_aux.push_back(reg);
        }
        else
        {
          uint32_t sz;
          uint32_t numUnboundVars;
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
        firstAppReg = reg;
        getStats(firstApp, firstAppSz, firstAppNumUnboundVars);
      }
    }

    if (!firstApp.isNull())
    {
      // d_todo contained at least one non-ground application
      TNode lbl = getDecl(firstApp);
      uint16_t numArgs = static_cast<uint16_t>(firstApp.getNumChildren());
      if (allArgsAreBoundVars(firstApp))
      {
        // Every argument is bound already, so the application only has to be
        // looked up rather than branched over: IS_CGR instead of BIND.
        std::vector<uint32_t> iregs;
        for (uint16_t i = 0; i < numArgs; ++i)
        {
          TNode arg = firstApp[i];
          Assert(isVar(arg));
          Assert(d_vars[varIndex(arg)] != -1);
          iregs.push_back(static_cast<uint32_t>(d_vars[varIndex(arg)]));
        }
        d_seq.push_back(
            d_ctManager.mkIsCgr(lbl, firstAppReg, numArgs, iregs.data()));
      }
      else
      {
        uint32_t oreg = d_tree->d_numRegs;
        d_tree->d_numRegs += numArgs;
        for (uint16_t j = 0; j < numArgs; ++j)
        {
          setRegister(oreg + j, firstApp[j]);
          d_aux.push_back(oreg + j);
        }
        d_seq.push_back(d_ctManager.mkBind(lbl, numArgs, firstAppReg, oreg));
        d_numChoices++;
      }
      setCheckMark(firstAppReg, NOT_CHECKED);
    }

    // d_aux becomes the new todo list
    d_todo.swap(d_aux);
  }

  uint32_t getNumBoundVarsCore(TNode n, bool& hasUnboundVars)
  {
    uint32_t r = 0;
    if (isGroundPat(n))
    {
      return 0;
    }
    for (const Node& arg : n)
    {
      if (isVar(arg))
      {
        if (d_vars[varIndex(arg)] != -1)
        {
          r++;
        }
        else
        {
          hasUnboundVars = true;
        }
      }
      else if (isApp(arg))
      {
        r += getNumBoundVarsCore(arg, hasUnboundVars);
      }
    }
    return r;
  }

  uint32_t getNumBoundVars(TNode n, bool& hasUnboundVars)
  {
    hasUnboundVars = false;
    return getNumBoundVarsCore(n, hasUnboundVars);
  }

  /**
   * Compile a pattern all of whose variables are already bound, returning the
   * register that will hold the enode congruent to it.
   */
  uint32_t genMpFilter(TNode n)
  {
    if (isGroundPat(n))
    {
      uint32_t oreg = d_tree->d_numRegs;
      d_tree->d_numRegs += 1;
      ENode* e = mkPatENode(d_context, d_qm, d_qa, n);
      d_seq.push_back(d_ctManager.mkGetENode(oreg, e));
      return oreg;
    }

    std::vector<uint32_t> iregs;
    size_t numArgs = n.getNumChildren();
    for (size_t i = 0; i < numArgs; ++i)
    {
      TNode arg = n[i];
      if (isVar(arg))
      {
        Assert(d_vars[varIndex(arg)] != -1);
        iregs.push_back(static_cast<uint32_t>(d_vars[varIndex(arg)]));
      }
      else
      {
        iregs.push_back(genMpFilter(arg));
      }
    }
    uint32_t oreg = d_tree->d_numRegs;
    d_tree->d_numRegs += 1;
    d_seq.push_back(d_ctManager.mkGetCgr(getDecl(n),
                                         isCommutative(n),
                                         oreg,
                                         static_cast<uint16_t>(numArgs),
                                         iregs.data()));
    return oreg;
  }

  /** Process the patterns of a multi-pattern other than firstIdx. */
  void lineariseMultiPattern()
  {
    size_t numArgs = d_mp.getNumChildren();
    for (size_t i = 1; i < numArgs; ++i)
    {
      // select the pattern with the most bound variables
      Node best;
      uint32_t bestNumBvars = 0;
      size_t bestJ = 0;
      bool foundBoundedMp = false;
      for (size_t j = 0; j < numArgs; ++j)
      {
        if (d_mpAlreadyProcessed[j])
        {
          continue;
        }
        TNode p = d_mp[j];
        bool hasUnboundVars = false;
        uint32_t numBvars = getNumBoundVars(p, hasUnboundVars);
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
      TNode p = best;
      TNode lbl = getDecl(p);
      uint16_t numPArgs = static_cast<uint16_t>(p.getNumChildren());
      ApproxSet s;
      s.insert(d_lblHasher(lbl));

      if (foundBoundedMp)
      {
        genMpFilter(p);
        continue;
      }
      // Some variables are still unbound, so this pattern has to be searched
      // over: CONTINUE.
      uint32_t oreg = d_tree->d_numRegs;
      d_tree->d_numRegs += numPArgs;
      std::vector<TaggedPtr> joints;
      // a joint of depth one is a bound variable or a ground term
      bool hasDepth1Joint = false;
      for (uint16_t j = 0; j < numPArgs; ++j)
      {
        TNode curr = p[j];
        Assert(!isQuantifier(curr));
        setRegister(oreg + j, curr);
        d_todo.push_back(oreg + j);

        if ((isVar(curr) && d_vars[varIndex(curr)] >= 0)
            || (isApp(curr) && isGroundPat(curr)))
        {
          hasDepth1Joint = true;
        }
      }

      if (hasDepth1Joint)
      {
        for (uint16_t j = 0; j < numPArgs; ++j)
        {
          TNode curr = p[j];
          if (isVar(curr))
          {
            uint32_t varId = varIndex(curr);
            if (d_vars[varId] >= 0)
            {
              joints.push_back(TaggedPtr::boxInt(
                  static_cast<uint32_t>(d_vars[varId]), VAR_TAG));
            }
            else
            {
              joints.push_back(TaggedPtr());
            }
            continue;
          }
          Assert(isApp(curr));
          if (isGroundPat(curr))
          {
            ENode* e = mkPatENode(d_context, d_qm, d_qa, curr);
            joints.push_back(TaggedPtr::tag(e, GROUND_TERM_TAG));
            continue;
          }
          joints.push_back(TaggedPtr());
        }
      }
      else
      {
        // Only look for depth-two joints when there is no depth-one joint.
        for (uint16_t j = 0; j < numPArgs; ++j)
        {
          TNode curr = p[j];
          if (!isApp(curr))
          {
            joints.push_back(TaggedPtr());
            continue;
          }
          size_t numArgs2 = curr.getNumChildren();
          size_t k = 0;
          for (; k < numArgs2; ++k)
          {
            TNode arg = curr[k];
            if (!isVar(arg))
            {
              continue;
            }
            uint32_t varId = varIndex(arg);
            if (d_vars[varId] < 0)
            {
              continue;
            }
            Joint2* newJoint =
                d_ctManager.mkJoint2(getDecl(curr),
                                     static_cast<uint32_t>(k),
                                     static_cast<uint32_t>(d_vars[varId]));
            joints.push_back(TaggedPtr::tag(newJoint, NESTED_VAR_TAG));
            break;  // found a joint
          }
          if (k == numArgs2)
          {
            joints.push_back(TaggedPtr());  // no joint found
          }
        }
      }
      Assert(joints.size() == numPArgs);
      d_seq.push_back(
          d_ctManager.mkCont(lbl, numPArgs, oreg, s, joints.data()));
      d_numChoices++;
      while (!d_todo.empty())
      {
        lineariseCore();
      }
    }
  }

  /** Produce the instructions for the registers in d_todo. */
  void linearise(Instr* head, size_t firstIdx)
  {
    d_seq.clear();
    d_matchedExprs.clear();
    while (!d_todo.empty())
    {
      lineariseCore();
    }

    if (d_mp.getNumChildren() > 1)
    {
      d_mpAlreadyProcessed.assign(d_mp.getNumChildren(), false);
      d_mpAlreadyProcessed[firstIdx] = true;
      lineariseMultiPattern();
    }

    // the pattern must capture every variable
    size_t numDecls = d_qa[0].getNumChildren();
    for (size_t i = 0; i < numDecls; ++i)
    {
      if (d_vars[i] == -1)
      {
        return;
      }
    }

    Assert(head->d_next == nullptr);

    // Note d_vars is indexed by de Bruijn level, i.e. by declaration
    // position, so no reversal is needed here or in YIELD.
    std::vector<uint32_t> varRegs(numDecls);
    for (size_t i = 0; i < numDecls; ++i)
    {
      varRegs[i] = static_cast<uint32_t>(d_vars[i]);
    }
    d_seq.push_back(d_ctManager.mkYield(
        d_qa, static_cast<uint16_t>(numDecls), varRegs.data()));

    for (Instr* curr : d_seq)
    {
      head->d_next = curr;
      head = curr;
    }
  }

  void setNext(Instr* instr, Instr* newNext)
  {
    if (d_isTmpTree)
    {
      instr->d_next = newNext;
    }
    else
    {
      d_ctManager.setNext(instr, newNext);
    }
  }

  /**
   * The nodes at the bottom of a code tree can have very many children, and
   * most of them will not be compatible. Cap how many trivial sequences are
   * traversed looking for one.
   */
  static constexpr size_t s_findBestChildThreshold = 64;
  /** A sequence this short with no branching counts as "too simple". */
  static constexpr size_t s_simpleSeqThreshold = 4;

  Choose* findBestChild(Choose* firstChild)
  {
    size_t numTooSimple = 0;
    Choose* bestChild = nullptr;
    uint32_t maxCompatibility = 0;
    Choose* currChild = firstChild;
    while (currChild != nullptr)
    {
      bool simple = false;
      uint32_t currCompatibility = getCompatibilityMeasure(currChild, simple);
      if (simple)
      {
        numTooSimple++;
        if (numTooSimple > s_findBestChildThreshold)
        {
          // it is unlikely that a compatible node will be found
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

  bool isCompatible(Bind* instr) const
  {
    TNode n = getRegister(instr->d_ireg);
    return !n.isNull()
           && isApp(n)
           // binding a ground term would be wasteful, and the rest of the
           // code assumes it does not happen
           && !isGroundPat(n) && getDecl(n) == instr->d_label
           && n.getNumChildren() == instr->d_numArgs;
  }

  bool isCompatible(Compare* instr) const
  {
    TNode r1 = getRegister(instr->d_reg1);
    return !r1.isNull() && r1 == getRegister(instr->d_reg2);
  }

  bool isCompatible(Check* instr) const
  {
    TNode r = getRegister(instr->d_reg);
    if (r.isNull() || !isApp(r) || !isGroundPat(r))
    {
      return false;
    }
    ENode* nPrime = mkPatENode(d_context, d_qm, d_qa, r);
    // Comparing the roots is safe, because the modifications to the code tree
    // are chronological.
    return instr->d_enode->getRoot() == nPrime->getRoot();
  }

  /**
   * The label hash of the pattern in register reg. A ground application is
   * viewed as a constant, so its enode's own label hash is used.
   */
  uint32_t getPatLblHash(uint32_t reg) const
  {
    TNode p = getRegister(reg);
    Assert(!p.isNull());
    Assert(isApp(p));
    if (isGroundPat(p))
    {
      ENode* e = mkPatENode(d_context, d_qm, d_qa, p);
      if (!e->hasLblHash())
      {
        e->setLblHash(d_context.getTrailStack());
      }
      return e->getLblHash();
    }
    return const_cast<Compiler*>(this)->d_lblHasher(getDecl(p));
  }

  /**
   * A check is semi compatible if it accesses a register that was not
   * processed yet, holding a ground term whose label hash matches. A CFILTER
   * is created in that case.
   */
  bool isSemiCompatible(Check* instr) const
  {
    uint32_t reg = instr->d_reg;
    // The enode may not have a label hash even though updateFilters ran
    // first: it can be a ground subterm of a maximal ground term, and only
    // the maximal ones get a hash there.
    if (!instr->d_enode->hasLblHash())
    {
      instr->d_enode->setLblHash(d_context.getTrailStack());
    }
    TNode r = getRegister(reg);
    return !r.isNull()
           // no point filtering a register another filter already checked
           && getCheckMark(reg) == NOT_CHECKED && isGroundPat(r)
           && getPatLblHash(reg) == instr->d_enode->getLblHash();
  }

  /** FILTER is for non-ground terms; CFILTER is the one for ground terms. */
  bool isCompatible(Filter* instr) const
  {
    uint32_t reg = instr->d_reg;
    TNode r = getRegister(reg);
    if (!r.isNull() && isApp(r) && !isGroundPat(r))
    {
      return instr->d_lblSet.mayContain(getPatLblHash(reg));
    }
    return false;
  }

  bool isCfilterCompatible(Filter* instr) const
  {
    uint32_t reg = instr->d_reg;
    TNode r = getRegister(reg);
    // only ground terms are considered in CFILTERs
    if (!r.isNull() && isGroundPat(r))
    {
      return instr->d_lblSet.mayContain(getPatLblHash(reg));
    }
    return false;
  }

  bool isSemiCompatible(Filter* instr) const
  {
    uint32_t reg = instr->d_reg;
    TNode r = getRegister(reg);
    return !r.isNull() && getCheckMark(reg) == NOT_CHECKED && isApp(r)
           && !isGroundPat(r);
  }

  /**
   * How many instructions in the branch starting at child are compatible with
   * the patterns in the registers of d_todo. Sets simple if the branch has no
   * branching and few instructions.
   */
  uint32_t getCompatibilityMeasure(Choose* child, bool& simple)
  {
    simple = true;
    d_toReset.clear();
    uint32_t weight = 0;
    size_t numInstr = 0;
    Instr* curr = child->d_next;
    while (curr != nullptr && curr->d_opcode != CHOOSE
           && curr->d_opcode != NOOP)
    {
      numInstr++;
      switch (curr->d_opcode)
      {
        case BIND:
          if (isCompatible(static_cast<Bind*>(curr)))
          {
            // a BIND weighs more than a COMPARE or a CHECK
            weight += 4;
            Bind* b = static_cast<Bind*>(curr);
            TNode n = getRegister(b->d_ireg);
            uint32_t oreg = b->d_oreg;
            uint16_t numArgs = b->d_numArgs;
            Assert(n.getNumChildren() == numArgs);
            for (uint16_t i = 0; i < numArgs; ++i)
            {
              setRegister(oreg + i, n[i]);
              d_toReset.push_back(oreg + i);
            }
          }
          break;
        case COMPARE:
          if (isCompatible(static_cast<Compare*>(curr)))
          {
            weight += 2;
          }
          break;
        case CHECK:
          if (isCompatible(static_cast<Check*>(curr)))
          {
            weight += 2;
          }
          else if (isSemiCompatible(static_cast<Check*>(curr)))
          {
            weight += 1;
          }
          break;
        case CFILTER:
          if (isCfilterCompatible(static_cast<Filter*>(curr)))
          {
            weight += 2;
          }
          break;
        case FILTER:
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
        || (curr != nullptr && curr->d_opcode == CHOOSE))
    {
      simple = false;
    }
    for (uint32_t r : d_toReset)
    {
      setRegister(r, TNode::null());
    }
    return weight;
  }

  void insert(Instr* head, size_t firstMpIdx)
  {
    for (;;)
    {
      d_compatible.clear();
      d_incompatible.clear();
      Instr* curr = head->d_next;
      Instr* last = head;
      while (curr != nullptr && curr->d_opcode != CHOOSE
             && curr->d_opcode != NOOP)
      {
        switch (curr->d_opcode)
        {
          case BIND:
          {
            Bind* bnd = static_cast<Bind*>(curr);
            if (isCompatible(bnd))
            {
              uint32_t ireg = bnd->d_ireg;
              Assert(todoContains(ireg));
              eraseTodo(ireg);
              setCheckMark(ireg, NOT_CHECKED);
              d_compatible.push_back(curr);
              TNode app = getRegister(ireg);
              uint32_t oreg = bnd->d_oreg;
              uint16_t numArgs = bnd->d_numArgs;
              for (uint16_t i = 0; i < numArgs; ++i)
              {
                setRegister(oreg + i, app[i]);
                d_todo.push_back(oreg + i);
              }
            }
            else
            {
              d_incompatible.push_back(curr);
            }
            break;
          }
          case CHECK:
          {
            Check* chk = static_cast<Check*>(curr);
            if (isCompatible(chk))
            {
              uint32_t reg = chk->d_reg;
              Assert(todoContains(reg));
              eraseTodo(reg);
              setCheckMark(reg, NOT_CHECKED);
              d_compatible.push_back(curr);
            }
            else if (isSemiCompatible(chk))
            {
              uint32_t reg = chk->d_reg;
              // isSemiCompatible gave the enode a label hash
              uint32_t h1 = chk->d_enode->getLblHash();
              uint32_t h2 = getPatLblHash(reg);
              ApproxSet s(h1);
              s.insert(h2);
              Filter* newInstr = d_ctManager.mkFilter(CFILTER, reg, s);
              setCheckMark(reg, CHECK_SET);
              d_compatible.push_back(newInstr);
              d_incompatible.push_back(curr);
            }
            else
            {
              d_incompatible.push_back(curr);
            }
            break;
          }
          case COMPARE:
            if (isCompatible(static_cast<Compare*>(curr)))
            {
              uint32_t reg1 = static_cast<Compare*>(curr)->d_reg1;
              uint32_t reg2 = static_cast<Compare*>(curr)->d_reg2;
              Assert(todoContains(reg2));
              eraseTodo(reg2);
              setCheckMark(reg2, NOT_CHECKED);
              if (isVar(getRegister(reg1)))
              {
                eraseTodo(reg1);
                setCheckMark(reg1, NOT_CHECKED);
                uint32_t varId = varIndex(getRegister(reg1));
                if (d_vars[varId] == -1)
                {
                  d_vars[varId] = static_cast<int32_t>(reg1);
                }
              }
              d_compatible.push_back(curr);
            }
            else
            {
              d_incompatible.push_back(curr);
            }
            break;
          case CFILTER:
            if (isCfilterCompatible(static_cast<Filter*>(curr)))
            {
              uint32_t reg = static_cast<Filter*>(curr)->d_reg;
              setCheckMark(reg, CHECK_SINGLETON);
              d_compatible.push_back(curr);
            }
            else
            {
              d_incompatible.push_back(curr);
            }
            break;
          case FILTER:
          {
            Filter* flt = static_cast<Filter*>(curr);
            if (isCompatible(flt))
            {
              uint32_t reg = flt->d_reg;
              if (flt->d_lblSet.size() == 1)
              {
                setCheckMark(reg, CHECK_SINGLETON);
              }
              else
              {
                setCheckMark(reg, CHECK_SET);
              }
              d_compatible.push_back(curr);
            }
            else if (isSemiCompatible(flt))
            {
              uint32_t reg = flt->d_reg;
              uint32_t h = getPatLblHash(reg);
              setCheckMark(reg, CHECK_SET);
              const ApproxSet& s = flt->d_lblSet;
              if (s.size() > 1)
              {
                d_ctManager.insertNewLblHash(flt, h);
                d_compatible.push_back(curr);
              }
              else
              {
                Assert(s.size() == 1);
                ApproxSet newS(s);
                newS.insert(h);
                Filter* newInstr = d_ctManager.mkFilter(FILTER, reg, newS);
                d_compatible.push_back(newInstr);
                d_incompatible.push_back(curr);
              }
            }
            else
            {
              d_incompatible.push_back(curr);
            }
            break;
          }
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
        Assert(curr->d_opcode == CHOOSE);
        Choose* firstChild = static_cast<Choose*>(curr);
        Choose* bestChild = findBestChild(firstChild);
        if (bestChild == nullptr)
        {
          // There is no compatible child. The sequence
          //   head -> c1 -> ... -> (cn == last) -> firstChild
          // becomes
          //   head -> c1 -> ... -> (cn == last) -> newChild
          //   newChild: CHOOSE(firstChild) -> linearise
          Choose* newChild = d_ctManager.mkChoose(firstChild);
          d_numChoices++;
          setNext(last, newChild);
          linearise(newChild, firstMpIdx);
          return;
        }
        head = bestChild;
        // continue from bestChild
      }
      else
      {
        Assert(head->isInit() || !d_compatible.empty());
        // Suppose the sequence is
        //   head -> c1 -> i1 -> c2 -> c3 -> i2 -> firstChildHead
        // where the c_j are compatible and the i_j are not. It becomes
        //   head -> c1 -> c2 -> c3 -> newChildHead1
        //   newChildHead1: CHOOSE(newChildHead2) -> i1 -> i2 -> firstChildHead
        //   newChildHead2: NOOP -> linearise()
        Instr* firstChildHead = curr;
        Choose* newChildHead2 = d_ctManager.mkNoop();
        Choose* newChildHead1 = d_ctManager.mkChoose(newChildHead2);
        d_numChoices++;
        curr = head;
        for (Instr* instr : d_compatible)
        {
          setNext(curr, instr);
          curr = instr;
        }
        setNext(curr, newChildHead1);
        curr = newChildHead1;
        for (Instr* inc : d_incompatible)
        {
          if (curr == newChildHead1)
          {
            // newChildHead1 is new, so no trail entry is needed
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
  }

  /** Note Z3's unsigned_vector::erase is a no-op when the element is absent */
  void eraseTodo(uint32_t reg)
  {
    auto it = std::find(d_todo.begin(), d_todo.end(), reg);
    if (it != d_todo.end())
    {
      d_todo.erase(it);
    }
  }

  bool todoContains(uint32_t reg) const
  {
    return std::find(d_todo.begin(), d_todo.end(), reg) != d_todo.end();
  }

  SmtContext& d_context;
  QuantifierManager& d_qm;
  CodeTreeManager& d_ctManager;
  LabelHasher& d_lblHasher;
  std::vector<Node> d_registers;
  /** the registers that still have patterns to process */
  std::vector<uint32_t> d_todo;
  std::vector<uint32_t> d_aux;
  /** -1 if the variable is unbound, otherwise the register holding it */
  std::vector<int32_t> d_vars;
  Node d_qa;
  Node d_mp;
  CodeTree* d_tree;
  uint32_t d_numChoices;
  bool d_isTmpTree;
  std::vector<bool> d_mpAlreadyProcessed;
  std::unordered_map<Node, uint32_t> d_matchedExprs;

  std::vector<CheckMark> d_mark;
  std::vector<uint32_t> d_toReset;
  std::vector<Instr*> d_compatible;
  std::vector<Instr*> d_incompatible;
  std::vector<Instr*> d_seq;
};

// -------------------------------------------------------------- interpreter

/** A pool of reusable enode vectors, standing in for Z3's pool<>. */
class ENodeVectorPool
{
 public:
  /** An empty vector, which stays owned by the pool. */
  ENodeVector* mk()
  {
    if (d_free.empty())
    {
      d_vectors.push_back(std::make_unique<ENodeVector>());
      return d_vectors.back().get();
    }
    ENodeVector* r = d_free.back();
    d_free.pop_back();
    r->clear();
    return r;
  }

  /** Make v, which mk returned, available to mk again. */
  void recycle(ENodeVector* v) { d_free.push_back(v); }

 private:
  std::vector<std::unique_ptr<ENodeVector>> d_vectors;
  std::vector<ENodeVector*> d_free;
};

/** The state a CONTINUE backtrack point has to remember. */
struct ContState
{
  ENodeVector* d_toRecycle;
  ENode* const* d_it;
  ENode* const* d_end;
};

struct BacktrackPoint
{
  const Instr* d_instr;
  uint32_t d_oldMaxGeneration;
  union
  {
    ENode* d_curr;
    ContState d_rest;
  };
};

class Interpreter
{
 public:
  Interpreter(SmtContext& ctx, QuantifierManager& qm)
      : d_context(ctx),
        d_egraph(ctx.getEGraph()),
        d_qm(qm),
        d_top(0),
        d_pc(nullptr),
        d_maxGeneration(0),
        d_currMaxGeneration(0),
        d_numArgs(0),
        d_oreg(0),
        d_n1(nullptr),
        d_n2(nullptr),
        d_app(nullptr),
        d_b(nullptr)
  {
    d_args.resize(s_initArgsSize, nullptr);
  }

  void init(CodeTree* t)
  {
    if (d_registers.size() < t->getNumRegs())
    {
      d_registers.resize(t->getNumRegs(), static_cast<ENode*>(nullptr));
    }
    if (d_bindings.size() < t->getNumRegs())
    {
      d_bindings.resize(t->getNumRegs(), static_cast<ENode*>(nullptr));
    }
    if (d_backtrackStack.size() < t->getNumChoices())
    {
      d_backtrackStack.resize(t->getNumChoices());
    }
  }

  bool execute(CodeTree* t)
  {
    d_context.getStats().d_numMamExecs++;
    init(t);
    // the candidates of a tree that filters them (one of the inverted path
    // index) may repeat, and are marked to be matched once
    bool filter = t->filterCandidates();
    bool ok = true;
    for (ENode* app : t->getCandidates())
    {
      if ((filter && app->isMarked()) || !app->isCgr())
      {
        continue;
      }
      if (d_context.resourceLimitsExceeded() || !executeCore(t, app))
      {
        ok = false;
        break;
      }
      if (filter)
      {
        app->setMark();
      }
    }
    if (filter)
    {
      cleanup(t);
    }
    return ok;
  }

  /** init(t) must be invoked before executeCore. */
  bool executeCore(CodeTree* t, ENode* n);

 private:
  static constexpr size_t s_initArgsSize = 16;

  void cleanup(CodeTree* t)
  {
    for (ENode* app : t->getCandidates())
    {
      if (app->isMarked())
      {
        app->unsetMark();
      }
    }
  }

  void updateMaxGeneration(ENode* n)
  {
    d_maxGeneration = std::max(d_maxGeneration, d_egraph.getGeneration(n));
  }

  /** Whether n is an application of lbl with numExpectedArgs arguments. */
  static bool isFApp(const ENode* n, TNode lbl, uint16_t numExpectedArgs)
  {
    return n->getDecl() == lbl && n->isCgr()
           && n->getNumArgs() == numExpectedArgs;
  }

  /**
   * The first application of lbl with the expected arity in n's equivalence
   * class. The arity has to be given explicitly because of the n-ary
   * operators, whose applications may have any number of arguments.
   */
  ENode* getFirstFApp(TNode lbl, uint16_t numExpectedArgs, ENode* curr)
  {
    if (isFApp(curr, lbl, numExpectedArgs))
    {
      updateMaxGeneration(curr);
      return curr;
    }
    return getNextFApp(lbl, numExpectedArgs, curr, curr);
  }

  ENode* getNextFApp(TNode lbl,
                     uint16_t numExpectedArgs,
                     ENode* first,
                     ENode* curr)
  {
    for (curr = curr->getNext(); curr != first; curr = curr->getNext())
    {
      if (isFApp(curr, lbl, numExpectedArgs))
      {
        updateMaxGeneration(curr);
        return curr;
      }
    }
    return nullptr;
  }

  /** Run an IS_CGR; false means backtrack. */
  bool execIsCgr(const IsCgr* pc)
  {
    uint16_t numArgs = pc->d_numArgs;
    ENode* n = d_registers[pc->d_ireg];
    TNode f = pc->d_label;
    ENode* first = n;
    const uint32_t* iregs = pc->iregsPtr();
    for (uint16_t i = 0; i < numArgs; ++i)
    {
      if (d_registers[iregs[i]] == nullptr)
      {
        return false;
      }
    }
    if (n == nullptr)
    {
      return false;
    }
    if (numArgs > d_args.size())
    {
      d_args.resize(numArgs + 1, nullptr);
    }
    for (uint16_t i = 0; i < numArgs; ++i)
    {
      d_args[i] = d_registers[iregs[i]]->getRoot();
    }
    do
    {
      if (n->getDecl() == f && n->getNumArgs() == numArgs)
      {
        uint16_t i = 0;
        for (; i < numArgs; ++i)
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

  /** The relevant f-parents of n in which n is the i-th argument. */
  ENodeVector* mkDepth1Vector(ENode* n, TNode f, uint16_t i)
  {
    ENodeVector* v = d_pool.mk();
    n = n->getRoot();
    for (ENode* p : n->getParents())
    {
      if (p->getDecl() == f && i < p->getNumArgs()
          && d_context.getPropCore().isRelevant(p->getExpr()) && p->isCgr()
          && p->getArg(i)->getRoot() == n)
      {
        v->push_back(p);
      }
    }
    return v;
  }

  /**
   * The relevant f-parents, in which the parent is the i-th argument, of each
   * g-parent of the register of j2 where that register is argument
   * j2->d_argPos.
   */
  ENodeVector* mkDepth2Vector(Joint2* j2, TNode f, uint16_t i)
  {
    ENode* n = d_registers[j2->d_reg]->getRoot();
    if (n->getNumParents() == 0)
    {
      return nullptr;
    }
    ENodeVector* v = d_pool.mk();
    for (ENode* p : n->getParents())
    {
      if (p->getDecl() == j2->d_decl
          && d_context.getPropCore().isRelevant(p->getExpr())
          && p->getNumArgs() > j2->d_argPos && p->isCgr()
          && p->getArg(j2->d_argPos)->getRoot() == n)
      {
        // p is in the joint
        ENode* pr = p->getRoot();
        for (ENode* p2 : pr->getParents())
        {
          if (p2->getDecl() == f
              && d_context.getPropCore().isRelevant(p2->getExpr())
              && p2->isCgr() && i < p2->getNumArgs()
              && p2->getArg(i)->getRoot() == pr)
          {
            v->push_back(p2);
          }
        }
      }
    }
    return v;
  }

  ENode* initContinue(const Cont* c, uint16_t expectedNumArgs);
  /**
   * Move st to the next relevant application with numArgs arguments, from
   * where it is. The applications may be the whole enode list of the label,
   * which is not necessarily relevant. Returns false at the end.
   */
  bool seekContApp(ContState& st, uint16_t numArgs) const
  {
    for (; st.d_it != st.d_end; ++st.d_it)
    {
      ENode* curr = *st.d_it;
      if (curr->getNumArgs() == numArgs
          && d_context.getPropCore().isRelevant(curr->getExpr()))
      {
        return true;
      }
    }
    return false;
  }

  /** Report a match to the quantifier manager. */
  void onMatch(TNode q,
               size_t numBindings,
               ENode* const* bindings,
               uint32_t maxGeneration)
  {
    d_context.getStats().d_numMamMatches++;
    d_qm.addInstance(q, numBindings, bindings, maxGeneration);
  }

  SmtContext& d_context;
  EGraph& d_egraph;
  QuantifierManager& d_qm;
  ENodeVector d_registers;
  ENodeVector d_bindings;
  ENodeVector d_args;
  std::vector<BacktrackPoint> d_backtrackStack;
  size_t d_top;
  const Instr* d_pc;

  // auxiliary temporaries
  /** the maximum generation of an application enode processed */
  uint32_t d_maxGeneration;
  uint32_t d_currMaxGeneration;
  uint16_t d_numArgs;
  uint32_t d_oreg;
  ENode* d_n1;
  ENode* d_n2;
  ENode* d_app;
  const Bind* d_b;

  ENodeVectorPool d_pool;
};

ENode* Interpreter::initContinue(const Cont* c, uint16_t expectedNumArgs)
{
  TNode lbl = c->d_label;
  size_t minSz = d_egraph.getNumENodesOf(lbl);
  uint16_t numArgs = c->d_numArgs;
  const TaggedPtr* joints = c->jointsPtr();
  // A quick filter: give up if any joint has no parents at all.
  for (uint16_t i = 0; i < numArgs; ++i)
  {
    TaggedPtr bare = joints[i];
    ENode* n = nullptr;
    switch (bare.getTag())
    {
      case NULL_TAG:
      case NESTED_VAR_TAG: continue;
      case GROUND_TERM_TAG: n = bare.untag<ENode>(); break;
      case VAR_TAG: n = d_registers[bare.unboxInt()]; break;
    }
    if (n == nullptr)
    {
      continue;
    }
    ENode* r = n->getRoot();
    if (r->getPlbls().emptyIntersection(c->d_lblSet))
    {
      return nullptr;
    }
    if (r->getNumParents() == 0)
    {
      return nullptr;
    }
  }
  // Walk the joints and keep the one that yields the fewest candidates.
  ENodeVector* bestV = nullptr;
  for (uint16_t i = 0; i < numArgs; ++i)
  {
    TaggedPtr bare = joints[i];
    ENodeVector* currV = nullptr;
    switch (bare.getTag())
    {
      case NULL_TAG: currV = nullptr; break;
      case GROUND_TERM_TAG:
        currV = mkDepth1Vector(bare.untag<ENode>(), lbl, i);
        break;
      case VAR_TAG:
        currV = mkDepth1Vector(d_registers[bare.unboxInt()], lbl, i);
        break;
      case NESTED_VAR_TAG:
        currV = mkDepth2Vector(bare.untag<Joint2>(), lbl, i);
        break;
    }
    if (currV != nullptr)
    {
      if (currV->size() < minSz
          && (bestV == nullptr || currV->size() < bestV->size()))
      {
        if (bestV != nullptr)
        {
          d_pool.recycle(bestV);
        }
        bestV = currV;
        if (bestV->empty())
        {
          d_pool.recycle(bestV);
          return nullptr;
        }
      }
      else
      {
        d_pool.recycle(currV);
      }
    }
  }
  BacktrackPoint& bp = d_backtrackStack[d_top];
  bp.d_instr = c;
  bp.d_oldMaxGeneration = d_maxGeneration;
  ContState& bpRest = bp.d_rest;
  if (bestV == nullptr)
  {
    const ENodeVector& all = d_egraph.enodesOf(lbl);
    bpRest.d_toRecycle = nullptr;
    bpRest.d_it = all.data();
    bpRest.d_end = all.data() + all.size();
  }
  else
  {
    Assert(!bestV->empty());
    bpRest.d_toRecycle = bestV;
    bpRest.d_it = bestV->data();
    bpRest.d_end = bestV->data() + bestV->size();
  }
  if (!seekContApp(bpRest, expectedNumArgs))
  {
    if (bestV != nullptr)
    {
      bpRest.d_toRecycle = nullptr;
      d_pool.recycle(bestV);
    }
    return nullptr;
  }
  d_top++;
  updateMaxGeneration(*(bpRest.d_it));
  return *(bpRest.d_it);
}

bool Interpreter::executeCore(CodeTree* t, ENode* n)
{
  size_t sinceLastCheck = 0;

  // It makes no sense to process an irrelevant enode.
  Assert(d_context.getPropCore().isRelevant(n->getExpr()));

  d_maxGeneration = d_egraph.getGeneration(n);

  d_pc = t->getRoot();
  d_registers[0] = n;
  d_top = 0;

main_loop:

  if (d_pc == nullptr)
  {
    goto backtrack;
  }

  switch (d_pc->d_opcode)
  {
    case INIT:
      // the root of the tree t, which holds the expected number of arguments
      d_app = d_registers[0];
      d_numArgs = static_cast<uint16_t>(d_app->getNumArgs());
      if (d_numArgs != t->expectedNumArgs())
      {
        goto backtrack;
      }
      for (uint16_t i = 0; i < d_numArgs; ++i)
      {
        d_registers[i + 1] = d_app->getArg(i);
      }
      d_pc = d_pc->d_next;
      goto main_loop;

    case COMPARE:
      d_n1 = d_registers[static_cast<const Compare*>(d_pc)->d_reg1];
      d_n2 = d_registers[static_cast<const Compare*>(d_pc)->d_reg2];
      if (d_n1 == nullptr || d_n2 == nullptr)
      {
        goto backtrack;
      }
      if (d_n1->getRoot() != d_n2->getRoot())
      {
        goto backtrack;
      }
      d_pc = d_pc->d_next;
      goto main_loop;

    case CHECK:
      d_n1 = d_registers[static_cast<const Check*>(d_pc)->d_reg];
      d_n2 = static_cast<const Check*>(d_pc)->d_enode;
      if (d_n1 == nullptr)
      {
        goto backtrack;
      }
      // A dynamically generated pattern may be a ground if-then-else, in
      // which case the equality check is skipped.
      if (d_n1->getRoot() != d_n2->getRoot()
          && d_n2->getExpr().getKind() != Kind::ITE)
      {
        goto backtrack;
      }
      d_pc = d_pc->d_next;
      goto main_loop;

      // CFILTER and FILTER are treated differently by the compiler: two
      // CFILTERs with different label sets are never merged. CFILTER
      // combines CHECKs, FILTER combines BINDs.
    case CFILTER:
    case FILTER:
      d_n1 = d_registers[static_cast<const Filter*>(d_pc)->d_reg]->getRoot();
      if (static_cast<const Filter*>(d_pc)->d_lblSet.emptyIntersection(
              d_n1->getLbls()))
      {
        goto backtrack;
      }
      d_pc = d_pc->d_next;
      goto main_loop;

    case CHOOSE:
      d_backtrackStack[d_top].d_instr = d_pc;
      d_backtrackStack[d_top].d_oldMaxGeneration = d_maxGeneration;
      d_top++;
      d_pc = d_pc->d_next;
      goto main_loop;

    case NOOP:
      Assert(static_cast<const Choose*>(d_pc)->d_alt == nullptr);
      d_pc = d_pc->d_next;
      goto main_loop;

    case BIND:
    {
      const Bind* bi = static_cast<const Bind*>(d_pc);
      d_n1 = d_registers[bi->d_ireg];
      Assert(d_n1 != nullptr);
      d_oreg = bi->d_oreg;
      d_currMaxGeneration = d_maxGeneration;
      d_app = getFirstFApp(bi->d_label, bi->d_numArgs, d_n1);
      if (d_app == nullptr)
      {
        goto backtrack;
      }
      d_backtrackStack[d_top].d_instr = d_pc;
      d_backtrackStack[d_top].d_oldMaxGeneration = d_currMaxGeneration;
      d_backtrackStack[d_top].d_curr = d_app;
      d_top++;
      for (uint16_t i = 0; i < bi->d_numArgs; ++i)
      {
        d_registers[d_oreg + i] = d_app->getArg(i);
      }
      d_pc = d_pc->d_next;
      goto main_loop;
    }

    case YIELD:
    {
      const Yield* y = static_cast<const Yield*>(d_pc);
      const uint32_t* bnds = y->bindingsPtr();
      d_numArgs = y->d_numBindings;
      // No reversal: the registers are indexed by de Bruijn level, which is
      // already declaration order. See the note at the top of this file.
      for (uint16_t i = 0; i < d_numArgs; ++i)
      {
        d_bindings[i] = d_registers[bnds[i]];
      }
      d_maxGeneration =
          std::max(d_maxGeneration,
                   d_egraph.getMaxGeneration(d_numArgs, d_bindings.data()));
      if (d_context.getCancelFlag())
      {
        return false;
      }
      onMatch(y->d_qa, d_numArgs, d_bindings.data(), d_maxGeneration);
      goto backtrack;
    }

    case GET_ENODE:
      d_registers[static_cast<const GetENodeInstr*>(d_pc)->d_oreg] =
          static_cast<const GetENodeInstr*>(d_pc)->d_enode;
      d_pc = d_pc->d_next;
      goto main_loop;

    case GET_CGR:
    {
      const GetCgr* c = static_cast<const GetCgr*>(d_pc);
      d_numArgs = c->d_numArgs;
      if (d_numArgs > d_args.size())
      {
        d_args.resize(d_numArgs, nullptr);
      }
      const uint32_t* iregs = c->iregsPtr();
      for (uint16_t i = 0; i < d_numArgs; ++i)
      {
        d_args[i] = d_registers[iregs[i]];
        if (c->d_lblSet.emptyIntersection(d_args[i]->getRoot()->getPlbls()))
        {
          goto backtrack;
        }
      }
      d_n1 = d_egraph.getENodeEqTo(
          c->d_label, c->d_commutative, d_numArgs, d_args.data());
      if (d_n1 == nullptr
          || !d_context.getPropCore().isRelevant(d_n1->getExpr()))
      {
        goto backtrack;
      }
      updateMaxGeneration(d_n1);
      d_registers[c->d_oreg] = d_n1;
      d_pc = d_pc->d_next;
      goto main_loop;
    }

    case IS_CGR:
      if (!execIsCgr(static_cast<const IsCgr*>(d_pc)))
      {
        goto backtrack;
      }
      d_pc = d_pc->d_next;
      goto main_loop;

    case CONTINUE:
    {
      const Cont* c = static_cast<const Cont*>(d_pc);
      d_numArgs = c->d_numArgs;
      d_oreg = c->d_oreg;
      d_app = initContinue(c, d_numArgs);
      if (d_app == nullptr)
      {
        goto backtrack;
      }
      for (uint16_t i = 0; i < d_numArgs; ++i)
      {
        d_registers[d_oreg + i] = d_app->getArg(i);
      }
      d_pc = d_pc->d_next;
      goto main_loop;
    }
  }

backtrack:
  if (d_top == 0)
  {
    return true;  // no more alternatives
  }
  {
    BacktrackPoint& bp = d_backtrackStack[d_top - 1];
    d_maxGeneration = bp.d_oldMaxGeneration;

    if (sinceLastCheck++ > 100)
    {
      sinceLastCheck = 0;
      if (d_context.resourceLimitsExceeded())
      {
        // A soft timeout: clean up before leaving.
        while (d_top != 0)
        {
          BacktrackPoint& bp2 = d_backtrackStack[d_top - 1];
          if (bp2.d_instr->d_opcode == CONTINUE
              && bp2.d_rest.d_toRecycle != nullptr)
          {
            d_pool.recycle(bp2.d_rest.d_toRecycle);
          }
          d_top--;
        }
        return false;
      }
    }

    switch (bp.d_instr->d_opcode)
    {
      case CHOOSE:
        d_pc = static_cast<const Choose*>(bp.d_instr)->d_alt;
        Assert(d_pc != nullptr);
        d_top--;
        goto main_loop;

      case BIND:
      {
        d_b = static_cast<const Bind*>(bp.d_instr);
        d_n1 = d_registers[d_b->d_ireg];
        d_app = getNextFApp(d_b->d_label, d_b->d_numArgs, d_n1, bp.d_curr);
        if (d_app == nullptr)
        {
          d_top--;
          goto backtrack;
        }
        bp.d_curr = d_app;
        d_oreg = d_b->d_oreg;
        for (uint16_t i = 0; i < d_b->d_numArgs; ++i)
        {
          d_registers[d_oreg + i] = d_app->getArg(i);
        }
        d_pc = d_b->d_next;
        goto main_loop;
      }

      case CONTINUE:
      {
        ContState& bpRest = bp.d_rest;
        const Cont* c = static_cast<const Cont*>(bp.d_instr);
        ++bpRest.d_it;
        if (seekContApp(bpRest, c->d_numArgs))
        {
          d_app = *bpRest.d_it;
          updateMaxGeneration(d_app);
          d_numArgs = c->d_numArgs;
          d_oreg = c->d_oreg;
          for (uint16_t i = 0; i < d_numArgs; ++i)
          {
            d_registers[d_oreg + i] = d_app->getArg(i);
          }
          d_pc = c->d_next;
          goto main_loop;
        }
        // the continue failed
        if (bpRest.d_toRecycle != nullptr)
        {
          d_pool.recycle(bpRest.d_toRecycle);
        }
        d_top--;
        goto backtrack;
      }

      default: Unreachable();
    }
  }
  return false;
}

// ----------------------------------------------------- func label -> tree

/**
 * A mapping from a function symbol to the code tree rooted at it.
 */
class CodeTreeMap
{
 public:
  CodeTreeMap(SmtContext& ctx, Compiler& c, TrailStack& s)
      : d_context(ctx),
        d_egraph(ctx.getEGraph()),
        d_compiler(c),
        d_trailStack(s)
  {
  }

  ~CodeTreeMap()
  {
    for (CodeTree* t : d_trees)
    {
      delete t;
    }
  }

  /**
   * Add a pattern to the code tree map, where mp is used as a pattern for q
   * and firstIdx is the index of the head of the multi-pattern mp.
   */
  void addPattern(TNode q, TNode mp, size_t firstIdx)
  {
    Assert(firstIdx < mp.getNumChildren());
    TNode p = mp[firstIdx];
    if (isGroundPat(p))
    {
      return;
    }
    uint32_t lblId = d_egraph.getDeclId(getDecl(p));
    if (d_trees.size() < lblId + 1)
    {
      d_trees.resize(lblId + 1, static_cast<CodeTree*>(nullptr));
    }
    if (d_trees[lblId] == nullptr)
    {
      d_trees[lblId] = d_compiler.mkTree(q, mp, firstIdx, false);
      d_context.getStats().d_numMamTrees++;
      Trace("z3-mam-order")
          << "mkTree for " << getDecl(p) << " lvl=" << d_context.getScopeLevel()
          << std::endl;
      Trace("z3-mam-tree") << "tree for " << getDecl(p) << std::endl;
      Assert(d_trees[lblId]->expectedNumArgs() == p.getNumChildren());
      d_trailStack.push(MkTreeTrail(d_trees, lblId));
    }
    else
    {
      Trace("z3-mam-newpat")
          << "  insert into existing tree for " << getDecl(p) << std::endl;
      d_compiler.insert(d_trees[lblId], q, mp, firstIdx, false);
    }
  }

  CodeTree* getCodeTreeFor(TNode lbl) const
  {
    uint32_t lblId = d_egraph.getDeclIdOption(lbl);
    return lblId < d_trees.size() ? d_trees[lblId] : nullptr;
  }

  const std::vector<CodeTree*>& getCodeTrees() const { return d_trees; }

 private:
  /** Delete the tree created for a label when its scope is popped. */
  class MkTreeTrail : public Trail
  {
   public:
    MkTreeTrail(std::vector<CodeTree*>& t, uint32_t id)
        : d_trees(t), d_lblId(id)
    {
    }

    void undo() override
    {
      delete d_trees[d_lblId];
      d_trees[d_lblId] = nullptr;
    }

   private:
    std::vector<CodeTree*>& d_trees;
    uint32_t d_lblId;
  };

  SmtContext& d_context;
  EGraph& d_egraph;
  Compiler& d_compiler;
  /** mapping: label id -> tree */
  std::vector<CodeTree*> d_trees;
  TrailStack& d_trailStack;
};

// ------------------------------------- path trees AKA inverted path index

/**
 * A temporary object encoding a path of the form
 *
 *   f.1 -> g.2 -> h.0
 *
 * used to update the inverted path index. For the path above, given an enode
 * n, follow the parents p_0 of n that are f-applications and in which n is
 * the second argument; then for each such p_0 follow the parents p_1 of p_0
 * that are g-applications and in which p_0 is the third argument; finally
 * follow the p_2 parents of p_1 that are h-applications and in which p_1 is
 * the first argument.
 *
 * To improve the filtering power of the index a ground argument is stored as
 * well when there is one, giving paths of the form
 *
 *   f.1:t.2 -> g.2 -> h.0:s.1
 *
 * The extra pairs t.2 and s.1 are an extra filter on the parents: only the
 * f-parents whose third argument is equal to t are of interest.
 */
struct Path
{
  Path(TNode lbl,
       uint16_t argIdx,
       uint16_t groundArgIdx,
       ENode* groundArg,
       size_t patIdx,
       Path* child)
      : d_label(lbl),
        d_argIdx(argIdx),
        d_groundArgIdx(groundArgIdx),
        d_groundArg(groundArg),
        d_patternIdx(patIdx),
        d_child(child)
  {
    Assert(groundArg != nullptr || groundArgIdx == 0);
  }

  TNode d_label;
  uint16_t d_argIdx;
  uint16_t d_groundArgIdx;
  ENode* d_groundArg;
  size_t d_patternIdx;
  Path* d_child;
};

bool isEqual(const Path* p1, const Path* p2)
{
  for (;;)
  {
    if (p1->d_label != p2->d_label || p1->d_argIdx != p2->d_argIdx
        || p1->d_patternIdx != p2->d_patternIdx
        || (p1->d_child == nullptr) != (p2->d_child == nullptr))
    {
      return false;
    }
    if (p1->d_child == nullptr && p2->d_child == nullptr)
    {
      return true;
    }
    p1 = p1->d_child;
    p2 = p2->d_child;
  }
}

using Paths = std::vector<Path*>;

/** The inverted path index. See the comment on Path. */
struct PathTree
{
  PathTree(Path* p, LabelHasher& h)
      : d_label(p->d_label),
        d_argIdx(p->d_argIdx),
        d_groundArgIdx(p->d_groundArgIdx),
        d_groundArg(p->d_groundArg),
        d_code(nullptr),
        d_filter(h(p->d_label)),
        d_sibling(nullptr),
        d_firstChild(nullptr),
        d_todo(nullptr)
  {
  }

  TNode d_label;
  uint16_t d_argIdx;
  uint16_t d_groundArgIdx;
  ENode* d_groundArg;
  CodeTree* d_code;
  ApproxSet d_filter;
  PathTree* d_sibling;
  PathTree* d_firstChild;
  /** temporary field used to collect candidates */
  ENodeVector* d_todo;
};

using PathTreePair = std::pair<PathTree*, PathTree*>;

/**
 * True if applications of this symbol may have a number of arguments other
 * than the symbol's arity, which in cvc5 is the case for the n-ary kinds
 * (+, *, and, ...). Z3 calls this func_decl::is_flat_associative.
 */
bool isFlatAssociative(ENode* n)
{
  // as the congruence keys, this is read from the declaration, which a
  // temporary enode has too
  TNode decl = n->getDecl();
  return decl.getKind() == Kind::BUILTIN
         && NodeManager::isNAryKind(NodeManager::operatorToKind(decl));
}

}  // namespace

// ----------------------------------------- matching abstract machine impl

class MamImpl
{
 public:
  MamImpl(SmtContext& ctx, QuantifierManager& qm)
      : d_context(ctx),
        d_egraph(ctx.getEGraph()),
        d_qm(qm),
        d_trailStack(ctx.getTrailStack()),
        d_lblHasher(ctx.getEGraph()),
        d_ctManager(d_lblHasher, d_trailStack),
        d_compiler(ctx, qm, d_ctManager, d_lblHasher),
        d_interpreter(ctx, qm),
        d_trees(ctx, d_compiler, d_trailStack),
        d_isPlbl(d_trailStack.getContext()),
        d_isClbl(d_trailStack.getContext()),
        d_r1(nullptr),
        d_r2(nullptr)
  {
    resetPpPc();
  }

  void addPattern(TNode q, TNode mp)
  {
    Assert(mp.getKind() == Kind::INST_PATTERN);
    // Ground patterns are discarded before solving, but the preprocessor may
    // have turned a non-ground pattern into a ground one, so it is checked
    // again here.
    bool allGround = true;
    for (const Node& arg : mp)
    {
      if (!isGroundPat(arg))
      {
        allGround = false;
        break;
      }
    }
    if (allGround)
    {
      // ignore a multi-pattern containing only ground patterns
      return;
    }
    for (const Node& arg : mp)
    {
      if (expr::hasClosure(arg))
      {
        // patterns with quantifiers are not handled
        return;
      }
    }
    updateFilters(q, mp);
    collectGroundExprs(q, mp);
    d_newPatterns.push_back(std::pair<Node, Node>(q, mp));
    // The matching abstract machine implements incremental E-matching, so for
    // a multi-pattern [p_1, ..., p_n] there are n insertions; in the i-th one
    // the pattern p_i is assumed to be the first.
    for (size_t i = 0, n = mp.getNumChildren(); i < n; ++i)
    {
      d_trees.addPattern(q, mp, i);
    }
  }

  void notifyPop()
  {
    if (!d_toMatch.empty())
    {
      Trace("z3-mam-order") << "notifyPop discards candidates of "
                            << d_toMatch.size() << " trees" << std::endl;
      for (CodeTree* t : d_toMatch)
      {
        t->resetCandidates();
      }
      d_toMatch.clear();
    }
    d_newPatterns.clear();
  }

  void match()
  {
    for (CodeTree* t : d_toMatch)
    {
      Trace("z3-mam-order")
          << "match tree " << t->getRootLbl() << " with "
          << t->getCandidates().size() << " candidates" << std::endl;
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

  void rematch()
  {
    for (CodeTree* t : d_trees.getCodeTrees())
    {
      if (t == nullptr)
      {
        continue;
      }
      executeOnRelevant(t, t->getRootLbl());
    }
  }

  /** Run the tree t over every relevant application of lbl. */
  void executeOnRelevant(CodeTree* t, TNode lbl)
  {
    d_interpreter.init(t);
    // executeCore may internalize new applications of lbl, which can grow
    // and reallocate the context's enode vector for lbl, so the vector
    // itself (not just its size) is re-fetched on every iteration.
    for (size_t i = 0; i < d_egraph.enodesOf(lbl).size(); ++i)
    {
      ENode* curr = d_egraph.enodesOf(lbl)[i];
      if (d_context.getPropCore().isRelevant(curr->getExpr()))
      {
        d_interpreter.executeCore(t, curr);
      }
    }
  }

  /**
   * Invoked when n becomes relevant. If lazy is true then n is not added to
   * the list of candidate enodes for matching, and the method only updates
   * the labels.
   */
  void notifyRelevant(ENode* n, bool lazy)
  {
    if (!lazy)
    {
      d_context.getStats().d_numMamNotifyRelevant++;
      if (n->getNumArgs() > 0)
      {
        d_context.getStats().d_numMamRelevantApp++;
      }
    }
    if (n->hasLblHash())
    {
      updateLbls(n, n->getLblHash());
    }
    if (n->getNumArgs() > 0)
    {
      TNode lbl = n->getDecl();
      uint8_t h = d_lblHasher(lbl);
      if (isClbl(lbl))
      {
        updateLbls(n, h);
      }
      if (isPlbl(lbl))
      {
        updateChildrenPlbls(n, h);
      }
      if (!lazy)
      {
        addCandidate(n);
      }
    }
  }

  bool hasWork() const { return !d_toMatch.empty() || !d_newPatterns.empty(); }

  void notifyMerge(ENode* r1, ENode* r2)
  {
    d_context.getStats().d_numMamAddEq++;
    ENode* oldR1 = d_r1;
    ENode* oldR2 = d_r2;
    d_r1 = r1;
    d_r2 = r2;

    processPc(r1, r2);
    processPc(r2, r1);
    processPp(r1, r2);

    ApproxSet r1Plbls = r1->getPlbls();
    ApproxSet& r2Plbls = r2->getPlbls();
    ApproxSet r1Lbls = r1->getLbls();
    ApproxSet& r2Lbls = r2->getLbls();

    d_trailStack.push(ValueTrail<ApproxSet>(r2Lbls));
    d_trailStack.push(ValueTrail<ApproxSet>(r2Plbls));
    r2Lbls |= r1Lbls;
    r2Plbls |= r1Plbls;

    d_r1 = oldR1;
    d_r2 = oldR2;
  }

 private:
  void addCandidate(CodeTree* t, ENode* app)
  {
    if (t != nullptr)
    {
      if (!t->hasCandidates())
      {
        d_toMatch.push_back(t);
      }
      t->addCandidate(app);
      d_context.getStats().d_numMamCandidates++;
      if (d_inCollectParents)
      {
        d_context.getStats().d_numMamEqCandidates++;
      }
      t->compressCandidates();
    }
  }

  void addCandidate(ENode* app)
  {
    CodeTree* t = d_trees.getCodeTreeFor(app->getDecl());
    Trace("z3-mam-order") << "addCandidate " << app->getExpr()
                          << " tree=" << (t != nullptr)
                          << " lvl=" << d_context.getScopeLevel() << std::endl;
    addCandidate(t, app);
  }

  bool isPlbl(TNode lbl) const
  {
    uint32_t lblId = d_egraph.getDeclIdOption(lbl);
    return d_isPlbl.contains(lblId);
  }

  bool isClbl(TNode lbl) const
  {
    uint32_t lblId = d_egraph.getDeclIdOption(lbl);
    return d_isClbl.contains(lblId);
  }

  void updateLbls(ENode* n, uint32_t elem)
  {
    ApproxSet& rLbls = n->getRoot()->getLbls();
    if (!rLbls.mayContain(elem))
    {
      d_trailStack.push(ValueTrail<ApproxSet>(rLbls));
      rLbls.insert(elem);
    }
  }

  void updateClbls(TNode lbl)
  {
    uint32_t lblId = d_egraph.getDeclId(lbl);
    if (!d_isClbl.insert(lblId))
    {
      return;
    }
    uint8_t h = d_lblHasher(lbl);
    for (ENode* app : d_egraph.enodesOf(lbl))
    {
      if (d_context.getPropCore().isRelevant(app->getExpr()))
      {
        updateLbls(app, h);
      }
    }
  }

  void updateChildrenPlbls(ENode* app, uint8_t elem)
  {
    uint32_t numArgs = app->getNumArgs();
    for (uint32_t i = 0; i < numArgs; ++i)
    {
      ENode* c = app->getArg(i);
      ApproxSet& rPlbls = c->getRoot()->getPlbls();
      if (!rPlbls.mayContain(elem))
      {
        d_trailStack.push(ValueTrail<ApproxSet>(rPlbls));
        rPlbls.insert(elem);
      }
    }
  }

  void updatePlbls(TNode lbl)
  {
    uint32_t lblId = d_egraph.getDeclId(lbl);
    if (!d_isPlbl.insert(lblId))
    {
      return;
    }
    uint8_t h = d_lblHasher(lbl);
    for (ENode* app : d_egraph.enodesOf(lbl))
    {
      if (d_context.getPropCore().isRelevant(app->getExpr()))
      {
        updateChildrenPlbls(app, h);
      }
    }
  }

  void resetPpPc()
  {
    for (uint32_t i = 0; i < approxSetCapacity(); ++i)
    {
      for (uint32_t j = 0; j < approxSetCapacity(); ++j)
      {
        d_pp[i][j].first = nullptr;
        d_pp[i][j].second = nullptr;
        d_pc[i][j] = nullptr;
      }
    }
  }

  CodeTree* mkCode(TNode q, TNode mp, size_t patIdx)
  {
    return d_compiler.mkTree(q, mp, patIdx, true);
  }

  void insertCode(PathTree* t, TNode q, TNode mp, size_t patIdx)
  {
    d_compiler.insert(t->d_code, q, mp, patIdx, false);
  }

  PathTree* mkPathTree(Path* p, TNode q, TNode mp)
  {
    Assert(p != nullptr);
    size_t patIdx = p->d_patternIdx;
    PathTree* head = nullptr;
    PathTree* curr = nullptr;
    PathTree* prev = nullptr;
    while (p != nullptr)
    {
      curr = new (d_trailStack) PathTree(p, d_lblHasher);
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
    curr->d_code = mkCode(q, mp, patIdx);
    d_trailStack.push(NewObjTrail<CodeTree>(curr->d_code));
    return head;
  }

  void insert(PathTree* t, Path* p, TNode q, TNode mp)
  {
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
          // found a compatible node
          if (t->d_firstChild == nullptr)
          {
            if (p->d_child == nullptr)
            {
              Assert(t->d_code != nullptr);
              insertCode(t, q, mp, p->d_patternIdx);
            }
            else
            {
              d_trailStack.push(SetPtrTrail<PathTree>(t->d_firstChild));
              t->d_firstChild = mkPathTree(p->d_child, q, mp);
            }
          }
          else
          {
            if (p->d_child == nullptr)
            {
              if (t->d_code != nullptr)
              {
                insertCode(t, q, mp, p->d_patternIdx);
              }
              else
              {
                d_trailStack.push(SetPtrTrail<CodeTree>(t->d_code));
                t->d_code = mkCode(q, mp, p->d_patternIdx);
                d_trailStack.push(NewObjTrail<CodeTree>(t->d_code));
              }
            }
            else
            {
              insert(t->d_firstChild, p->d_child, q, mp);
            }
          }
          return;
        }
      }
      prevSibling = t;
      t = t->d_sibling;
    }
    d_trailStack.push(SetPtrTrail<PathTree>(prevSibling->d_sibling));
    prevSibling->d_sibling = mkPathTree(p, q, mp);
    if (!foundLabel)
    {
      d_trailStack.push(ValueTrail<ApproxSet>(head->d_filter));
      head->d_filter.insert(d_lblHasher(p->d_label));
    }
  }

  void updatePc(uint8_t h1, uint8_t h2, Path* p, TNode q, TNode mp)
  {
    if (d_pc[h1][h2] != nullptr)
    {
      insert(d_pc[h1][h2], p, q, mp);
    }
    else
    {
      d_trailStack.push(SetPtrTrail<PathTree>(d_pc[h1][h2]));
      d_pc[h1][h2] = mkPathTree(p, q, mp);
    }
  }

  void updatePp(uint8_t h1, uint8_t h2, Path* p1, Path* p2, TNode q, TNode mp)
  {
    if (h1 == h2)
    {
      Assert(d_pp[h1][h2].second == nullptr);
      if (d_pp[h1][h2].first != nullptr)
      {
        insert(d_pp[h1][h2].first, p1, q, mp);
        if (!isEqual(p1, p2))
        {
          insert(d_pp[h1][h2].first, p2, q, mp);
        }
      }
      else
      {
        d_trailStack.push(SetPtrTrail<PathTree>(d_pp[h1][h2].first));
        d_pp[h1][h2].first = mkPathTree(p1, q, mp);
        insert(d_pp[h1][h2].first, p2, q, mp);
      }
    }
    else
    {
      if (h1 > h2)
      {
        std::swap(h1, h2);
        std::swap(p1, p2);
      }
      if (d_pp[h1][h2].first != nullptr)
      {
        Assert(d_pp[h1][h2].second != nullptr);
        insert(d_pp[h1][h2].first, p1, q, mp);
        insert(d_pp[h1][h2].second, p2, q, mp);
      }
      else
      {
        Assert(d_pp[h1][h2].second == nullptr);
        d_trailStack.push(SetPtrTrail<PathTree>(d_pp[h1][h2].first));
        d_trailStack.push(SetPtrTrail<PathTree>(d_pp[h1][h2].second));
        d_pp[h1][h2].first = mkPathTree(p1, q, mp);
        d_pp[h1][h2].second = mkPathTree(p2, q, mp);
      }
    }
  }

  void updateVars(uint32_t varId, Path* p, TNode q, TNode mp)
  {
    Paths& varPaths = d_varPaths[varId];
    bool found = false;
    for (Path* currPath : varPaths)
    {
      if (isEqual(p, currPath))
      {
        found = true;
      }
      TNode lbl1 = currPath->d_label;
      TNode lbl2 = p->d_label;
      updatePlbls(lbl1);
      updatePlbls(lbl2);
      updatePp(d_lblHasher(lbl1), d_lblHasher(lbl2), currPath, p, q, mp);
    }
    if (!found)
    {
      varPaths.push_back(p);
    }
  }

  ENode* getGroundArg(TNode pat, TNode q, uint32_t& pos)
  {
    pos = 0;
    for (size_t i = 0, n = pat.getNumChildren(); i < n; ++i)
    {
      if (isGroundPat(pat[i]))
      {
        pos = static_cast<uint32_t>(i);
        return mkPatENode(d_context, d_qm, q, pat[i]);
      }
    }
    return nullptr;
  }

  /**
   * Update the inverted path index with respect to the pattern pat in the
   * context of the path p, where pat is a subterm of mp[patIdx] and mp is a
   * multi-pattern of q. If p is null then mp[patIdx] == pat.
   */
  void updateFilters(TNode pat, Path* p, TNode q, TNode mp, size_t patIdx)
  {
    uint16_t numArgs = static_cast<uint16_t>(pat.getNumChildren());
    uint32_t groundArgPos = 0;
    ENode* groundArg = getGroundArg(pat, q, groundArgPos);
    TNode plbl = getDecl(pat);
    for (uint16_t i = 0; i < numArgs; ++i)
    {
      TNode child = pat[i];
      Path* newPath = &d_tmpPaths.emplace_back(
          plbl, i, static_cast<uint16_t>(groundArgPos), groundArg, patIdx, p);

      if (isVar(child))
      {
        updateVars(varIndex(child), newPath, q, mp);
        continue;
      }

      if (isGroundPat(child))
      {
        ENode* n = mkPatENode(d_context, d_qm, q, child);
        updatePlbls(plbl);
        if (!n->hasLblHash())
        {
          n->setLblHash(d_context.getTrailStack());
        }
        updatePc(d_lblHasher(plbl), n->getLblHash(), newPath, q, mp);
        continue;
      }

      TNode clbl = getDecl(child);
      updatePlbls(plbl);
      updateClbls(clbl);
      updatePc(d_lblHasher(plbl), d_lblHasher(clbl), newPath, q, mp);
      updateFilters(child, newPath, q, mp, patIdx);
    }
  }

  /** Update the inverted path index. */
  void updateFilters(TNode q, TNode mp)
  {
    size_t numVars = q[0].getNumChildren();
    if (numVars >= d_varPaths.size())
    {
      d_varPaths.resize(numVars + 1);
    }
    for (Paths& p : d_varPaths)
    {
      p.clear();
    }
    d_tmpPaths.clear();
    // Given a multi-pattern (p_1, ..., p_n) the filters have to be updated
    // using the patterns
    //   (p_1, p_2, ..., p_n)
    //   (p_2, p_1, ..., p_n)
    //   ...
    //   (p_n, p_2, ..., p_1)
    for (size_t i = 0, n = mp.getNumChildren(); i < n; ++i)
    {
      updateFilters(mp[i], nullptr, q, mp, i);
    }
  }

  /** Check equality modulo the equality d_r1 = d_r2. */
  bool isEq(ENode* n1, ENode* n2) const
  {
    return n1->getRoot() == n2->getRoot()
           || (n1->getRoot() == d_r1 && n2->getRoot() == d_r2)
           || (n2->getRoot() == d_r1 && n1->getRoot() == d_r2);
  }

  /** Collect new E-matching candidates using the inverted path index t. */
  void collectParents(ENode* r, PathTree* t)
  {
    if (t == nullptr)
    {
      return;
    }
    d_todo.clear();
    d_inCollectParents = true;
    ENodeVector* toUnmark = d_pool.mk();
    ENodeVector* toUnmark2 = d_pool.mk();
    t->d_todo = d_pool.mk();
    t->d_todo->push_back(r);
    d_todo.push_back(t);
    size_t head = 0;
    while (head < d_todo.size())
    {
      PathTree* currT = d_todo[head];
      ENodeVector* v = currT->d_todo;
      ApproxSet& filter = currT->d_filter;
      head++;

      for (ENode* n : *v)
      {
        // Two different kinds of mark are used:
        // - the enode mark field: marks the already processed parents;
        // - the enode mark2 field: marks the roots already added to be
        //   processed at the next level.
        // Using the mark field for both is incorrect and makes the matcher
        // miss potential new matches.
        ENode* currChild = n->getRoot();

        if (currChild->getPlbls().emptyIntersection(filter))
        {
          continue;
        }

        for (ENode* currParent : currChild->getParents())
        {
          // An equality is never in the inverted path index.
          if (currParent->isEq())
          {
            continue;
          }
          TNode lbl = currParent->getDecl();
          bool isFlatAssoc = isFlatAssociative(currParent);
          ENode* currParentRoot = currParent->getRoot();
          ENode* currParentCg = currParent->getCg();
          if (filter.mayContain(d_lblHasher(lbl)) && !currParent->isMarked()
              && (currParentCg == currParent
                  || !isEq(currParentCg, currParentRoot))
              && d_context.getPropCore().isRelevant(currParent->getExpr()))
          {
            PathTree* currTree = currT;
            while (currTree != nullptr)
            {
              // Since cvc5 represents the associative operators (e.g. + and
              // *) with n-ary applications, the invariant that every
              // application of f has f's arity does not hold for them, hence
              // the extra checks.
              if (currTree->d_label == lbl
                  && (!isFlatAssoc
                      || (currTree->d_argIdx < currParent->getNumArgs()
                          && currTree->d_groundArgIdx
                                 < currParent->getNumArgs())))
              {
                ENode* currParentChild =
                    currParent->getArg(currTree->d_argIdx)->getRoot();
                if (  // Filter 1: currChild is equal to the child of the
                      // current parent.
                    currChild == currParentChild
                    // Filter 2:
                    && (  // currTree has no filter based on a ground
                          // argument, or
                        currTree->d_groundArg == nullptr
                        // the child of the parent is equal to the expected
                        // ground argument.
                        || isEq(currTree->d_groundArg,
                                currParent->getArg(currTree->d_groundArgIdx))))
                {
                  if (currTree->d_code != nullptr)
                  {
                    addCandidate(currTree->d_code, currParent);
                  }
                  if (currTree->d_firstChild != nullptr)
                  {
                    PathTree* child = currTree->d_firstChild;
                    if (child->d_todo == nullptr)
                    {
                      child->d_todo = d_pool.mk();
                      d_todo.push_back(child);
                    }
                    if (!currParentRoot->isMarked2())
                    {
                      child->d_todo->push_back(currParentRoot);
                    }
                  }
                }
              }
              currTree = currTree->d_sibling;
            }
            currParent->setMark();
            toUnmark->push_back(currParent);
            if (!currParentRoot->isMarked2())
            {
              currParentRoot->setMark2();
              toUnmark2->push_back(currParentRoot);
            }
          }
        }
      }
      d_pool.recycle(currT->d_todo);
      currT->d_todo = nullptr;
      // remove both marks
      unmarkENodes(toUnmark->size(), toUnmark->data());
      unmarkENodes2(toUnmark2->size(), toUnmark2->data());
      toUnmark->clear();
      toUnmark2->clear();
    }
    d_pool.recycle(toUnmark);
    d_pool.recycle(toUnmark2);
    d_inCollectParents = false;
  }

  void processPp(ENode* r1, ENode* r2)
  {
    ApproxSet& plbls1 = r1->getPlbls();
    ApproxSet& plbls2 = r2->getPlbls();
    if (plbls1.empty() || plbls2.empty())
    {
      return;
    }
    for (uint32_t plbl1 : plbls1)
    {
      if (d_context.getCancelFlag())
      {
        break;
      }
      for (uint32_t plbl2 : plbls2)
      {
        uint32_t nPlbl1 = plbl1;
        uint32_t nPlbl2 = plbl2;
        ENode* nR1 = r1;
        ENode* nR2 = r2;
        if (nPlbl1 > nPlbl2)
        {
          std::swap(nPlbl1, nPlbl2);
          std::swap(nR1, nR2);
        }
        // Collect from the root with fewer parents. The second path tree is
        // for the larger label, which is the same as the first when the two
        // labels are equal.
        PathTreePair& pp = d_pp[nPlbl1][nPlbl2];
        Assert(nPlbl1 < nPlbl2 || pp.second == nullptr);
        if (nR1->getNumParents() <= nR2->getNumParents())
        {
          collectParents(nR1, pp.first);
        }
        else
        {
          collectParents(nR2, nPlbl1 == nPlbl2 ? pp.first : pp.second);
        }
      }
    }
  }

  void processPc(ENode* r1, ENode* r2)
  {
    ApproxSet& plbls = r1->getPlbls();
    ApproxSet& clbls = r2->getLbls();
    if (plbls.empty() || clbls.empty())
    {
      return;
    }
    for (uint32_t plbl1 : plbls)
    {
      if (d_context.getCancelFlag())
      {
        break;
      }
      for (uint32_t lbl2 : clbls)
      {
        collectParents(r1, d_pc[plbl1][lbl2]);
      }
    }
  }

  void matchNewPatterns()
  {
    Trace("z3-mam-newpat") << "matchNewPatterns: " << d_newPatterns.size()
                           << " new patterns" << std::endl;
    // a temporary tree per label, in the order they are made
    std::vector<std::pair<TNode, CodeTree*>> tmpTrees;
    std::unordered_map<uint32_t, CodeTree*> lblToTree;
    for (const std::pair<Node, Node>& kv : d_newPatterns)
    {
      if (d_context.getCancelFlag())
      {
        break;
      }
      TNode q = kv.first;
      TNode mp = kv.second;
      TNode p = mp[0];
      TNode lbl = getDecl(p);
      if (d_egraph.getNumENodesOf(lbl) > 0)
      {
        uint32_t lblId = d_egraph.getDeclId(lbl);
        std::unordered_map<uint32_t, CodeTree*>::iterator it =
            lblToTree.find(lblId);
        if (it == lblToTree.end())
        {
          CodeTree* tmpTree = d_compiler.mkTree(q, mp, 0, false);
          lblToTree[lblId] = tmpTree;
          tmpTrees.emplace_back(lbl, tmpTree);
        }
        else
        {
          d_compiler.insert(it->second, q, mp, 0, true);
        }
      }
    }

    for (const std::pair<TNode, CodeTree*>& lt : tmpTrees)
    {
      Trace("z3-mam-newpat")
          << "  running tree for " << lt.first << " over "
          << d_egraph.enodesOf(lt.first).size() << " enodes" << std::endl;
      executeOnRelevant(lt.second, lt.first);
      delete lt.second;
    }
  }

  void collectGroundExprs(TNode q, TNode mp)
  {
    std::vector<Node> todo;
    for (size_t i = 0, n = mp.getNumChildren(); i < n; ++i)
    {
      TNode pat = mp[i];
      if (isGroundPat(pat))
      {
        ENode* e = mkPatENode(d_context, d_qm, q, pat);
        d_context.getPropCore().markAsRelevant(e->getExpr());
      }
      else
      {
        todo.push_back(pat);
      }
    }
    while (!todo.empty())
    {
      Node n = todo.back();
      todo.pop_back();
      if (isGroundPat(n))
      {
        mkPatENode(d_context, d_qm, q, n);
      }
      else
      {
        for (const Node& arg : n)
        {
          if (!isVar(arg))
          {
            todo.push_back(arg);
          }
        }
      }
    }
  }

  SmtContext& d_context;
  EGraph& d_egraph;
  /** The quantifier manager, which receives the matches. */
  QuantifierManager& d_qm;
  /** The trail of the context, and the memory of the code trees. */
  TrailStack& d_trailStack;
  LabelHasher d_lblHasher;
  CodeTreeManager d_ctManager;
  Compiler d_compiler;
  Interpreter d_interpreter;
  CodeTreeMap d_trees;

  std::vector<CodeTree*> d_toMatch;
  /** recently added patterns */
  std::vector<std::pair<Node, Node>> d_newPatterns;

  /**
   * If d_isPlbl contains f then when f(c_1, ..., c_n) becomes relevant,
   * lblHash(f) is inserted into c_i->getRoot()->getPlbls() for each c_i.
   */
  context::CDHashSet<uint32_t> d_isPlbl;
  /**
   * If d_isClbl contains f then when n = f(c_1, ..., c_n) becomes relevant,
   * lblHash(f) is inserted into n->getRoot()->getLbls().
   */
  context::CDHashSet<uint32_t> d_isClbl;

  /** The paths of updateFilters, which are dropped at each call. */
  std::deque<Path> d_tmpPaths;
  PathTreePair d_pp[approxSetCapacity()][approxSetCapacity()];
  PathTree* d_pc[approxSetCapacity()][approxSetCapacity()];
  ENodeVectorPool d_pool;

  /** temporary field used to update the path trees */
  std::vector<Paths> d_varPaths;
  /** temporary field used to collect candidates */
  std::vector<PathTree*> d_todo;

  ENode* d_r1;
  ENode* d_r2;
  /** true while collectParents is running, for the statistics */
  bool d_inCollectParents = false;
};

Mam::Mam(SmtContext& ctx, QuantifierManager& qm)
    : d_impl(std::make_unique<MamImpl>(ctx, qm))
{
}

Mam::~Mam() {}

void Mam::addPattern(TNode q, TNode mp) { d_impl->addPattern(q, mp); }

void Mam::notifyPop() { d_impl->notifyPop(); }

void Mam::match() { d_impl->match(); }

void Mam::rematch() { d_impl->rematch(); }

bool Mam::hasWork() const { return d_impl->hasWork(); }

void Mam::notifyRelevant(ENode* n, bool lazy)
{
  d_impl->notifyRelevant(n, lazy);
}

void Mam::notifyMerge(ENode* r1, ENode* r2) { d_impl->notifyMerge(r1, r2); }

}  // namespace z3
}  // namespace cvc5::internal

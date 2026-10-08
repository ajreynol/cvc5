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
 * z3/ast.h), so YIELD here does not reverse. In both cases `bindings[i]` ends
 * up being the binding of the i-th declared variable.
 */

#include "z3/mam.h"

#include <algorithm>
#include <cstring>
#include <ostream>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "base/output.h"
#include "expr/node_algorithm.h"
#include "expr/node_manager.h"
#include "z3/ast.h"
#include "z3/enode.h"
#include "z3/quantifier_manager.h"
#include "z3/smt_context.h"
#include "z3/util/approx_set.h"
#include "z3/util/hash.h"
#include "z3/util/tagged_ptr.h"
#include "z3/util/trail.h"
#include "z3/util/uint_set.h"
#include "z3/util/util.h"

namespace cvc5::internal {
namespace z3 {

namespace {

/** Z3 uses IS_CGR in place of BIND when every argument is already bound. */
constexpr bool s_isCgrSupport = true;

/** True if the pattern subterm n contains no quantified variable. */
bool isGroundPat(TNode n) { return !expr::hasBoundVar(n); }

/** Internalize a ground pattern subterm and return its enode. */
ENode* mkPatENode(SmtContext& ctx, TNode qa, TNode n)
{
  ctx.internalize(n, false, ctx.getGeneration(qa));
  ENode* e = ctx.getENode(n);
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
  LabelHasher(SmtContext& ctx) : d_ctx(ctx) {}

  uint8_t operator()(TNode lbl)
  {
    uint32_t lblId = d_ctx.getDeclId(lbl);
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

  void print(std::ostream& out) const
  {
    out << "lbl-hasher:\n";
    bool first = true;
    for (size_t i = 0; i < d_lbl2Hash.size(); ++i)
    {
      if (d_lbl2Hash[i] != -1)
      {
        if (first)
        {
          first = false;
        }
        else
        {
          out << ", ";
        }
        out << i << " -> " << static_cast<int>(d_lbl2Hash[i]);
      }
    }
    out << "\n";
  }

 private:
  void mkLblHash(uint32_t lblId)
  {
    uint32_t a = 17;
    uint32_t b = 3;
    uint32_t c = lblId;
    hashMix(a, b, c);
    d_lbl2Hash[lblId] =
        static_cast<int8_t>(c & (approxSetCapacity() - 1));
  }

  SmtContext& d_ctx;
  /** Cache: declaration id to hash. */
  std::vector<int8_t> d_lbl2Hash;
};

// ------------------------------------------------------------- instructions

enum Opcode
{
  INIT1 = 0,
  INIT2,
  INIT3,
  INIT4,
  INIT5,
  INIT6,
  INITN,
  BIND1,
  BIND2,
  BIND3,
  BIND4,
  BIND5,
  BIND6,
  BINDN,
  YIELD1,
  YIELD2,
  YIELD3,
  YIELD4,
  YIELD5,
  YIELD6,
  YIELDN,
  COMPARE,
  CHECK,
  FILTER,
  CFILTER,
  PFILTER,
  CHOOSE,
  NOOP,
  CONTINUE,
  GET_ENODE,
  GET_CGR1,
  GET_CGR2,
  GET_CGR3,
  GET_CGR4,
  GET_CGR5,
  GET_CGR6,
  GET_CGRN,
  IS_CGR
};

struct Instr
{
  Opcode d_opcode;
  Instr* d_next = nullptr;
  bool isInit() const { return d_opcode >= INIT1 && d_opcode <= INITN; }
};

/**
 * INITN carries the argument count explicitly, because n-ary operators such
 * as + and * may be applied to any number of arguments. INIT1 to INIT6 do not
 * need it.
 */
struct InitN : public Instr
{
  uint32_t d_numArgs;
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
    return reinterpret_cast<const uint32_t*>(
        reinterpret_cast<const char*>(this) + sizeof(GetCgr));
  }
};

struct Yield : public Instr
{
  TNode d_qa;
  TNode d_pat;
  uint16_t d_numBindings;
  uint32_t* bindingsPtr()
  {
    return reinterpret_cast<uint32_t*>(reinterpret_cast<char*>(this)
                                       + sizeof(Yield));
  }
  const uint32_t* bindingsPtr() const
  {
    return reinterpret_cast<const uint32_t*>(
        reinterpret_cast<const char*>(this) + sizeof(Yield));
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
    return reinterpret_cast<const uint32_t*>(
        reinterpret_cast<const char*>(this) + sizeof(IsCgr));
  }
};

void printNumArgs(std::ostream& out, size_t numArgs)
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

std::ostream& operator<<(std::ostream& out, const Instr& instr)
{
  switch (instr.d_opcode)
  {
    case INIT1:
    case INIT2:
    case INIT3:
    case INIT4:
    case INIT5:
    case INIT6:
    case INITN:
      out << "(INIT";
      if (instr.d_opcode <= INIT6)
      {
        out << (instr.d_opcode - INIT1 + 1);
      }
      else
      {
        out << "N";
      }
      out << ")";
      break;
    case BIND1:
    case BIND2:
    case BIND3:
    case BIND4:
    case BIND5:
    case BIND6:
    case BINDN:
    {
      const Bind& b = static_cast<const Bind&>(instr);
      out << "(BIND";
      printNumArgs(out, b.d_numArgs);
      out << " " << b.d_label << " " << b.d_ireg << " " << b.d_oreg << ")";
      break;
    }
    case GET_CGR1:
    case GET_CGR2:
    case GET_CGR3:
    case GET_CGR4:
    case GET_CGR5:
    case GET_CGR6:
    case GET_CGRN:
    {
      const GetCgr& c = static_cast<const GetCgr&>(instr);
      out << "(GET_CGR";
      printNumArgs(out, c.d_numArgs);
      out << " " << c.d_label << " " << c.d_oreg;
      for (uint16_t i = 0; i < c.d_numArgs; ++i)
      {
        out << " " << c.iregsPtr()[i];
      }
      out << ")";
      break;
    }
    case IS_CGR:
    {
      const IsCgr& c = static_cast<const IsCgr&>(instr);
      out << "(IS_CGR " << c.d_label << " " << c.d_ireg;
      for (uint16_t i = 0; i < c.d_numArgs; ++i)
      {
        out << " " << c.iregsPtr()[i];
      }
      out << ")";
      break;
    }
    case YIELD1:
    case YIELD2:
    case YIELD3:
    case YIELD4:
    case YIELD5:
    case YIELD6:
    case YIELDN:
    {
      const Yield& y = static_cast<const Yield&>(instr);
      out << "(YIELD";
      printNumArgs(out, y.d_numBindings);
      out << " #" << y.d_qa.getId();
      for (uint16_t i = 0; i < y.d_numBindings; ++i)
      {
        out << " " << y.bindingsPtr()[i];
      }
      out << ")";
      break;
    }
    case CONTINUE:
    {
      const Cont& c = static_cast<const Cont&>(instr);
      out << "(CONTINUE " << c.d_label << " " << c.d_numArgs << " "
          << c.d_oreg << " " << c.d_lblSet << " (";
      for (uint16_t i = 0; i < c.d_numArgs; ++i)
      {
        if (i > 0)
        {
          out << " ";
        }
        TaggedPtr bare = c.jointsPtr()[i];
        switch (bare.getTag())
        {
          case NULL_TAG: out << "nil"; break;
          case GROUND_TERM_TAG:
            out << "#" << bare.untag<ENode>()->getOwnerId();
            break;
          case VAR_TAG: out << bare.unboxInt(); break;
          case NESTED_VAR_TAG:
          {
            Joint2* j = bare.untag<Joint2>();
            out << "(" << j->d_decl << " " << j->d_argPos << " " << j->d_reg
                << ")";
            break;
          }
        }
      }
      out << "))";
      break;
    }
    case COMPARE:
      out << "(COMPARE " << static_cast<const Compare&>(instr).d_reg1 << " "
          << static_cast<const Compare&>(instr).d_reg2 << ")";
      break;
    case CHECK:
      out << "(CHECK " << static_cast<const Check&>(instr).d_reg << " #"
          << static_cast<const Check&>(instr).d_enode->getOwnerId() << ")";
      break;
    case FILTER:
    case CFILTER:
    case PFILTER:
    {
      const Filter& f = static_cast<const Filter&>(instr);
      const char* op = instr.d_opcode == FILTER
                           ? "FILTER"
                           : (instr.d_opcode == CFILTER ? "CFILTER"
                                                        : "PFILTER");
      out << "(" << op << " " << f.d_reg << " " << f.d_lblSet << ")";
      break;
    }
    case GET_ENODE:
      out << "(GET_ENODE "
          << static_cast<const GetENodeInstr&>(instr).d_oreg << " #"
          << static_cast<const GetENodeInstr&>(instr).d_enode->getOwnerId()
          << ")";
      break;
    case CHOOSE: out << "(CHOOSE)"; break;
    case NOOP: out << "(NOOP)"; break;
  }
  return out;
}

// --------------------------------------------------------------- code tree

class Compiler;
class CodeTreeManager;

class CodeTree
{
 public:
  CodeTree(LabelHasher& h,
           TNode lbl,
           uint16_t numArgs,
           bool filterCandidates)
      : d_lblHasher(h),
        d_rootLbl(lbl),
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
    UIntSet seen;
    size_t j = 0;
    for (ENode* n : d_candidates)
    {
      size_t id = n->getExprId();
      if (!seen.contains(id))
      {
        d_candidates[j++] = n;
      }
      seen.insert(id);
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

  void print(std::ostream& out) const
  {
    out << "function: " << d_rootLbl << "\n";
    out << "num. regs:    " << d_numRegs << "\n"
        << "num. choices: " << d_numChoices << "\n";
    printSeq(out, d_root, 0);
  }

 private:
  friend class Compiler;
  friend class CodeTreeManager;

  void printSeq(std::ostream& out, Instr* head, size_t indent) const
  {
    for (size_t i = 0; i < indent; ++i)
    {
      out << "    ";
    }
    Instr* curr = head;
    out << *curr;
    curr = curr->d_next;
    while (curr != nullptr && curr->d_opcode != CHOOSE
           && curr->d_opcode != NOOP)
    {
      out << "\n" << *curr;
      curr = curr->d_next;
    }
    out << "\n";
    if (curr != nullptr)
    {
      printChildren(out, static_cast<Choose*>(curr), indent + 1);
    }
  }

  void printChildren(std::ostream& out,
                     Choose* firstChild,
                     size_t indent) const
  {
    Choose* curr = firstChild;
    while (curr != nullptr)
    {
      printSeq(out, curr, indent);
      curr = curr->d_alt;
    }
  }

  LabelHasher& d_lblHasher;
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
      : d_lblHasher(h), d_trailStack(s), d_region(s.getRegion())
  {
  }

  CodeTree* mkCodeTree(TNode lbl, uint16_t numArgs, bool filterCandidates)
  {
    CodeTree* r = new CodeTree(d_lblHasher, lbl, numArgs, filterCandidates);
    r->d_root = mkInit(numArgs);
    return r;
  }

  Joint2* mkJoint2(TNode f, uint32_t pos, uint32_t reg)
  {
    Joint2* r = static_cast<Joint2*>(d_region.allocate(sizeof(Joint2)));
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

  Filter* mkFilterCore(Opcode op, uint32_t reg, ApproxSet s)
  {
    Filter* r = mkInstr<Filter>(op, sizeof(Filter));
    r->d_reg = reg;
    r->d_lblSet = s;
    return r;
  }

  Filter* mkFilter(uint32_t reg, ApproxSet s)
  {
    return mkFilterCore(FILTER, reg, s);
  }

  Filter* mkPfilter(uint32_t reg, ApproxSet s)
  {
    return mkFilterCore(PFILTER, reg, s);
  }

  Filter* mkCfilter(uint32_t reg, ApproxSet s)
  {
    return mkFilterCore(CFILTER, reg, s);
  }

  GetENodeInstr* mkGetENode(uint32_t reg, ENode* n)
  {
    GetENodeInstr* s =
        mkInstr<GetENodeInstr>(GET_ENODE, sizeof(GetENodeInstr));
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
    Opcode op =
        numArgs <= 6 ? static_cast<Opcode>(BIND1 + numArgs - 1) : BINDN;
    Bind* r = mkInstr<Bind>(op, sizeof(Bind));
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
    Opcode op = numArgs <= 6 ? static_cast<Opcode>(GET_CGR1 + numArgs - 1)
                             : GET_CGRN;
    GetCgr* r = mkInstr<GetCgr>(
        op, sizeof(GetCgr) + numArgs * sizeof(uint32_t));
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
                 TNode pat,
                 uint16_t numBindings,
                 const uint32_t* bindings)
  {
    Assert(numBindings >= 1);
    Opcode op = numBindings <= 6
                    ? static_cast<Opcode>(YIELD1 + numBindings - 1)
                    : YIELDN;
    Yield* y = mkInstr<Yield>(
        op, sizeof(Yield) + numBindings * sizeof(uint32_t));
    y->d_qa = qa;
    y->d_pat = pat;
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
    Cont* r = mkInstr<Cont>(CONTINUE,
                            sizeof(Cont) + numArgs * sizeof(TaggedPtr));
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
    void* mem = d_region.allocate(size);
    OP* r = new (mem) OP;
    r->d_opcode = op;
    r->d_next = nullptr;
    return r;
  }

  Instr* mkInit(uint32_t n)
  {
    Assert(n >= 1);
    Opcode op = n <= 6 ? static_cast<Opcode>(INIT1 + n - 1) : INITN;
    if (op == INITN)
    {
      InitN* r = mkInstr<InitN>(op, sizeof(InitN));
      r->d_numArgs = n;
      return r;
    }
    return mkInstr<Instr>(op, sizeof(Instr));
  }

  LabelHasher& d_lblHasher;
  TrailStack& d_trailStack;
  Region& d_region;
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
           CodeTreeManager& ctMg,
           LabelHasher& h,
           bool useFilters = true)
      : d_context(ctx),
        d_ctManager(ctMg),
        d_lblHasher(h),
        d_useFilters(useFilters),
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
    CodeTree* r =
        d_ctManager.mkCodeTree(getDecl(p), numArgs, filterCandidates);
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
    setx(d_registers, static_cast<size_t>(reg), Node(p), Node::null());
  }

  TNode getRegister(uint32_t reg) const
  {
    return reg < d_registers.size() ? TNode(d_registers[reg])
                                    : TNode::null();
  }

  CheckMark getCheckMark(uint32_t reg) const
  {
    return reg < d_mark.size() ? d_mark[reg] : NOT_CHECKED;
  }

  void setCheckMark(uint32_t reg, CheckMark cm)
  {
    setx(d_mark, static_cast<size_t>(reg), cm, NOT_CHECKED);
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
    size_t numDecls = getNumDecls(qa);
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
          d_seq.push_back(d_ctManager.mkCompare(
              static_cast<uint32_t>(d_vars[varId]), reg));
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
        ENode* e = mkPatENode(d_context, d_qa, p);
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

      if (d_useFilters && getCheckMark(reg) != CHECK_SINGLETON)
      {
        ApproxSet s(d_lblHasher(getDecl(p)));
        d_seq.push_back(d_ctManager.mkFilter(reg, s));
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
              || (sz == firstAppSz
                  && numUnboundVars < firstAppNumUnboundVars))
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
      if (s_isCgrSupport && allArgsAreBoundVars(firstApp))
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
        d_seq.push_back(
            d_ctManager.mkBind(lbl, numArgs, firstAppReg, oreg));
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
      ENode* e = mkPatENode(d_context, d_qa, n);
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
  void lineariseMultiPattern(size_t /*firstIdx*/)
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
      if (d_useFilters)
      {
        s.insert(d_lblHasher(lbl));
      }

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
            ENode* e = mkPatENode(d_context, d_qa, curr);
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
            Joint2* newJoint = d_ctManager.mkJoint2(
                getDecl(curr),
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
      lineariseMultiPattern(firstIdx);
    }

    // the pattern must capture every variable
    size_t numDecls = getNumDecls(d_qa);
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
        d_qa, d_mp, static_cast<uint16_t>(numDecls), varRegs.data()));

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
      uint32_t currCompatibility =
          getCompatibilityMeasure(currChild, simple);
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
    return !n.isNull() && isApp(n)
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
    ENode* nPrime = mkPatENode(d_context, d_qa, r);
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
      ENode* e = mkPatENode(d_context, d_qa, p);
      if (!e->hasLblHash())
      {
        e->setLblHash(d_context);
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
    if (instr->d_enode != nullptr && !instr->d_enode->hasLblHash())
    {
      instr->d_enode->setLblHash(d_context);
    }
    TNode r = getRegister(reg);
    return !r.isNull()
           // no point filtering a register another filter already checked
           && getCheckMark(reg) == NOT_CHECKED && isGroundPat(r)
           && instr->d_enode != nullptr
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

  bool isCompatible(Cont* instr) const
  {
    uint32_t oreg = instr->d_oreg;
    for (uint16_t i = 0; i < instr->d_numArgs; ++i)
    {
      if (!getRegister(oreg + i).isNull())
      {
        return false;
      }
    }
    return true;
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
        case BIND1:
        case BIND2:
        case BIND3:
        case BIND4:
        case BIND5:
        case BIND6:
        case BINDN:
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
          else if (d_useFilters
                   && isSemiCompatible(static_cast<Check*>(curr)))
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
          case BIND1:
          case BIND2:
          case BIND3:
          case BIND4:
          case BIND5:
          case BIND6:
          case BINDN:
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
            else if (d_useFilters && isSemiCompatible(chk))
            {
              uint32_t reg = chk->d_reg;
              ENode* n1 = chk->d_enode;
              // n1 may not have a label hash even though updateFilters ran
              // first: n1 can be a ground subterm of a maximal ground term,
              // and only the maximal ones get a hash there.
              if (!n1->hasLblHash())
              {
                n1->setLblHash(d_context);
              }
              uint32_t h1 = n1->getLblHash();
              uint32_t h2 = getPatLblHash(reg);
              ApproxSet s(h1);
              s.insert(h2);
              Filter* newInstr = d_ctManager.mkCfilter(reg, s);
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
            Assert(d_useFilters);
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
            Assert(d_useFilters);
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
                Filter* newInstr = d_ctManager.mkFilter(reg, newS);
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
  CodeTreeManager& d_ctManager;
  LabelHasher& d_lblHasher;
  bool d_useFilters;
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
  ~ENodeVectorPool()
  {
    for (ENodeVector* v : d_free)
    {
      delete v;
    }
  }

  ENodeVector* mk()
  {
    if (d_free.empty())
    {
      return new ENodeVector();
    }
    ENodeVector* r = d_free.back();
    d_free.pop_back();
    r->clear();
    return r;
  }

  void recycle(ENodeVector* v) { d_free.push_back(v); }

 private:
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
  Interpreter(SmtContext& ctx, Mam& ma, bool useFilters)
      : d_context(ctx),
        d_mam(ma),
        d_useFilters(useFilters),
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
    reservex(d_registers, t->getNumRegs(), static_cast<ENode*>(nullptr));
    reservex(d_bindings, t->getNumRegs(), static_cast<ENode*>(nullptr));
    if (d_backtrackStack.size() < t->getNumChoices())
    {
      d_backtrackStack.resize(t->getNumChoices());
    }
  }

  bool execute(CodeTree* t)
  {
    d_context.getStats().d_numMamExecs++;
    init(t);
    if (t->filterCandidates())
    {
      for (ENode* app : t->getCandidates())
      {
        if (!app->isMarked() && app->isCgr())
        {
          if (d_context.resourceLimitsExceeded() || !executeCore(t, app))
          {
            cleanup(t);
            return false;
          }
          app->setMark();
        }
      }
      cleanup(t);
    }
    else
    {
      for (ENode* app : t->getCandidates())
      {
        if (app->isCgr())
        {
          if (d_context.resourceLimitsExceeded() || !executeCore(t, app))
          {
            return false;
          }
        }
      }
    }
    return true;
  }

  /** init(t) must be invoked before executeCore. */
  bool executeCore(CodeTree* t, ENode* n);

  /** The min and max generation of the enodes in d_patternInstances. */
  void getMinMaxTopGeneration(uint32_t& min, uint32_t& max)
  {
    Assert(!d_patternInstances.empty());
    if (d_minTopGeneration.empty())
    {
      min = max = d_context.getGeneration(d_patternInstances[0]);
      d_minTopGeneration.push_back(min);
      d_maxTopGeneration.push_back(max);
    }
    else
    {
      min = d_minTopGeneration.back();
      max = d_maxTopGeneration.back();
    }
    for (size_t i = d_minTopGeneration.size();
         i < d_patternInstances.size();
         ++i)
    {
      uint32_t curr = d_context.getGeneration(d_patternInstances[i]);
      min = std::min(min, curr);
      d_minTopGeneration.push_back(min);
      max = std::max(max, curr);
      d_maxTopGeneration.push_back(max);
    }
  }

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

  ENodeVector* mkENodeVector()
  {
    ENodeVector* r = d_pool.mk();
    r->clear();
    return r;
  }

  void recycleENodeVector(ENodeVector* v) { d_pool.recycle(v); }

  void updateMaxGeneration(ENode* n)
  {
    d_maxGeneration =
        std::max(d_maxGeneration, d_context.getGeneration(n));
  }

  /**
   * The first application of lbl with the expected arity in n's equivalence
   * class. The arity has to be given explicitly because of the n-ary
   * operators, whose applications may have any number of arguments.
   */
  ENode* getFirstFApp(TNode lbl, uint16_t numExpectedArgs, ENode* curr)
  {
    ENode* first = curr;
    do
    {
      if (curr->getDecl() == lbl && curr->isCgr()
          && curr->getNumArgs() == numExpectedArgs)
      {
        updateMaxGeneration(curr);
        return curr;
      }
      curr = curr->getNext();
    } while (curr != first);
    return nullptr;
  }

  ENode* getNextFApp(TNode lbl,
                     uint16_t numExpectedArgs,
                     ENode* first,
                     ENode* curr)
  {
    curr = curr->getNext();
    while (curr != first)
    {
      if (curr->getDecl() == lbl && curr->isCgr()
          && curr->getNumArgs() == numExpectedArgs)
      {
        updateMaxGeneration(curr);
        return curr;
      }
      curr = curr->getNext();
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
    ENodeVector* v = mkENodeVector();
    n = n->getRoot();
    for (ENode* p : n->getConstParents())
    {
      if (p->getDecl() == f && i < p->getNumArgs()
          && d_context.isRelevant(p) && p->isCgr()
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
    ENodeVector* v = mkENodeVector();
    for (ENode* p : n->getConstParents())
    {
      if (p->getDecl() == j2->d_decl && d_context.isRelevant(p)
          && p->getNumArgs() > j2->d_argPos && p->isCgr()
          && p->getArg(j2->d_argPos)->getRoot() == n)
      {
        // p is in the joint
        ENode* pr = p->getRoot();
        for (ENode* p2 : pr->getConstParents())
        {
          if (p2->getDecl() == f && d_context.isRelevant(p2) && p2->isCgr()
              && i < p2->getNumArgs() && p2->getArg(i)->getRoot() == pr)
          {
            v->push_back(p2);
          }
        }
      }
    }
    return v;
  }

  ENode* initContinue(const Cont* c, uint16_t expectedNumArgs);

  SmtContext& d_context;
  Mam& d_mam;
  bool d_useFilters;
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

  /**
   * Z3 records here the equalities a match relied on, for its proof log. This
   * port does not produce that log, so the vector is always empty; it is kept
   * because onMatch passes it on.
   */
  std::vector<std::pair<ENode*, ENode*>> d_usedENodes;
  /** used to compute the min and max top generation */
  ENodeVector d_patternInstances;
  std::vector<uint32_t> d_minTopGeneration;
  std::vector<uint32_t> d_maxTopGeneration;

  ENodeVectorPool d_pool;
};

ENode* Interpreter::initContinue(const Cont* c, uint16_t expectedNumArgs)
{
  TNode lbl = c->d_label;
  size_t minSz = d_context.getNumENodesOf(lbl);
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
    if (d_useFilters && r->getPlbls().emptyIntersection(c->d_lblSet))
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
          recycleENodeVector(bestV);
        }
        bestV = currV;
        if (bestV->empty())
        {
          recycleENodeVector(bestV);
          return nullptr;
        }
      }
      else
      {
        recycleENodeVector(currV);
      }
    }
  }
  BacktrackPoint& bp = d_backtrackStack[d_top];
  bp.d_instr = c;
  bp.d_oldMaxGeneration = d_maxGeneration;
  ContState& bpRest = bp.d_rest;
  if (bestV == nullptr)
  {
    const ENodeVector& all = d_context.enodesOf(lbl);
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
  // find an application with the right number of arguments
  for (; bpRest.d_it != bpRest.d_end; ++bpRest.d_it)
  {
    ENode* curr = *bpRest.d_it;
    if (curr->getNumArgs() == expectedNumArgs && d_context.isRelevant(curr))
    {
      break;
    }
  }
  if (bpRest.d_it == bpRest.d_end)
  {
    if (bestV != nullptr)
    {
      bpRest.d_toRecycle = nullptr;
      recycleENodeVector(bestV);
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
  Assert(d_context.isRelevant(n));
  d_patternInstances.clear();
  d_minTopGeneration.clear();
  d_maxTopGeneration.clear();
  d_patternInstances.push_back(n);

  d_maxGeneration = d_context.getGeneration(n);

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
    case INIT1:
    case INIT2:
    case INIT3:
    case INIT4:
    case INIT5:
    case INIT6:
    {
      d_app = d_registers[0];
      uint16_t expected =
          static_cast<uint16_t>(d_pc->d_opcode - INIT1 + 1);
      if (d_app->getNumArgs() != expected)
      {
        goto backtrack;
      }
      for (uint16_t i = 0; i < expected; ++i)
      {
        d_registers[i + 1] = d_app->getArg(i);
      }
      d_pc = d_pc->d_next;
      goto main_loop;
    }

    case INITN:
      d_app = d_registers[0];
      d_numArgs = static_cast<uint16_t>(d_app->getNumArgs());
      if (d_numArgs != static_cast<const InitN*>(d_pc)->d_numArgs)
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
      if (d_n1 == nullptr || d_n2 == nullptr)
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

    case PFILTER:
      d_n1 = d_registers[static_cast<const Filter*>(d_pc)->d_reg]->getRoot();
      if (static_cast<const Filter*>(d_pc)->d_lblSet.emptyIntersection(
              d_n1->getPlbls()))
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

    case BIND1:
    case BIND2:
    case BIND3:
    case BIND4:
    case BIND5:
    case BIND6:
    case BINDN:
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

    case YIELD1:
    case YIELD2:
    case YIELD3:
    case YIELD4:
    case YIELD5:
    case YIELD6:
    case YIELDN:
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
      d_maxGeneration = std::max(
          d_maxGeneration,
          d_context.getMaxGeneration(d_numArgs, d_bindings.data()));
      if (d_context.getCancelFlag())
      {
        return false;
      }
      d_mam.onMatch(y->d_qa,
                    y->d_pat,
                    d_numArgs,
                    d_bindings.data(),
                    d_maxGeneration,
                    d_usedENodes);
      goto backtrack;
    }

    case GET_ENODE:
      d_registers[static_cast<const GetENodeInstr*>(d_pc)->d_oreg] =
          static_cast<const GetENodeInstr*>(d_pc)->d_enode;
      d_pc = d_pc->d_next;
      goto main_loop;

    case GET_CGR1:
    case GET_CGR2:
    case GET_CGR3:
    case GET_CGR4:
    case GET_CGR5:
    case GET_CGR6:
    case GET_CGRN:
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
        if (d_useFilters
            && c->d_lblSet.emptyIntersection(
                d_args[i]->getRoot()->getPlbls()))
        {
          goto backtrack;
        }
      }
      d_n1 = d_context.getENodeEqTo(
          c->d_label, c->d_commutative, d_numArgs, d_args.data());
      if (d_n1 == nullptr || !d_context.isRelevant(d_n1))
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
      d_patternInstances.push_back(d_app);
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
            recycleENodeVector(bp2.d_rest.d_toRecycle);
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

      case BIND1:
      case BIND2:
      case BIND3:
      case BIND4:
      case BIND5:
      case BIND6:
      case BINDN:
      {
        d_b = static_cast<const Bind*>(bp.d_instr);
        d_n1 = d_registers[d_b->d_ireg];
        d_app =
            getNextFApp(d_b->d_label, d_b->d_numArgs, d_n1, bp.d_curr);
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
        ++bpRest.d_it;
        for (; bpRest.d_it != bpRest.d_end; ++bpRest.d_it)
        {
          d_app = *bpRest.d_it;
          const Cont* c = static_cast<const Cont*>(bp.d_instr);
          // The iterator may walk the whole enode list of the label, which
          // is not necessarily relevant, so relevance has to be checked.
          if (d_app->getNumArgs() == c->d_numArgs
              && d_context.isRelevant(d_app))
          {
            // update the pattern instance
            Assert(!d_patternInstances.empty());
            if (d_patternInstances.size() == d_maxTopGeneration.size())
            {
              d_maxTopGeneration.pop_back();
              d_minTopGeneration.pop_back();
            }
            d_patternInstances.pop_back();
            d_patternInstances.push_back(d_app);
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
        }
        // the continue failed
        if (bpRest.d_toRecycle != nullptr)
        {
          recycleENodeVector(bpRest.d_toRecycle);
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
      : d_context(ctx), d_compiler(c), d_trailStack(s)
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
    uint32_t lblId = d_context.getDeclId(getDecl(p));
    reservex(d_trees, lblId + 1, static_cast<CodeTree*>(nullptr));
    if (d_trees[lblId] == nullptr)
    {
      d_trees[lblId] = d_compiler.mkTree(q, mp, firstIdx, false);
      Assert(d_trees[lblId]->expectedNumArgs() == p.getNumChildren());
      d_trailStack.push(MkTreeTrail(d_trees, lblId));
    }
    else
    {
      CodeTree* tree = d_trees[lblId];
      // The number of arguments has to be checked because of the n-ary + and
      // * operators: the E-matching engine was built when every application
      // of a symbol had the symbol's arity. A pattern with an unexpected
      // number of arguments is ignored, which is not ideal but avoids a
      // crash.
      if (tree->expectedNumArgs() == p.getNumChildren())
      {
        d_compiler.insert(tree, q, mp, firstIdx, false);
      }
    }
  }

  void reset()
  {
    for (CodeTree* t : d_trees)
    {
      delete t;
    }
    d_trees.clear();
  }

  CodeTree* getCodeTreeFor(TNode lbl) const
  {
    uint32_t lblId = d_context.getDeclIdOption(lbl);
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

  void print(std::ostream& out, size_t indent) const
  {
    const PathTree* curr = this;
    while (curr != nullptr)
    {
      for (size_t i = 0; i < indent; ++i)
      {
        out << "  ";
      }
      out << curr->d_label << ":" << curr->d_argIdx;
      if (curr->d_groundArg != nullptr)
      {
        out << ":#" << curr->d_groundArg->getOwnerId() << ":"
            << curr->d_groundArgIdx;
      }
      out << "  " << curr->d_filter << " " << curr->d_code << "\n";
      if (curr->d_firstChild != nullptr)
      {
        curr->d_firstChild->print(out, indent + 1);
      }
      curr = curr->d_sibling;
    }
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
  return NodeManager::isNAryKind(n->getExpr().getKind());
}


// ----------------------------------------- matching abstract machine impl

class MamImpl : public Mam
{
 public:
  MamImpl(SmtContext& ctx, bool useFilters)
      : Mam(ctx),
        d_useFilters(useFilters),
        d_lblHasher(ctx),
        d_ctManager(d_lblHasher, d_trailStack),
        d_compiler(ctx, d_ctManager, d_lblHasher, useFilters),
        d_interpreter(ctx, *this, useFilters),
        d_trees(ctx, d_compiler, d_trailStack),
        d_region(d_trailStack.getRegion()),
        d_r1(nullptr),
        d_r2(nullptr)
  {
    resetPpPc();
  }

  ~MamImpl() override { d_trailStack.reset(); }

  void addPattern(TNode q, TNode mp) override
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

  void pushScope() override { d_trailStack.pushScope(); }

  void popScope(size_t numScopes) override
  {
    if (!d_toMatch.empty())
    {
      for (CodeTree* t : d_toMatch)
      {
        t->resetCandidates();
      }
      d_toMatch.clear();
    }
    d_newPatterns.clear();
    d_trailStack.popScope(numScopes);
  }

  void reset() override
  {
    d_trailStack.reset();
    d_trees.reset();
    d_toMatch.clear();
    d_newPatterns.clear();
    d_isPlbl.clear();
    d_isClbl.clear();
    resetPpPc();
    d_tmpRegion.reset();
  }

  void print(std::ostream& out) override
  {
    out << "mam:\n";
    d_lblHasher.print(out);
    for (CodeTree* t : d_trees.getCodeTrees())
    {
      if (t != nullptr)
      {
        t->print(out);
      }
    }
  }

  void match() override
  {
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

  void rematch(bool useIrrelevant) override
  {
    for (CodeTree* t : d_trees.getCodeTrees())
    {
      if (t == nullptr)
      {
        continue;
      }
      d_interpreter.init(t);
      TNode lbl = t->getRootLbl();
      // executeCore may internalize new applications of lbl, which can grow
      // and reallocate the context's enode vector for lbl, so the vector
      // itself (not just its size) is re-fetched on every iteration.
      for (size_t i = 0; i < d_context.enodesOf(lbl).size(); ++i)
      {
        ENode* curr = d_context.enodesOf(lbl)[i];
        if (useIrrelevant || d_context.isRelevant(curr))
        {
          d_interpreter.executeCore(t, curr);
        }
      }
    }
  }

  void onMatch(TNode q,
               TNode pat,
               size_t numBindings,
               ENode* const* bindings,
               uint32_t maxGeneration,
               std::vector<std::pair<ENode*, ENode*>>& usedENodes) override
  {
    d_context.getStats().d_numMamMatches++;
    uint32_t minGen = 0;
    uint32_t maxGen = 0;
    d_interpreter.getMinMaxTopGeneration(minGen, maxGen);
    d_context.addInstance(
        q, pat, numBindings, bindings, maxGeneration, minGen, maxGen,
        usedENodes);
  }

  bool isShared(ENode* n) const override
  {
    return !d_sharedENodes.empty() && d_sharedENodes.count(n) > 0;
  }

  /**
   * Invoked when n becomes relevant. If lazy is true then n is not added to
   * the list of candidate enodes for matching, and the method only updates
   * the labels.
   */
  void relevantEh(ENode* n, bool lazy) override
  {
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

  bool hasWork() const override
  {
    return !d_toMatch.empty() || !d_newPatterns.empty();
  }

  void addEqEh(ENode* r1, ENode* r2) override
  {
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
  /** Erase a shared enode when its scope is popped. */
  class AddSharedENodeTrail : public Trail
  {
   public:
    AddSharedENodeTrail(MamImpl& m, ENode* n) : d_mam(m), d_enode(n) {}

    void undo() override { d_mam.d_sharedENodes.erase(d_enode); }

   private:
    MamImpl& d_mam;
    ENode* d_enode;
  };

  ENodeVector* mkTmpVector()
  {
    ENodeVector* r = d_pool.mk();
    r->clear();
    return r;
  }

  void recycle(ENodeVector* v) { d_pool.recycle(v); }

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
      t->compressCandidates();
    }
  }

  void addCandidate(ENode* app)
  {
    addCandidate(d_trees.getCodeTreeFor(app->getDecl()), app);
  }

  bool isPlbl(TNode lbl) const
  {
    uint32_t lblId = d_context.getDeclIdOption(lbl);
    return lblId < d_isPlbl.size() && d_isPlbl[lblId];
  }

  bool isClbl(TNode lbl) const
  {
    uint32_t lblId = d_context.getDeclIdOption(lbl);
    return lblId < d_isClbl.size() && d_isClbl[lblId];
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
    uint32_t lblId = d_context.getDeclId(lbl);
    reservex(d_isClbl, lblId + 1, false);
    if (d_isClbl[lblId])
    {
      return;
    }
    d_trailStack.push(
        SetBitvectorTrail<std::vector<bool>>(d_isClbl, lblId));
    Assert(d_isClbl[lblId]);
    uint8_t h = d_lblHasher(lbl);
    for (ENode* app : d_context.enodesOf(lbl))
    {
      if (d_context.isRelevant(app))
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
    uint32_t lblId = d_context.getDeclId(lbl);
    reservex(d_isPlbl, lblId + 1, false);
    if (d_isPlbl[lblId])
    {
      return;
    }
    d_trailStack.push(
        SetBitvectorTrail<std::vector<bool>>(d_isPlbl, lblId));
    Assert(d_isPlbl[lblId]);
    uint8_t h = d_lblHasher(lbl);
    for (ENode* app : d_context.enodesOf(lbl))
    {
      if (d_context.isRelevant(app))
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
      curr = new (d_region) PathTree(p, d_lblHasher);
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
        return mkPatENode(d_context, q, pat[i]);
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
      Path* newPath = new (d_tmpRegion) Path(
          plbl, i, static_cast<uint16_t>(groundArgPos), groundArg, patIdx, p);

      if (isVar(child))
      {
        updateVars(varIndex(child), newPath, q, mp);
        continue;
      }

      if (isGroundPat(child))
      {
        ENode* n = mkPatENode(d_context, q, child);
        updatePlbls(plbl);
        if (!n->hasLblHash())
        {
          n->setLblHash(d_context);
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
    size_t numVars = getNumDecls(q);
    if (numVars >= d_varPaths.size())
    {
      d_varPaths.resize(numVars + 1);
    }
    for (Paths& p : d_varPaths)
    {
      p.clear();
    }
    d_tmpRegion.reset();
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
    ENodeVector* toUnmark = mkTmpVector();
    ENodeVector* toUnmark2 = mkTmpVector();
    t->d_todo = mkTmpVector();
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

        if (d_useFilters
            && currChild->getPlbls().emptyIntersection(filter))
        {
          continue;
        }

        for (ENode* currParent : currChild->getConstParents())
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
              && d_context.isRelevant(currParent))
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
                                currParent->getArg(
                                    currTree->d_groundArgIdx))))
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
                      child->d_todo = mkTmpVector();
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
      recycle(currT->d_todo);
      currT->d_todo = nullptr;
      // remove both marks
      unmarkENodes(toUnmark->size(), toUnmark->data());
      unmarkENodes2(toUnmark2->size(), toUnmark2->data());
      toUnmark->clear();
      toUnmark2->clear();
    }
    recycle(toUnmark);
    recycle(toUnmark2);
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
        if (nPlbl1 == nPlbl2)
        {
          Assert(d_pp[nPlbl1][nPlbl2].second == nullptr);
          if (nR1->getNumParents() <= nR2->getNumParents())
          {
            collectParents(nR1, d_pp[nPlbl1][nPlbl2].first);
          }
          else
          {
            collectParents(nR2, d_pp[nPlbl1][nPlbl2].first);
          }
        }
        else
        {
          Assert(nPlbl1 < nPlbl2);
          if (nR1->getNumParents() <= nR2->getNumParents())
          {
            collectParents(nR1, d_pp[nPlbl1][nPlbl2].first);
          }
          else
          {
            collectParents(nR2, d_pp[nPlbl1][nPlbl2].second);
          }
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
    d_tmpTreesToDelete.clear();
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
      if (d_context.getNumENodesOf(lbl) > 0)
      {
        uint32_t lblId = d_context.getDeclId(lbl);
        reservex(d_tmpTrees, lblId + 1, static_cast<CodeTree*>(nullptr));
        if (d_tmpTrees[lblId] == nullptr)
        {
          d_tmpTrees[lblId] = d_compiler.mkTree(q, mp, 0, false);
          d_tmpTreesToDelete.push_back(lbl);
        }
        else
        {
          d_compiler.insert(d_tmpTrees[lblId], q, mp, 0, true);
        }
      }
    }

    for (TNode lbl : d_tmpTreesToDelete)
    {
      uint32_t lblId = d_context.getDeclId(lbl);
      CodeTree* tmpTree = d_tmpTrees[lblId];
      Assert(tmpTree != nullptr);
      d_interpreter.init(tmpTree);
      for (size_t i = 0; i < d_context.enodesOf(lbl).size(); ++i)
      {
        ENode* app = d_context.enodesOf(lbl)[i];
        if (d_context.isRelevant(app))
        {
          d_interpreter.executeCore(tmpTree, app);
        }
      }
      d_tmpTrees[lblId] = nullptr;
      delete tmpTree;
    }
    d_newPatterns.clear();
  }

  void collectGroundExprs(TNode q, TNode mp)
  {
    std::vector<Node> todo;
    for (size_t i = 0, n = mp.getNumChildren(); i < n; ++i)
    {
      TNode pat = mp[i];
      if (isGroundPat(pat))
      {
        ENode* e = mkPatENode(d_context, q, pat);
        d_context.markAsRelevant(e);
        d_context.pushTrail(AddSharedENodeTrail(*this, e));
        d_sharedENodes.insert(e);
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
        ENode* e = mkPatENode(d_context, q, n);
        d_context.pushTrail(AddSharedENodeTrail(*this, e));
        d_sharedENodes.insert(e);
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

  bool d_useFilters;
  TrailStack d_trailStack;
  LabelHasher d_lblHasher;
  CodeTreeManager d_ctManager;
  Compiler d_compiler;
  Interpreter d_interpreter;
  CodeTreeMap d_trees;

  std::vector<CodeTree*> d_tmpTrees;
  std::vector<Node> d_tmpTreesToDelete;
  std::vector<CodeTree*> d_toMatch;
  /** recently added patterns */
  std::vector<std::pair<Node, Node>> d_newPatterns;

  /**
   * If d_isPlbl[f] is true then when f(c_1, ..., c_n) becomes relevant,
   * lblHash(f) is inserted into c_i->getRoot()->getPlbls() for each c_i.
   */
  std::vector<bool> d_isPlbl;
  /**
   * If d_isClbl[f] is true then when n = f(c_1, ..., c_n) becomes relevant,
   * lblHash(f) is inserted into n->getRoot()->getLbls().
   */
  std::vector<bool> d_isClbl;

  Region& d_region;
  Region d_tmpRegion;
  PathTreePair d_pp[approxSetCapacity()][approxSetCapacity()];
  PathTree* d_pc[approxSetCapacity()][approxSetCapacity()];
  ENodeVectorPool d_pool;

  /** temporary field used to update the path trees */
  std::vector<Paths> d_varPaths;
  /** temporary field used to collect candidates */
  std::vector<PathTree*> d_todo;

  /** the ground terms that appear in patterns */
  std::unordered_set<ENode*> d_sharedENodes;

  ENode* d_r1;
  ENode* d_r2;
};

}  // namespace

Mam* mkMam(SmtContext& ctx) { return new MamImpl(ctx, true); }

}  // namespace z3
}  // namespace cvc5::internal

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
 *
 * A port of z3's smt/mam.cpp. As in z3, the instruction set, the code trees,
 * the compiler, the interpreter and the inverted path index all live in one
 * translation unit, since they are mutually recursive and share the
 * representation of instructions.
 *
 * The machine has two entry points for work, mirroring z3:
 * - notifyNewENode, which queues a new application as a candidate for the code
 *   tree of its label (z3: mam::relevant_eh),
 * - notifyPreMerge, which uses the inverted path index to find the
 *   applications that the merge makes congruent (z3: mam::add_eq_eh),
 * and one entry point for executing the queued work, match (z3: mam::match).
 *
 * See theory/quantifiers/eager/README.md section 2.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__MAM_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__MAM_H

#include <map>
#include <memory>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/eager/egraph.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

/**
 * The opcodes of the machine. This is exactly z3's opcode enumeration
 * (mam.cpp), including the unrolled forms for small arities, which we keep so
 * that a code tree prints the same way z3's does.
 */
enum class Opcode
{
  // Initialize the registers from the candidate, for an application of the
  // given arity. INITN is the general form.
  INIT1,
  INIT2,
  INIT3,
  INIT4,
  INIT5,
  INIT6,
  INITN,
  // Try each application of a label in the class of a register, binding its
  // arguments to consecutive registers. This is a backtracking point.
  BIND1,
  BIND2,
  BIND3,
  BIND4,
  BIND5,
  BIND6,
  BINDN,
  // A match was found; report the bindings.
  YIELD1,
  YIELD2,
  YIELD3,
  YIELD4,
  YIELD5,
  YIELD6,
  YIELDN,
  // The classes of two registers must be the same.
  COMPARE,
  // The class of a register must be the class of a given ground term.
  CHECK,
  // The label set of the class of a register must intersect a given set.
  FILTER,
  // As FILTER, but introduced to combine CHECKs rather than BINDs.
  CFILTER,
  // As FILTER, but against the parent label set.
  PFILTER,
  // The alternative branches of a code tree.
  CHOOSE,
  NOOP,
  // Continue matching the remaining patterns of a multi-pattern.
  CONTINUE,
  // Copy a ground term into a register.
  GET_ENODE,
  // Look up the application of a label to the classes of given registers.
  GET_CGR1,
  GET_CGR2,
  GET_CGR3,
  GET_CGR4,
  GET_CGR5,
  GET_CGR6,
  GET_CGRN,
  // Check that a register holds an application of a label to the classes of
  // given registers.
  IS_CGR
};

/** Base class of the instructions. z3: struct instruction */
struct Instruction
{
  Instruction(Opcode op) : d_opcode(op), d_next(nullptr) {}
  virtual ~Instruction() {}
  bool isInit() const
  {
    return d_opcode >= Opcode::INIT1 && d_opcode <= Opcode::INITN;
  }
  Opcode d_opcode;
  Instruction* d_next;
};

/** INITN: the arity is not implied by the opcode. z3: struct initn */
struct InitN : public Instruction
{
  InitN(size_t numArgs) : Instruction(Opcode::INITN), d_numArgs(numArgs) {}
  size_t d_numArgs;
};

/** COMPARE. z3: struct compare */
struct Compare : public Instruction
{
  Compare(size_t r1, size_t r2)
      : Instruction(Opcode::COMPARE), d_reg1(r1), d_reg2(r2)
  {
  }
  size_t d_reg1;
  size_t d_reg2;
};

/** CHECK. z3: struct check */
struct Check : public Instruction
{
  Check(size_t reg, ENode* e)
      : Instruction(Opcode::CHECK), d_reg(reg), d_enode(e)
  {
  }
  size_t d_reg;
  ENode* d_enode;
};

/** FILTER, CFILTER, PFILTER. z3: struct filter */
struct Filter : public Instruction
{
  Filter(Opcode op, size_t reg, ApproxSet s)
      : Instruction(op), d_reg(reg), d_lblSet(s)
  {
  }
  size_t d_reg;
  ApproxSet d_lblSet;
};

/** GET_ENODE. z3: struct get_enode_instr */
struct GetENode : public Instruction
{
  GetENode(size_t oreg, ENode* e)
      : Instruction(Opcode::GET_ENODE), d_oreg(oreg), d_enode(e)
  {
  }
  size_t d_oreg;
  ENode* d_enode;
};

/** CHOOSE and NOOP. z3: struct choose */
struct Choose : public Instruction
{
  Choose(Opcode op, Choose* alt) : Instruction(op), d_alt(alt) {}
  Choose* d_alt;
};

/** BIND. z3: struct bind */
struct Bind : public Instruction
{
  Bind(Opcode op, Node label, size_t numArgs, size_t ireg, size_t oreg)
      : Instruction(op),
        d_label(label),
        d_numArgs(numArgs),
        d_ireg(ireg),
        d_oreg(oreg)
  {
  }
  Node d_label;
  size_t d_numArgs;
  size_t d_ireg;
  size_t d_oreg;
};

/** GET_CGR. z3: struct get_cgr */
struct GetCgr : public Instruction
{
  GetCgr(Opcode op, Node label, ApproxSet s, size_t oreg)
      : Instruction(op), d_label(label), d_lblSet(s), d_oreg(oreg)
  {
  }
  Node d_label;
  ApproxSet d_lblSet;
  size_t d_oreg;
  std::vector<size_t> d_iregs;
};

/** IS_CGR. z3: struct is_cgr */
struct IsCgr : public Instruction
{
  IsCgr(Node label, size_t ireg)
      : Instruction(Opcode::IS_CGR), d_label(label), d_ireg(ireg)
  {
  }
  Node d_label;
  size_t d_ireg;
  std::vector<size_t> d_iregs;
};

/** YIELD. z3: struct yield */
struct Yield : public Instruction
{
  Yield(Opcode op, Node q, Node pat)
      : Instruction(op), d_quant(q), d_pattern(pat)
  {
  }
  Node d_quant;
  Node d_pattern;
  /** the register holding the binding of each bound variable, in order */
  std::vector<size_t> d_bindings;
};

/**
 * A joint of a CONTINUE instruction, which constrains which applications are
 * worth considering for the next pattern term of a multi-pattern. z3: struct
 * joint2 and the NULL_TAG/GROUND_TERM_TAG/VAR_TAG/NESTED_VAR_TAG tagging of
 * cont::m_joints.
 */
struct Joint
{
  enum class Kind
  {
    NONE,
    GROUND_TERM,
    VAR,
    NESTED_VAR
  };
  Kind d_kind = Kind::NONE;
  /** for GROUND_TERM */
  ENode* d_enode = nullptr;
  /** for VAR and NESTED_VAR, the register holding the variable */
  size_t d_reg = 0;
  /** for NESTED_VAR, the enclosing label and the argument position */
  Node d_label;
  size_t d_argPos = 0;
};

/** CONTINUE. z3: struct cont */
struct Continue : public Instruction
{
  Continue(Node label, size_t numArgs, size_t oreg, ApproxSet s)
      : Instruction(Opcode::CONTINUE),
        d_label(label),
        d_numArgs(numArgs),
        d_oreg(oreg),
        d_lblSet(s)
  {
  }
  Node d_label;
  size_t d_numArgs;
  size_t d_oreg;
  /** a singleton set containing the label, empty if filters are off */
  ApproxSet d_lblSet;
  std::vector<Joint> d_joints;
};

std::ostream& operator<<(std::ostream& out, const Instruction& i);

/**
 * A code tree, i.e. the compiled form of all patterns whose first pattern term
 * has the same top symbol. Holds the enodes that have yet to be matched
 * against it. z3: class code_tree.
 */
class CodeTree
{
  friend class Compiler;
  friend class CodeTreeManager;
  friend class Interpreter;
  friend class Mam;

 public:
  CodeTree(Node rootLabel, size_t numArgs, bool filterCandidates);
  /** The top symbol of the first pattern term of every pattern in this tree */
  TNode getRootLabel() const { return d_rootLabel; }
  /** The arity the candidates must have. z3: code_tree::expected_num_args */
  size_t getExpectedNumArgs() const { return d_numArgs; }
  size_t getNumRegs() const { return d_numRegs; }
  size_t getNumChoices() const { return d_numChoices; }
  /** Whether duplicate candidates are filtered out when executing */
  bool filterCandidates() const { return d_filterCandidates; }
  Instruction* getRoot() const { return d_root; }

  /** Are there candidates queued for this tree? */
  bool hasCandidates() const { return !d_candidates.empty(); }
  /** Queue e as a candidate */
  void addCandidate(ENode* e) { d_candidates.push_back(e); }
  const std::vector<ENode*>& getCandidates() const { return d_candidates; }
  /** Drop the queued candidates. z3 does this on pop and after matching. */
  void resetCandidates() { d_candidates.clear(); }
  /** Print this tree */
  void display(std::ostream& out) const;

 private:
  /** Print the instructions reachable from head */
  void displaySeq(std::ostream& out, Instruction* head, size_t indent) const;
  /** Print the alternatives of a choice point */
  void displayChildren(std::ostream& out,
                       Choose* firstChild,
                       size_t indent) const;
  Node d_rootLabel;
  size_t d_numArgs;
  bool d_filterCandidates;
  size_t d_numRegs;
  size_t d_numChoices;
  Instruction* d_root;
  std::vector<ENode*> d_candidates;
  /** The patterns compiled into this tree, for debugging */
  std::vector<Node> d_patterns;
};

/**
 * Owns the instructions and the code trees. z3: class code_tree_manager.
 *
 * Nothing is freed when a scope is popped: z3 deletes the code tree it created
 * for a pattern (new_obj_trail in mam_impl::mk_path_tree), we keep it, since
 * the only consequence is that the memory is held until the machine is
 * destroyed, and the trees are unreachable once the path index entry pointing
 * at them is restored. The same applies to the path trees owned by Mam.
 */
class CodeTreeManager
{
 public:
  CodeTreeManager(EGraph& eg, Trail& trail);
  ~CodeTreeManager();
  /** Allocate a tree whose first pattern term has top symbol label */
  CodeTree* mkCodeTree(Node label, size_t numArgs, bool filterCandidates);

  //----------------------------------------------- instruction constructors
  Instruction* mkInit(size_t numArgs);
  Compare* mkCompare(size_t reg1, size_t reg2);
  Check* mkCheck(size_t reg, ENode* e);
  Filter* mkFilter(size_t reg, ApproxSet s);
  Filter* mkPFilter(size_t reg, ApproxSet s);
  Filter* mkCFilter(size_t reg, ApproxSet s);
  GetENode* mkGetENode(size_t oreg, ENode* e);
  Choose* mkChoose(Choose* alt);
  Choose* mkNoop();
  Bind* mkBind(Node label, size_t numArgs, size_t ireg, size_t oreg);
  GetCgr* mkGetCgr(Node label, size_t oreg, const std::vector<size_t>& iregs);
  IsCgr* mkIsCgr(Node label, size_t ireg, const std::vector<size_t>& iregs);
  Yield* mkYield(Node q, Node pat, const std::vector<size_t>& bindings);
  Continue* mkCont(Node label,
                   size_t numArgs,
                   size_t oreg,
                   ApproxSet s,
                   const std::vector<Joint>& joints);
  //------------------------------------------- end instruction constructors

  /** Set the successor of instr, recording the old value on the trail */
  void setNext(Instruction* instr, Instruction* next);
  /** Record the number of registers of tree on the trail */
  void saveNumRegs(CodeTree* tree);
  /** Record the number of choice points of tree on the trail */
  void saveNumChoices(CodeTree* tree);
  /** Add h to the label set of a filter, recording the old value */
  void insertNewLblHash(Filter* instr, size_t h);

 private:
  /** Take ownership of an instruction */
  template <class T>
  T* own(T* i)
  {
    d_instructions.emplace_back(i);
    return i;
  }
  EGraph& d_egraph;
  Trail& d_trail;
  std::vector<std::unique_ptr<Instruction>> d_instructions;
  std::vector<std::unique_ptr<CodeTree>> d_trees;
};

/**
 * An element of a path from a variable of a pattern up to the top of the
 * pattern term it occurs in. z3: struct path.
 */
struct Path
{
  Node d_label;
  size_t d_argIdx;
  size_t d_groundArgIdx;
  ENode* d_groundArg;
  size_t d_patternIdx;
  Path* d_child;
};

/**
 * The inverted path index: for a pair of label hashes, the paths that have to
 * be followed upwards from the classes being merged in order to find the
 * applications the merge makes congruent. z3: struct path_tree.
 */
struct PathTree
{
  PathTree(const Path& p, size_t labelHash);
  Node d_label;
  size_t d_argIdx;
  size_t d_groundArgIdx;
  ENode* d_groundArg;
  CodeTree* d_code;
  ApproxSet d_filter;
  PathTree* d_sibling;
  PathTree* d_firstChild;
  /** temporary, the classes to walk up from at this level */
  std::vector<ENode*> d_todo;
  /** temporary, whether this node is queued for processing */
  bool d_todoActive;
  /** Print this path tree */
  void display(std::ostream& out, size_t indent) const;
};

class Mam;

/**
 * The consumer of the matches the machine finds. Implemented by the instance
 * queue. z3: mam::on_match, which forwards to context::add_instance.
 */
class MamListener
{
 public:
  virtual ~MamListener() {}
  /**
   * q was matched through pattern pat with the given bindings, one per bound
   * variable of q. maxGeneration is the maximum generation of any enode used
   * in the match, minTopGeneration and maxTopGeneration the minimum and
   * maximum generation of the top-level pattern instances.
   */
  virtual void onMatch(TNode q,
                       TNode pat,
                       const std::vector<ENode*>& bindings,
                       uint32_t maxGeneration,
                       uint32_t minTopGeneration,
                       uint32_t maxTopGeneration) = 0;
};

/**
 * Compiles a multi-pattern into a code tree, or inserts it into an existing
 * one, sharing the longest common prefix of instructions. z3: class compiler.
 */
class Compiler : protected EnvObj
{
 public:
  Compiler(Env& env, EGraph& eg, CodeTreeManager& ctm, bool useFilters);
  /**
   * Compile the multi-pattern mp of q, with the firstIdx^th pattern term taken
   * as the first one, into a fresh code tree.
   */
  CodeTree* mkTree(TNode q, TNode mp, size_t firstIdx, bool filterCandidates);
  /**
   * Insert the multi-pattern mp of q into the existing tree t, with the
   * firstIdx^th pattern term taken as the first one. A temporary tree is one
   * that is thrown away after matching, so no undo information is recorded.
   */
  void insert(CodeTree* t, TNode q, TNode mp, size_t firstIdx, bool isTmpTree);

 private:
  /** Whether a register has already been constrained by a filter */
  enum class CheckMark
  {
    NOT_CHECKED,
    CHECK_SET,
    CHECK_SINGLETON
  };
  /** Prepare to compile mp into t. z3: compiler::init */
  void init(CodeTree* t, TNode q, TNode mp, size_t firstIdx);
  void setRegister(size_t reg, TNode p);
  TNode getRegister(size_t reg) const;
  CheckMark getCheckMark(size_t reg) const;
  void setCheckMark(size_t reg, CheckMark cm);
  /** Is n a bound variable of the quantifier being compiled? */
  bool isPatVar(TNode n, size_t& varId) const;
  /** Is n ground, i.e. free of the bound variables of the quantifier? */
  static bool isGround(TNode n);
  /** The enode of the ground pattern term n. z3: mk_enode */
  ENode* mkENode(TNode n);
  /** z3: compiler::all_args_are_bound_vars */
  bool allArgsAreBoundVars(TNode n) const;
  /** z3: compiler::get_stats */
  void getStats(TNode n, size_t& sz, size_t& numUnboundVars) const;
  void getStatsCore(TNode n, size_t& sz, size_t& numUnboundVars) const;
  /** z3: compiler::get_num_bound_vars */
  size_t getNumBoundVars(TNode n, bool& hasUnboundVars) const;
  size_t getNumBoundVarsCore(TNode n, bool& hasUnboundVars) const;
  /** z3: compiler::linearise_core */
  void lineariseCore();
  /** z3: compiler::gen_mp_filter */
  size_t genMpFilter(TNode n);
  /** z3: compiler::linearise_multi_pattern */
  void lineariseMultiPattern(size_t firstIdx);
  /** z3: compiler::linearise */
  void linearise(Instruction* head, size_t firstIdx);
  /** z3: compiler::set_next */
  void setNext(Instruction* instr, Instruction* next);
  /** z3: compiler::find_best_child */
  Choose* findBestChild(Choose* firstChild);
  /** z3: compiler::get_compatibility_measure */
  size_t getCompatibilityMeasure(Choose* child, bool& simple);
  /** z3: compiler::get_pat_lbl_hash */
  size_t getPatLblHash(size_t reg);
  //--------------------------------------------- compatibility of instructions
  bool isCompatible(Bind* instr);
  bool isCompatible(Compare* instr);
  bool isCompatible(Check* instr);
  bool isCompatible(Filter* instr);
  bool isCompatible(Continue* instr);
  bool isCfilterCompatible(Filter* instr);
  bool isSemiCompatible(Check* instr);
  bool isSemiCompatible(Filter* instr);
  //----------------------------------------- end compatibility of instructions
  /** z3: compiler::insert(instruction*, unsigned) */
  void insertInto(Instruction* head, size_t firstMpIdx);

  EGraph& d_egraph;
  CodeTreeManager& d_ctm;
  bool d_useFilters;
  /** The pattern term held by each register */
  std::vector<Node> d_registers;
  /** The registers whose patterns still have to be processed */
  std::vector<size_t> d_todo;
  /** Scratch list used while linearising */
  std::vector<size_t> d_aux;
  /** For each bound variable, the register it is bound in, or -1 */
  std::vector<int64_t> d_vars;
  /** The index of each bound variable of the quantifier being compiled */
  std::map<Node, size_t> d_varIndex;
  Node d_quant;
  Node d_mp;
  CodeTree* d_tree;
  size_t d_numChoices;
  bool d_isTmpTree;
  /** Which pattern terms of the multi-pattern have been compiled */
  std::vector<bool> d_mpAlreadyProcessed;
  /** The register each pattern term was first matched in */
  std::map<Node, size_t> d_matchedExprs;
  /** The check mark of each register */
  std::vector<CheckMark> d_mark;
  /** Scratch lists used while measuring compatibility and inserting */
  std::vector<size_t> d_toReset;
  std::vector<Instruction*> d_compatible;
  std::vector<Instruction*> d_incompatible;
  std::vector<Instruction*> d_seq;
  /**
   * Set when a ground pattern term could not be given an enode, in which case
   * the pattern is not compiled.
   */
  bool d_failed;
};

/**
 * The interpreter of the machine. One instance is shared by all code trees, as
 * in z3; it is not reentrant.
 */
class Interpreter : protected EnvObj
{
 public:
  Interpreter(Env& env, EGraph& eg, Mam& mam, bool useFilters);
  /** Prepare to execute t */
  void init(CodeTree* t);
  /**
   * Run t on all of its queued candidates. Returns false if execution was
   * interrupted. z3: interpreter::execute.
   */
  bool execute(CodeTree* t);
  /** Run t on the single candidate n. z3: interpreter::execute_core */
  bool executeCore(CodeTree* t, ENode* n);

 private:
  /** A point to resume execution from. z3: struct backtrack_point */
  struct BacktrackPoint
  {
    const Instruction* d_instr = nullptr;
    uint32_t d_oldMaxGeneration = 0;
    /** for BIND, the application currently bound */
    ENode* d_curr = nullptr;
    /** for CONTINUE, the candidates and the position in them */
    const std::vector<ENode*>* d_rest = nullptr;
    std::vector<ENode*> d_restOwned;
    size_t d_restIdx = 0;
  };
  /** z3: interpreter::get_first_f_app */
  ENode* getFirstFApp(TNode lbl, size_t numExpectedArgs, ENode* curr);
  /** z3: interpreter::get_next_f_app */
  ENode* getNextFApp(TNode lbl,
                     size_t numExpectedArgs,
                     ENode* first,
                     ENode* curr);
  /** z3: interpreter::exec_is_cgr */
  bool execIsCgr(const IsCgr* instr);
  /** z3: interpreter::mk_depth1_vector */
  void mkDepth1Vector(ENode* n, TNode f, size_t i, std::vector<ENode*>& v);
  /**
   * z3: interpreter::mk_depth2_vector. Returns false if the joint gives no
   * vector at all, which z3 signals with a null pointer.
   */
  bool mkDepth2Vector(const Joint& j,
                      TNode f,
                      size_t i,
                      std::vector<ENode*>& v);
  /** z3: interpreter::init_continue */
  ENode* initContinue(const Continue* c, size_t expectedNumArgs);
  /** z3: interpreter::update_max_generation */
  void updateMaxGeneration(ENode* n);
  /** z3: interpreter::get_min_max_top_generation */
  void getMinMaxTopGeneration(uint32_t& min, uint32_t& max);
  /**
   * Resume from the most recent choice point, setting the program counter.
   * Returns false if there is no alternative left, i.e. execution is done.
   */
  bool backtrack();
  /** Set the registers oreg..oreg+n-1 from the arguments of app */
  void setRegisters(size_t oreg, ENode* app, size_t numArgs);

  EGraph& d_egraph;
  Mam& d_mam;
  bool d_useFilters;
  /** The registers */
  std::vector<ENode*> d_registers;
  /** The bindings of the bound variables */
  std::vector<ENode*> d_bindings;
  /** Scratch list used by GET_CGR and IS_CGR */
  std::vector<ENode*> d_args;
  /** The backtracking stack and its height */
  std::vector<BacktrackPoint> d_backtrack;
  size_t d_top;
  /** The program counter */
  const Instruction* d_pc;
  /** The maximum generation of an enode processed so far */
  uint32_t d_maxGeneration;
  /** The top-level pattern instances, for the generation bookkeeping */
  std::vector<ENode*> d_patternInstances;
  std::vector<uint32_t> d_minTopGeneration;
  std::vector<uint32_t> d_maxTopGeneration;
};

/**
 * The matching abstract machine. z3: class mam_impl.
 */
class Mam : protected EnvObj, public EGraphListener
{
  friend class Interpreter;

 public:
  Mam(Env& env, EGraph& eg, Trail& trail, bool useFilters);
  ~Mam();

  /** Set the listener, which must outlive this object */
  void setListener(MamListener* l) { d_listener = l; }

  /**
   * Add the multi-pattern mp of the quantified formula q. z3:
   * mam_impl::add_pattern.
   */
  void addPattern(TNode q, TNode mp);

  //----------------------------------------------- EGraphListener
  void notifyNewENode(ENode* e) override;
  void notifyPreMerge(ENode* r1, ENode* r2) override;
  //------------------------------------------- end EGraphListener

  /** Is there queued matching work? z3: mam_impl::has_work */
  bool hasWork() const;
  /** Run the queued matching work. z3: mam_impl::match */
  void match();
  /**
   * Re-run every code tree on every application of its root label. z3:
   * mam_impl::rematch, used for the lazy mam at final check.
   */
  void rematch();
  /** Drop the queued work, called when a scope is popped */
  void clearWork();
  /** Is e a ground term occurring in a pattern? z3: mam_impl::is_shared */
  bool isShared(ENode* e) const;

  /** Report a match, called by the interpreter. z3: mam_impl::on_match */
  void onMatch(TNode q,
               TNode pat,
               const std::vector<ENode*>& bindings,
               uint32_t maxGeneration,
               uint32_t minTopGeneration,
               uint32_t maxTopGeneration);

  /** Print the machine */
  void display(std::ostream& out) const;

  /** Statistics of this machine, for -t eager-inst */
  struct Stats
  {
    /** candidate enodes queued for matching */
    uint64_t d_numCandidates = 0;
    /** merges observed */
    uint64_t d_numMerges = 0;
    /** calls to match */
    uint64_t d_numMatchCalls = 0;
    /** code tree executions */
    uint64_t d_numExecutions = 0;
    /** matches found */
    uint64_t d_numMatches = 0;
  };
  const Stats& getStats() const { return d_stats; }

 private:
  /** Queue e as a candidate of the code tree of its label */
  void addCandidate(ENode* e);
  /** Queue e as a candidate of t */
  void addCandidate(CodeTree* t, ENode* e);
  /** The code tree for label, or nullptr */
  CodeTree* getCodeTree(TNode label) const;
  /**
   * Compile the multi-pattern mp of q, with its patIdx^th pattern term taken
   * as the first one, into the code tree of that term's top symbol.
   * z3: code_tree_map::add_pattern.
   */
  void addPatternToTree(TNode q, TNode mp, size_t patIdx);
  /**
   * Update the label filters and the inverted path index for the pattern term
   * pat, which occurs at the path p within the patIdx^th pattern term of mp.
   */
  void updateFilters(TNode pat, Path* p, TNode q, TNode mp, size_t patIdx);
  /** Update them for all of the pattern terms of mp */
  void updateFilters(TNode q, TNode mp);
  /** z3: mam_impl::update_vars */
  void updateVars(size_t varId, Path* p, TNode q, TNode mp);
  /** The first ground argument of pat and its position. z3: get_ground_arg */
  ENode* getGroundArg(TNode pat, size_t& pos);
  /** Allocate a path, valid for the duration of one updateFilters call */
  Path* mkPath(Node label,
               size_t argIdx,
               size_t groundArgIdx,
               ENode* groundArg,
               size_t patIdx,
               Path* child);
  /** Do p1 and p2 describe the same path? z3: is_equal */
  static bool isEqualPath(const Path* p1, const Path* p2);
  /** Allocate the path tree for p. z3: mam_impl::mk_path_tree */
  PathTree* mkPathTree(Path* p, TNode q, TNode mp);
  /** Insert p into the path tree t. z3: mam_impl::insert */
  void insertPathTree(PathTree* t, Path* p, TNode q, TNode mp);
  /** z3: mam_impl::update_pc */
  void updatePc(size_t h1, size_t h2, Path* p, TNode q, TNode mp);
  /** z3: mam_impl::update_pp */
  void updatePp(size_t h1, size_t h2, Path* p1, Path* p2, TNode q, TNode mp);
  /** Collect the ground terms of mp. z3: mam_impl::collect_ground_exprs */
  void collectGroundTerms(TNode q, TNode mp);
  /**
   * Walk up from the class of r along the paths of t, queueing the
   * applications found as candidates. z3: mam_impl::collect_parents.
   */
  void collectParents(ENode* r, PathTree* t);
  /** z3: mam_impl::process_pc */
  void processPc(ENode* r1, ENode* r2);
  /** z3: mam_impl::process_pp */
  void processPp(ENode* r1, ENode* r2);
  /** Match the patterns added since the last call. z3: match_new_patterns */
  void matchNewPatterns();
  /**
   * Are n1 and n2 equal, taking the merge currently being processed into
   * account? z3: mam_impl::is_eq.
   */
  bool isEqModPending(ENode* n1, ENode* n2) const;

  EGraph& d_egraph;
  Trail& d_trail;
  /** Whether the label filters are used */
  bool d_useFilters;
  /** The listener */
  MamListener* d_listener;
  /** Owns the instructions and trees */
  CodeTreeManager d_ctm;
  /** The compiler */
  Compiler d_compiler;
  /** The interpreter */
  Interpreter d_interpreter;
  /** Map from labels to code trees. z3: class code_tree_map */
  std::map<Node, CodeTree*> d_trees;
  /** The code trees with queued candidates. z3: m_to_match */
  std::vector<CodeTree*> d_toMatch;
  /** The patterns added since the last match. z3: m_new_patterns */
  std::vector<std::pair<Node, Node>> d_newPatterns;
  /** The inverted path index, parent-child. z3: m_pc */
  std::vector<PathTree*> d_pc;
  /** The inverted path index, parent-parent. z3: m_pp */
  std::vector<std::pair<PathTree*, PathTree*>> d_pp;
  /** The ground terms occurring in patterns. z3: m_shared_enodes */
  std::unordered_set<Node> d_sharedTerms;
  /** Owns the path trees */
  std::vector<std::unique_ptr<PathTree>> d_pathTrees;
  /** The paths of one updateFilters call. z3: m_tmp_region */
  std::vector<std::unique_ptr<Path>> d_tmpPaths;
  /** For each bound variable, the paths it occurs at. z3: m_var_paths */
  std::vector<std::vector<Path*>> d_varPaths;
  /** The index of each bound variable of the quantifier being processed */
  std::map<Node, size_t> d_varIndex;
  /** The path trees to process, used by collectParents. z3: m_todo */
  std::vector<PathTree*> d_todo;
  /** The roots of the merge being processed. z3: m_r1, m_r2 */
  ENode* d_r1;
  ENode* d_r2;
  /** Statistics */
  Stats d_stats;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif

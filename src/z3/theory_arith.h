/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The simplex-based arithmetic solver of the ported Z3 core.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), files
 * src/smt/theory_arith.h, theory_arith_core.h, theory_arith_aux.h,
 * theory_arith_eq.h, theory_arith_int.h and (in part) theory_arith_nl.h, and
 * recast in cvc5 style.
 *
 * This is theory_arith<mi_ext>, which Z3 instantiates as theory_mi_arith for
 * smt.arith.solver=2 -- the solver Verus runs Z3 with. Numerals are rationals
 * and the values of variables are rationals extended with an infinitesimal
 * (InfRational), which is how a strict bound is represented. The template
 * parameter of the original is resolved to mi_ext throughout.
 *
 * Not ported: the theory_opt interface (maximize, objectives), the Groebner
 * basis and interval based nonlinear reasoning, proof coefficients, and the
 * debug-only invariant checks. The nonlinear parts that run with
 * smt.arith.nl=false are ported: a monomial is a variable of the simplex,
 * propagate_linear_monomials linearizes one whose factors are fixed but one,
 * and process_non_linear gives up unless check_monomial_assignments holds.
 */

#include "cvc5_private.h"

#ifndef CVC5__Z3__THEORY_ARITH_H
#define CVC5__Z3__THEORY_ARITH_H

#include <map>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "expr/node.h"
#include "z3/arith_eq_adapter.h"
#include "z3/params.h"
#include "z3/theory.h"
#include "z3/util/heap.h"
#include "z3/util/inf_rational.h"
#include "z3/util/nat_set.h"
#include "z3/util/numeral.h"
#include "z3/util/random_gen.h"
#include "z3/util/uint_set.h"

namespace cvc5::internal {
namespace z3 {

struct TheoryArithStats
{
  uint64_t d_conflicts = 0, d_addRows = 0, d_pivots = 0, d_diseqCs = 0,
           d_gomoryCuts = 0, d_branches = 0, d_gcdTests = 0, d_gcdConflicts = 0,
           d_patches = 0, d_patchesSucc = 0;
  uint64_t d_assertLower = 0, d_assertUpper = 0, d_assertDiseq = 0,
           d_core2thEqs = 0, d_core2thDiseqs = 0;
  uint64_t d_th2coreEqs = 0, d_th2coreDiseqs = 0, d_boundProps = 0,
           d_offsetEqs = 0, d_fixedEqs = 0, d_offlineEqs = 0;
  uint64_t d_maxMin = 0;
  uint64_t d_assumeEqs = 0;
  uint64_t d_nlBranching = 0, d_nlLinear = 0, d_nlBounds = 0;
  uint64_t d_branchInfeasibleInt = 0, d_branchInfeasibleVar = 0;
  uint64_t d_tableauMaxRows = 0, d_tableauMaxColumns = 0;
};

/**
 * - There are 3 kinds of variables in the tableau: base, quasi-base, and
 *   non-base.
 * - Each base var and quasi-base var v owns a row R(v).
 * - If v is a base var, then R(v) contains v and other non-base variables.
 * - If v is a quasi-base var, then R(v) contains v and other base and
 *   non-base variables.
 * - Each quasi-base var occurs only once in the tableau (i.e., it occurs in
 *   R(v)).
 * - A quasi-base var does not have upper & lower bounds and distinct set.
 * - A quasi-base var v can be transformed into a base var by eliminating the
 *   base vars v' in R(v). This can be accomplished by adding -c * R(v') where
 *   c is the coefficient of v' in R(v).
 * - A column is used to store the occurrences of a non-base var v' in rows
 *   R(v), where v is a base variable.
 * - An implied bound stores the linear equation that implied it.
 */
class TheoryArith : public Theory
{
 public:
  using Numeral = Rational;
  using InfNumeral = InfRational;
  using NumeralVector = std::vector<Numeral>;

  static const int s_deadRowId = -1;

  TheoryArith(SmtContext& ctx);
  ~TheoryArith() override;

  void setup() override;

  LBool getPhase(BoolVar v) override;

  const char* getName() const override { return "arithmetic"; }

  void print(std::ostream& out) const override;

  // ------------------------------------------------------ model generation
  bool getValue(ENode* n, Node& r) override;

  const TheoryArithStats& getStats() const { return d_stats; }

  /** The number of equality axioms the adapter created. */
  uint64_t getNumEqAxioms() const
  {
    return d_arithEqAdapter.getStats().d_numEqAxioms;
  }

 protected:
  // ------------------------------------------------------- mi_ext
  InfNumeral d_intEpsilon;
  InfNumeral d_realEpsilon;
  static Numeral fractionalPart(const InfNumeral& n)
  {
    Assert(n.isRational());
    return n.getRational() - floor(n);
  }
  static Numeral fractionalPart(const Numeral& n) { return n - floor(n); }
  static InfNumeral mkInfNumeral(const Numeral& n, const Numeral& r)
  {
    return InfNumeral(n, r);
  }
  static bool isInfinite(const InfNumeral&) { return false; }

  bool proofsEnabled() const { return false; }
  bool coeffsEnabled() const { return false; }

  struct LinearMonomial
  {
    Numeral d_coeff;
    TheoryVar d_var;
    LinearMonomial() : d_var(s_nullTheoryVar) {}
    LinearMonomial(const Numeral& c, TheoryVar v) : d_coeff(c), d_var(v) {}
  };

  /**
   * A RowEntry is d_var * d_coeff. d_colIdx points to the place in the
   * column where the variable occurs.
   */
  struct RowEntry
  {
    Numeral d_coeff;
    TheoryVar d_var = 0;
    union
    {
      int d_colIdx;
      int d_nextFreeRowEntryIdx;
    };

    RowEntry() : d_colIdx(0) {}
    RowEntry(const Numeral& c, TheoryVar v) : d_coeff(c), d_var(v), d_colIdx(0)
    {
    }
    bool isDead() const { return d_var == s_nullTheoryVar; }
  };

  /**
   * A column entry points to the row and the row entry within the row that
   * has a non-zero coefficient on the variable of the column.
   */
  struct ColEntry
  {
    int d_rowId = 0;
    union
    {
      int d_rowIdx;
      int d_nextFreeRowEntryIdx;
    };

    ColEntry(int r, int i) : d_rowId(r), d_rowIdx(i) {}
    ColEntry() : d_rowIdx(0) {}
    bool isDead() const { return d_rowId == s_deadRowId; }
  };

  struct Column;

  /**
   * A row contains a base variable and a set of row entries. The base
   * variable must occur in the set of row entries with coefficient 1.
   */
  struct Row
  {
    std::vector<RowEntry> d_entries;
    /** the real size; d_entries contains dead row entries */
    size_t d_size;
    int d_baseVar;
    /** first available position */
    int d_firstFreeIdx;
    Row();
    size_t size() const { return d_size; }
    size_t numEntries() const { return d_entries.size(); }
    void reset();
    RowEntry& operator[](size_t idx) { return d_entries[idx]; }
    const RowEntry& operator[](size_t idx) const { return d_entries[idx]; }
    std::vector<RowEntry>::iterator begin() { return d_entries.begin(); }
    std::vector<RowEntry>::const_iterator begin() const
    {
      return d_entries.begin();
    }
    std::vector<RowEntry>::iterator end() { return d_entries.end(); }
    std::vector<RowEntry>::const_iterator end() const
    {
      return d_entries.end();
    }
    RowEntry& addRowEntry(int& posIdx);
    void delRowEntry(size_t idx);
    void compress(std::vector<Column>& cols);
    void compressIfNeeded(std::vector<Column>& cols);
    void saveVarPos(std::vector<int>& resultMap) const;
    void resetVarPos(std::vector<int>& resultMap) const;
    TheoryVar getBaseVar() const { return d_baseVar; }
    void print(std::ostream& out) const;
    Numeral getDenominatorsLcm() const;
    int getIdxOf(TheoryVar v) const;
  };

  /**
   * A column stores in which rows a variable occurs. The column may have
   * free/dead entries. d_firstFreeIdx is a reference to the first free/dead
   * entry.
   */
  struct Column
  {
    std::vector<ColEntry> d_entries;
    size_t d_size = 0;
    int d_firstFreeIdx = -1;

    size_t size() const { return d_size; }
    size_t numEntries() const { return d_entries.size(); }
    void reset();
    void compress(std::vector<Row>& rows);
    void compressIfNeeded(std::vector<Row>& rows);
    void compressSingleton(std::vector<Row>& rows, size_t singletonPos);
    const ColEntry* getFirstColEntry() const;
    ColEntry& operator[](size_t idx) { return d_entries[idx]; }
    const ColEntry& operator[](size_t idx) const { return d_entries[idx]; }
    std::vector<ColEntry>::iterator begin() { return d_entries.begin(); }
    std::vector<ColEntry>::const_iterator begin() const
    {
      return d_entries.begin();
    }
    std::vector<ColEntry>::iterator end() { return d_entries.end(); }
    std::vector<ColEntry>::const_iterator end() const
    {
      return d_entries.end();
    }
    ColEntry& addColEntry(int& posIdx);
    void delColEntry(size_t idx);
  };

  enum BoundKind
  {
    B_LOWER,
    B_UPPER
  };

  using EqVector = std::vector<ENodePair>;

  /**
   * The antecedents of a bound or a conflict. Z3 also keeps the
   * coefficients, for proofs and for theory_opt's conflict recording; the
   * port has neither, so only the literals and equalities are kept.
   */
  class AntecedentsT
  {
   public:
    void reset()
    {
      d_lits.clear();
      d_eqs.clear();
    }
    const LiteralVector& lits() const { return d_lits; }
    const EqVector& eqs() const { return d_eqs; }
    void pushLit(Literal l, const Numeral&, bool) { d_lits.push_back(l); }
    void pushEq(const ENodePair& p, const Numeral&, bool)
    {
      d_eqs.push_back(p);
    }
    void append(size_t sz, const Literal* ls)
    {
      d_lits.insert(d_lits.end(), ls, ls + sz);
    }
    void append(size_t sz, const ENodePair* ps)
    {
      d_eqs.insert(d_eqs.end(), ps, ps + sz);
    }

   private:
    LiteralVector d_lits;
    EqVector d_eqs;
  };

  /**
   * A scoped handle on one of the theory's three antecedents buffers, which
   * keeps nested uses from clobbering each other.
   */
  class Antecedents
  {
   public:
    Antecedents(TheoryArith& th);
    ~Antecedents();
    const LiteralVector& lits() const { return d_a.lits(); }
    const EqVector& eqs() const { return d_a.eqs(); }
    void pushLit(Literal l, const Numeral& r, bool e) { d_a.pushLit(l, r, e); }
    void pushEq(const ENodePair& p, const Numeral& r, bool e)
    {
      d_a.pushEq(p, r, e);
    }
    void append(size_t sz, const Literal* ls) { d_a.append(sz, ls); }
    void append(size_t sz, const ENodePair* ps) { d_a.append(sz, ps); }

   private:
    TheoryArith& d_th;
    AntecedentsT& d_a;
  };

  class Bound
  {
   public:
    Bound(TheoryVar v, const InfNumeral& val, BoundKind k, bool a)
        : d_var(v), d_value(val), d_boundKind(k), d_atom(a)
    {
    }
    virtual ~Bound() = default;
    TheoryVar getVar() const { return d_var; }
    BoundKind getBoundKind() const
    {
      return static_cast<BoundKind>(d_boundKind);
    }
    bool isAtom() const { return d_atom; }
    const InfNumeral& getValue() const { return d_value; }
    virtual bool hasJustification() const { return false; }
    virtual void pushJustification(Antecedents& antecedents,
                                   const Numeral& coeff,
                                   bool proofsEnabled)
    {
    }
    virtual std::ostream& print(const TheoryArith& th, std::ostream& out) const;

   protected:
    TheoryVar d_var;
    InfNumeral d_value;
    unsigned d_boundKind : 1;
    unsigned d_atom : 1;
  };

  enum AtomKind
  {
    A_LOWER,
    A_UPPER
  };

  class Atom : public Bound
  {
   public:
    Atom(BoolVar bv, TheoryVar v, const InfNumeral& k, AtomKind kind);
    AtomKind getAtomKind() const { return static_cast<AtomKind>(d_atomKind); }
    const InfNumeral& getK() const { return d_k; }
    BoolVar getBoolVar() const { return d_bvar; }
    bool isTrue() const { return d_isTrue; }
    void assignEh(bool isTrue, const InfNumeral& epsilon);
    bool hasJustification() const override { return true; }
    void pushJustification(Antecedents& a,
                           const Numeral& coeff,
                           bool proofsEnabled) override
    {
      a.pushLit(Literal(getBoolVar(), !d_isTrue), coeff, proofsEnabled);
    }
    std::ostream& print(const TheoryArith& th,
                        std::ostream& out) const override;

   protected:
    BoolVar d_bvar;
    InfNumeral d_k;
    unsigned d_atomKind : 2;
    /** cache: true if the atom was assigned to true */
    unsigned d_isTrue : 1;
  };

  class EqBound : public Bound
  {
   public:
    EqBound(
        TheoryVar v, const InfNumeral& val, BoundKind k, ENode* lhs, ENode* rhs)
        : Bound(v, val, k, false), d_lhs(lhs), d_rhs(rhs)
    {
      Assert(d_lhs->getRoot() == d_rhs->getRoot());
    }
    bool hasJustification() const override { return true; }
    void pushJustification(Antecedents& a,
                           const Numeral& coeff,
                           bool proofsEnabled) override
    {
      Assert(d_lhs->getRoot() == d_rhs->getRoot());
      a.pushEq(ENodePair(d_lhs, d_rhs), coeff, proofsEnabled);
    }
    std::ostream& print(const TheoryArith& th,
                        std::ostream& out) const override;

   private:
    ENode* d_lhs;
    ENode* d_rhs;
  };

  class DerivedBound : public Bound
  {
   public:
    DerivedBound(TheoryVar v, const InfNumeral& val, BoundKind k)
        : Bound(v, val, k, false)
    {
    }
    const LiteralVector& lits() const { return d_lits; }
    const EqVector& eqs() const { return d_eqs; }
    bool hasJustification() const override { return true; }
    void pushJustification(Antecedents& a,
                           const Numeral& coeff,
                           bool proofsEnabled) override;
    virtual void pushLit(Literal l, const Numeral&) { d_lits.push_back(l); }
    virtual void pushEq(const ENodePair& p, const Numeral&)
    {
      d_eqs.push_back(p);
    }
    std::ostream& print(const TheoryArith& th,
                        std::ostream& out) const override;

   protected:
    LiteralVector d_lits;
    EqVector d_eqs;
    friend class TheoryArith;
  };

  class JustifiedDerivedBound : public DerivedBound
  {
   public:
    JustifiedDerivedBound(TheoryVar v, const InfNumeral& val, BoundKind k)
        : DerivedBound(v, val, k)
    {
    }
    bool hasJustification() const override { return true; }
    void pushJustification(Antecedents& a,
                           const Numeral& coeff,
                           bool proofsEnabled) override;
    void pushLit(Literal l, const Numeral& coeff) override;
    void pushEq(const ENodePair& p, const Numeral& coeff) override;

   private:
    std::vector<Numeral> d_litCoeffs;
    std::vector<Numeral> d_eqCoeffs;
    friend class TheoryArith;
  };

  using LiteralIdxSet = std::unordered_set<int>;
  using EqSet = std::set<ENodePair>;
  LiteralVector d_tmpAccLits;
  EqVector d_tmpAccEqs;
  LiteralIdxSet d_tmpLitSet;
  EqSet d_tmpEqSet;
  void accumulateJustification(Bound& b,
                               DerivedBound& target,
                               const Numeral& coeff,
                               LiteralIdxSet& lits,
                               EqSet& eqs);
  InfNumeral normalizeBound(TheoryVar v, const InfNumeral& k, BoundKind kind);
  void mkBoundFromRow(TheoryVar v,
                      const InfNumeral& coeff,
                      BoundKind k,
                      const Row& r);

  using Atoms = std::vector<Atom*>;
  using BoolVar2Atom = std::vector<Atom*>;

  struct TheoryVarLt
  {
    bool operator()(TheoryVar v1, TheoryVar v2) const { return v1 < v2; }
  };

  using VarHeap = Heap<TheoryVarLt>;

  enum VarKind
  {
    NON_BASE,
    BASE,
    QUASI_BASE
  };

  struct VarData
  {
    /** row owned by the variable, irrelevant if kind() == NON_BASE */
    unsigned d_rowId : 28;
    unsigned d_kind : 2;
    unsigned d_isInt : 1;
    unsigned d_nlPropagated : 1;
    VarData(bool isInt = false)
        : d_rowId(0), d_kind(NON_BASE), d_isInt(isInt), d_nlPropagated(false)
    {
    }
    VarKind kind() const { return static_cast<VarKind>(d_kind); }
  };

  class BoundTrail
  {
   public:
    BoundTrail(TheoryVar v, Bound* b, bool isUpper)
        : d_var(v << 1 | static_cast<int>(isUpper)), d_oldBound(b)
    {
    }
    bool isUpper() const { return (d_var & 1) == 1; }
    TheoryVar getVar() const { return d_var >> 1; }
    Bound* getOldBound() const { return d_oldBound; }

   private:
    TheoryVar d_var;
    Bound* d_oldBound;
  };

  TheoryArithStats d_stats;
  Params& d_params;
  /** applications the solver treats as uninterpreted */
  std::vector<Node> d_underspecifiedOps;
  /** applications the solver does not support */
  std::vector<Node> d_unsupportedOps;
  ArithEqAdapter d_arithEqAdapter;
  std::vector<Row> d_rows;
  std::vector<size_t> d_deadRows;
  /** per var */
  std::vector<Column> d_columns;
  /** per var */
  std::vector<VarData> d_data;
  /** per var, the current assignment for the variable */
  std::vector<InfNumeral> d_value;
  /** per var, the old assignment for the variable */
  std::vector<InfNumeral> d_oldValue;
  /** per var, lower bound & upper bound */
  std::vector<Bound*> d_bounds[2];
  /** per var, atoms that contain a variable */
  std::vector<Atoms> d_varOccs;
  /** per var, the number of unassigned atoms that contain a variable */
  std::vector<size_t> d_unassignedAtoms;
  /** map BoolVar -> atom */
  BoolVar2Atom d_boolVar2Atom;
  /** temporary array used in addRows */
  std::vector<int> d_varPos;
  /** set of theory atoms */
  Atoms d_atoms;
  /** set of asserted bounds */
  std::vector<Bound*> d_assertedBounds;
  size_t d_assertedQhead = 0;
  /** new bound atoms that have yet to be internalized */
  std::vector<Atom*> d_newAtoms;
  /** non linear monomials */
  std::vector<TheoryVar> d_nlMonomials;
  /** non linear monomials that became linear */
  std::vector<TheoryVar> d_nlPropagated;

  /**
   * Variables in a given row. Used during internalization to detect
   * repeated variables.
   */
  std::vector<UIntSet> d_rowVars;
  size_t d_rowVarsTop = 0;

  /** all variables v such that d_value[v] does not satisfy the bounds of v */
  VarHeap d_toPatch;
  /** temporary: variables that already left the basis in makeFeasible */
  NatSet d_leftBasis;
  bool d_blandsRule = false;

  /** temporary trail stack used to restore the last feasible assignment */
  std::vector<size_t> d_updateTrailStack;
  /** the variables in d_updateTrailStack */
  NatSet d_inUpdateTrailStack;

  /** rows that should be checked for theory propagation */
  std::vector<size_t> d_toCheck;
  /** the rows in d_toCheck */
  NatSet d_inToCheck;

  InfNumeral d_tmp;
  RandomGen d_random;
  size_t d_numConflicts = 0;

  size_t d_branchCutCounter = 0;
  /** true if gcd should be applied at every addRow */
  bool d_eagerGcd;
  size_t d_finalCheckIdx = 0;

  // backtracking
  std::vector<BoundTrail> d_boundTrail;
  std::vector<TheoryVar> d_unassignedAtomsTrail;
  std::vector<Bound*> d_boundsToDelete;
  struct Scope
  {
    size_t d_atomsLim;
    size_t d_boundTrailLim;
    size_t d_unassignedAtomsTrailLim;
    size_t d_assertedBoundsLim;
    size_t d_assertedQheadOld;
    size_t d_boundsToDeleteLim;
    size_t d_nlMonomialsLim;
    size_t d_nlPropagatedLim;
  };

  std::vector<Scope> d_scopes;
  LiteralVector d_tmpLiteralVector2;
  AntecedentsT d_antecedents[3];
  size_t d_antecedentsIndex;

  /**
   * int_hashtable<var_value_hash, var_value_eq>: the table assume_eqs uses
   * to find the variables that share a value. Two variables collide when
   * they have the same value and the same sort.
   */
  class VarValueTable
  {
   public:
    VarValueTable(TheoryArith& th) : d_th(th) {}
    void reset() { d_table.clear(); }
    /** The variable of v's value already in the table, or v if none. */
    TheoryVar insertIfNotThere(TheoryVar v);

   private:
    TheoryArith& d_th;
    std::unordered_map<size_t, std::vector<TheoryVar>> d_table;
  };
  friend class VarValueTable;
  VarValueTable d_varValueTable;

  TheoryVar mkVar(ENode* n) override;

  void foundUnsupportedOp(TNode n);
  void foundUnderspecifiedOp(TNode n);

  bool hasVar(TNode v) const;
  TheoryVar expr2var(TNode v) const;
  TNode var2expr(TheoryVar v) const { return getENode(v)->getExpr(); }
  bool reflectionEnabled() const;
  bool reflect(TNode n) const;
  size_t lazyPivotingLvl() const { return d_params.d_arithLazyPivotingLvl; }
  bool propagateEqs() const
  {
    return d_params.d_arithPropagateEqs
           && d_numConflicts < d_params.d_arithPropagationThreshold;
  }
  bool propagateDiseqs() const { return false; }
  bool randomInitialValue() const { return d_params.d_arithRandomInitialValue; }
  int randomLower() const { return d_params.d_arithRandomLower; }
  int randomUpper() const { return d_params.d_arithRandomUpper; }
  size_t blandsRuleThreshold() const
  {
    return d_params.d_arithBlandsRuleThreshold;
  }
  BoundPropMode propagationMode() const
  {
    return d_numConflicts < d_params.d_arithPropagationThreshold
               ? d_params.d_arithBoundProp
               : BP_NONE;
  }
  bool adaptive() const { return d_params.d_arithAdaptive; }
  double adaptiveAssertionThreshold() const
  {
    return d_params.d_arithAdaptiveAssertionThreshold;
  }
  size_t maxLemmaSize() const { return d_params.d_arithMaxLemmaSize; }
  size_t smallLemmaSize() const { return d_params.d_arithSmallLemmaSize; }
  bool relaxBounds() const { return d_params.d_arithStrongerLemmas; }
  bool skipBigCoeffs() const { return d_params.d_arithSkipRowsWithBigCoeffs; }
  bool processAtoms() const;
  size_t getNumConflicts() const { return d_numConflicts; }
  VarKind getVarKind(TheoryVar v) const { return d_data[v].kind(); }
  bool isBase(TheoryVar v) const
  {
    return v != s_nullTheoryVar && getVarKind(v) == BASE;
  }
  bool isQuasiBase(TheoryVar v) const
  {
    return v != s_nullTheoryVar && getVarKind(v) == QUASI_BASE;
  }
  bool isNonBase(TheoryVar v) const
  {
    return v != s_nullTheoryVar && getVarKind(v) == NON_BASE;
  }
  void setVarKind(TheoryVar v, VarKind k) { d_data[v].d_kind = k; }
  size_t getVarRow(TheoryVar v) const
  {
    Assert(!isNonBase(v));
    return d_data[v].d_rowId;
  }
  void setVarRow(TheoryVar v, size_t rId) { d_data[v].d_rowId = rId; }
  std::vector<Node> d_todo;
  bool isIntExpr(TNode e);
  bool isInt(TheoryVar v) const { return d_data[v].d_isInt; }
  bool isIntSrc(TheoryVar v) const;
  bool isReal(TheoryVar v) const { return !isInt(v); }
  bool isRealSrc(TheoryVar v) const { return !isIntSrc(v); }
  bool getImpliedOldValue(TheoryVar v, InfNumeral& r) const;
  const InfNumeral& getImpliedValue(TheoryVar v) const;
  const InfNumeral& getQuasiBaseValue(TheoryVar v) const
  {
    return getImpliedValue(v);
  }
  const InfNumeral& getValue(TheoryVar v) const
  {
    return isQuasiBase(v) ? getQuasiBaseValue(v) : d_value[v];
  }
  Bound* getBound(TheoryVar v, bool upper) const
  {
    return d_bounds[static_cast<size_t>(upper)][v];
  }
  Bound* lower(TheoryVar v) const { return d_bounds[0][v]; }
  Bound* upper(TheoryVar v) const { return d_bounds[1][v]; }
  const InfNumeral& lowerBound(TheoryVar v) const
  {
    Assert(lower(v) != nullptr);
    return lower(v)->getValue();
  }
  const InfNumeral& upperBound(TheoryVar v) const
  {
    Assert(upper(v) != nullptr);
    return upper(v)->getValue();
  }
  bool belowLower(TheoryVar v) const
  {
    Bound* l = lower(v);
    return l != nullptr && getValue(v) < l->getValue();
  }
  bool aboveUpper(TheoryVar v) const
  {
    Bound* u = upper(v);
    return u != nullptr && getValue(v) > u->getValue();
  }
  bool belowUpper(TheoryVar v) const
  {
    Bound* u = upper(v);
    return u == nullptr || getValue(v) < u->getValue();
  }
  bool aboveLower(TheoryVar v) const
  {
    Bound* l = lower(v);
    return l == nullptr || getValue(v) > l->getValue();
  }
  bool atBound(TheoryVar v) const;
  bool atLower(TheoryVar v) const
  {
    Bound* l = lower(v);
    return l != nullptr && getValue(v) == l->getValue();
  }
  bool atUpper(TheoryVar v) const
  {
    Bound* u = upper(v);
    return u != nullptr && getValue(v) == u->getValue();
  }
  bool isFree(TheoryVar v) const
  {
    return lower(v) == nullptr && upper(v) == nullptr;
  }
  bool isNonFree(TheoryVar v) const
  {
    return lower(v) != nullptr || upper(v) != nullptr;
  }
  bool isBounded(TheoryVar v) const
  {
    return lower(v) != nullptr && upper(v) != nullptr;
  }
  bool isFree(TNode n) const;
  bool isFixed(TheoryVar v) const;
  void setBoundCore(TheoryVar v, Bound* newBound, bool upper)
  {
    d_bounds[static_cast<size_t>(upper)][v] = newBound;
  }
  void restoreBound(TheoryVar v, Bound* newBound, bool upper)
  {
    setBoundCore(v, newBound, upper);
  }
  void restoreNlPropagatedFlag(size_t oldTrailSize);
  void setBound(Bound* newBound, bool upper);
  const InfNumeral& getEpsilon(TheoryVar v) const
  {
    return isReal(v) ? d_realEpsilon : d_intEpsilon;
  }
  bool enableCgcFor(TNode n) const;
  ENode* mkENode(TNode n);
  void mkENodeIfReflect(TNode n);
  template <bool invert>
  void addRowEntry(size_t rId, const Numeral& coeff, TheoryVar v);
  UIntSet& rowVars();
  class ScopedRowVars;

  void checkApp(TNode e, TNode n);
  void internalizeInternalMonomial(TNode m, size_t rId);
  TheoryVar internalizeAdd(TNode n);
  TheoryVar internalizeSub(TNode n);
  TheoryVar internalizeMulCore(TNode m);
  TheoryVar internalizeMul(TNode m);
  TheoryVar internalizeDiv(TNode n);
  TheoryVar mkBinaryOp(TNode n);
  TheoryVar internalizeIdiv(TNode n);
  TheoryVar internalizeMod(TNode n);
  TheoryVar internalizeRem(TNode n);
  TheoryVar internalizeToReal(TNode n);
  TheoryVar internalizeToInt(TNode n);
  void internalizeIsInt(TNode n);
  TheoryVar internalizeNumeral(TNode n);
  TheoryVar internalizeNumeral(TNode n, const Numeral& val);
  TheoryVar internalizeTermCore(TNode n);
  void mkAxiom(TNode n1, TNode n2, bool simplifyConseq = true);
  void mkIdivModAxioms(TNode dividend, TNode divisor);
  void mkDivAxiom(TNode dividend, TNode divisor);
  void mkRemAxiom(TNode dividend, TNode divisor);
  void mkToIntAxiom(TNode toInt);
  void mkIsIntAxiom(TNode isInt);
  /**
   * Not from Z3: the value cvc5's total division operators take at a zero
   * divisor, which Z3's partial ones leave unconstrained.
   */
  void mkTotalDivZeroAxiom(TNode n);

  size_t mkRow();
  void initRow(size_t rId);
  void collectVars(size_t rId, VarKind k, std::vector<LinearMonomial>& result);
  void normalizeQuasiBaseRow(size_t rId);
  void quasiBaseRow2BaseRow(size_t rId);
  void normalizeBaseRow(size_t rId);
  void mkClause(Literal l1, Literal l2);
  void mkClause(Literal l1, Literal l2, Literal l3);
  void mkBoundAxioms(Atom* a);
  void mkBoundAxiom(Atom* a1, Atom* a2);
  void flushBoundAxioms();
  Atoms::iterator nextSup(Atom* a1,
                          AtomKind kind,
                          Atoms::iterator it,
                          Atoms::iterator end,
                          bool& foundCompatible);
  Atoms::iterator nextInf(Atom* a1,
                          AtomKind kind,
                          Atoms::iterator it,
                          Atoms::iterator end,
                          bool& foundCompatible);
  Atoms::iterator first(AtomKind kind, Atoms::iterator it, Atoms::iterator end);
  struct CompareAtoms
  {
    bool operator()(Atom* a1, Atom* a2) const
    {
      return a1->getK() < a2->getK();
    }
  };
  bool defaultInternalizer() const override { return false; }
  bool internalizeAtom(TNode n, bool gateCtx) override;
  bool internalizeTerm(TNode term) override;
  void internalizeEqEh(TNode atom, BoolVar v) override;
  void applySortCnstr(ENode* n, const TypeNode& s) override;

  void assignEh(BoolVar v, bool isTrue) override;
  void newEqEh(TheoryVar v1, TheoryVar v2) override;
  bool useDiseqs() const override;
  void newDiseqEh(TheoryVar v1, TheoryVar v2) override;

  void pushScopeEh() override;
  void popScopeEh(size_t numScopes) override;

  void relevantEh(TNode n) override;

  void restartEh() override;
  void initSearchEh() override;
  /**
   * True if the assignment may be changed during final check. assumeEqs,
   * checkIntFeasibility and processNonLinear may change the current
   * assignment to satisfy their respective constraints, and when they do that
   * they may create inconsistencies in the other modules. This flag avoids
   * infinite loops where the modules keep changing the assignment and no
   * progress is made; when it is false, these modules avoid mutating the
   * assignment to satisfy constraints. See also d_changedAssignment.
   */
  bool d_liberalFinalCheck = true;
  FinalCheckStatus finalCheckCore();
  FinalCheckStatus finalCheckEh(size_t level) override;

  bool canPropagate() override;
  void propagate() override;
  bool propagateCore();
  void failed();

  void flushEh() override;
  void resetEh() override;

  // ------------------------------------------------ bool var -> atom mapping
  void insertBv2a(BoolVar bv, Atom* a)
  {
    if (bv >= d_boolVar2Atom.size())
    {
      d_boolVar2Atom.resize(bv + 1, nullptr);
    }
    d_boolVar2Atom[bv] = a;
  }
  void eraseBv2a(BoolVar bv) { d_boolVar2Atom[bv] = nullptr; }
  Atom* getBv2a(BoolVar bv)
  {
    return bv < d_boolVar2Atom.size() ? d_boolVar2Atom[bv] : nullptr;
  }

  // ------------------------------------------------ add row
  void addRow(size_t r1, const Numeral& coeff, size_t r2, bool applyGcdTest);
  void addRows(size_t r1, size_t sz, LinearMonomial* aXs);

  // ------------------------------------------------ assignment management
  /** set to true when the assignment is changed */
  bool d_changedAssignment = false;
  void saveValue(TheoryVar v);
  void discardUpdateTrail();
  void restoreAssignment();
  void updateValueCore(TheoryVar v, const InfNumeral& delta);
  void updateValue(TheoryVar v, const InfNumeral& delta);
  void setValue(TheoryVar v, const InfNumeral& newVal)
  {
    updateValue(v, newVal - d_value[v]);
  }

  // ------------------------------------------------ pivoting
  template <bool Lazy>
  void pivot(TheoryVar xI, TheoryVar xJ, const Numeral& aIJ, bool applyGcdTest);
  template <bool Lazy>
  void eliminate(TheoryVar xI, bool applyGcdTest);
  void updateAndPivot(TheoryVar xI,
                      TheoryVar xJ,
                      const Numeral& aIJ,
                      const InfNumeral& xINewVal);
  int getNumNonFreeDepVars(TheoryVar v, int bestSoFar);
  TheoryVar selectBlandsPivotCore(TheoryVar xI, bool isBelow, Numeral& outAIJ);
  template <bool isBelow>
  TheoryVar selectPivotCore(TheoryVar xI, Numeral& outAIJ);
  TheoryVar selectPivot(TheoryVar xI, bool isBelow, Numeral& outAIJ);

  // ------------------------------------------------ make feasible
  bool makeVarFeasible(TheoryVar xI);
  TheoryVar selectVarToFix();
  TheoryVar selectLgErrorVar(bool least);
  TheoryVar selectGreatestErrorVar() { return selectLgErrorVar(false); }
  TheoryVar selectLeastErrorVar() { return selectLgErrorVar(true); }
  TheoryVar selectSmallestVar();
  bool makeFeasible();
  void signRowConflict(TheoryVar xI, bool isBelow);

  // ------------------------------------------------ assert bound
  bool assertLower(Bound* b);
  bool assertUpper(Bound* b);
  bool assertBound(Bound* b);
  void signBoundConflict(Bound* b1, Bound* b2);

  // ------------------------------------------------ bound propagation
  void markRowForBoundProp(size_t r1);
  void addColumnRowsToTouchedRows(TheoryVar v);
  void isRowUsefulForBoundProp(const Row& r,
                               int& lowerIdx,
                               int& upperIdx) const;
  size_t implyBoundForMonomial(const Row& r, int idx, bool lower);
  size_t implyBoundForAllMonomials(const Row& r, bool lower);
  void explainBound(const Row& r,
                    int idx,
                    bool lower,
                    InfNumeral& delta,
                    Antecedents& antecedents);
  size_t mkImpliedBound(const Row& r,
                        size_t idx,
                        bool lower,
                        TheoryVar v,
                        BoundKind kind,
                        const InfNumeral& k);
  void assignBoundLiteral(
      Literal l, const Row& r, size_t idx, bool lower, InfNumeral& delta);
  void propagateBounds();

  // ------------------------------------------------ freedom intervals
  bool getFreedomInterval(TheoryVar xJ,
                          bool& infL,
                          InfNumeral& l,
                          bool& infU,
                          InfNumeral& u,
                          Numeral& m);

  // ------------------------------------------------ implied eqs
  bool tryToImplyEq(TheoryVar v1, TheoryVar v2);

  // ------------------------------------------------ assume eqs
  using VarSet = std::unordered_set<int>;
  VarSet d_tmpVarSet;
  VarSet d_tmpVarSet2;
  std::vector<std::pair<TheoryVar, TheoryVar>> d_assumeEqCandidates;
  size_t d_assumeEqHead = 0;
  bool randomUpdate(TheoryVar v);
  void mutateAssignment();
  bool assumeEqs();
  bool delayedAssumeEqs();

  // ------------------------------------------------ integrality
  void moveNonBaseVarsToBounds();
  bool hasInfeasibleIntVar();
  TheoryVar findInfeasibleIntBaseVar();
  TheoryVar findBoundedInfeasibleIntBaseVar();
  void branchInfeasibleIntVar(TheoryVar v);
  bool branchInfeasibleIntEquality();
  bool constrainFreeVars(const Row& r);
  bool isGomoryCutTarget(const Row& r);
  bool mkGomoryCut(const Row& r);
  bool gcdTest(const Row& r);
  bool extGcdTest(const Row& r,
                  const Numeral& leastCoeff,
                  const Numeral& lcmDen,
                  const Numeral& consts);
  bool gcdTest();
  Node mkPolynomialGe(size_t numArgs, const RowEntry* args, const Rational& k);
  bool maxMinInfeasibleIntVars();
  void patchIntInfeasibleVars();
  void fixNonBaseVars();
  FinalCheckStatus checkIntFeasibility();

  // ------------------------------------------------ eq propagation
  using ValueSortPair = std::pair<Numeral, bool>;
  std::map<ValueSortPair, TheoryVar> d_fixedVarTable;

  using VarOffset = std::pair<TheoryVar, Numeral>;
  std::map<VarOffset, int> d_varOffset2RowId;

  bool isEqual(TheoryVar x, TheoryVar y) const
  {
    return getENode(x)->getRoot() == getENode(y)->getRoot();
  }
  void fixedVarEh(TheoryVar v);
  bool isOffsetRow(const Row& r, TheoryVar& x, TheoryVar& y, Numeral& k) const;
  void propagateCheapEq(size_t rid);
  void propagateEqToCore(TheoryVar x, TheoryVar y, Antecedents& antecedents);

  bool isShared(TheoryVar v) const override;

  // ------------------------------------------------ justification
  void setConflict(size_t numLiterals,
                   const Literal* lits,
                   size_t numEqs,
                   const ENodePair* eqs,
                   Antecedents& antecedents,
                   const char* proofRule);
  void setConflict(const Antecedents& ante,
                   Antecedents& bounds,
                   const char* proofRule);
  void setConflict(const DerivedBound& ante,
                   Antecedents& bounds,
                   const char* proofRule);
  void collectFixedVarJustifications(const Row& r,
                                     Antecedents& antecedents) const;

  // ------------------------------------------------ backtracking
  void pushBoundTrail(TheoryVar v, Bound* oldBound, bool isUpper)
  {
    d_boundTrail.push_back(BoundTrail(v, oldBound, isUpper));
  }
  void pushDecUnassignedAtomsTrail(TheoryVar v)
  {
    d_unassignedAtomsTrail.push_back(v);
  }
  void restoreBounds(size_t oldTrailSize);
  void restoreUnassignedAtoms(size_t oldTrailSize);
  void delAtoms(size_t oldSize);
  void delBounds(size_t oldSize);
  void delVars(size_t oldNumVars);
  void delRow(size_t rId);

  // ------------------------------------------------ auxiliary methods
  const ColEntry* getABaseRowThatContains(TheoryVar v);
  bool allCoeffInt(const Row& r) const;
  const ColEntry* getRowForEliminating(TheoryVar v) const;
  void moveUnconstrainedToBase();
  void elimQuasiBaseRows();
  void removeFixedVarsFromBase();
  void tryToMinimizeRationalCoeffs();

  /** See the comment at Theory::mkEqAtom. */
  Node mkEqAtom(TNode lhs, TNode rhs) override;

  // ------------------------------------------------ maximization/minimization
  Row d_tmpRow;

  void addTmpRow(Row& r1, const Numeral& coeff, const Row& r2);
  bool isSafeToLeave(TheoryVar x, bool inc, bool& hasInt, bool& isShared);
  template <bool invert>
  void addTmpRowEntry(Row& r, const Numeral& coeff, TheoryVar v);
  enum MaxMinT
  {
    UNBOUNDED,
    AT_BOUND,
    OPTIMIZED,
    BEST_EFFORT
  };
  MaxMinT maxMin(TheoryVar v,
                 bool max,
                 bool maintainIntegrality,
                 bool& hasShared);
  bool hasInterfaceEquality(TheoryVar v);
  bool maxMin(const std::vector<TheoryVar>& vars);

  MaxMinT maxMin(Row& r, bool max, bool maintainIntegrality, bool& hasShared);
  bool unboundedGain(const InfNumeral& maxGain) const;
  bool safeGain(const InfNumeral& minGain, const InfNumeral& maxGain) const;
  void normalizeGain(const Numeral& divisor, InfNumeral& maxGain) const;
  void initGains(TheoryVar x,
                 bool inc,
                 InfNumeral& minGain,
                 InfNumeral& maxGain);
  bool updateGains(bool inc,
                   TheoryVar xI,
                   const Numeral& aIJ,
                   InfNumeral& minGain,
                   InfNumeral& maxGain);
  bool moveToBound(TheoryVar xI,
                   bool inc,
                   size_t& bestEfforts,
                   bool& hasShared);
  bool pickVarToLeave(TheoryVar xJ,
                      bool inc,
                      Numeral& aIJ,
                      InfNumeral& minGain,
                      InfNumeral& maxGain,
                      bool& shared,
                      TheoryVar& xI);

  // ------------------------------------------------ non linear
  bool d_modelDependsOnComputedEpsilon = false;
  size_t d_nlRounds = 0;

  /** A monomial is 'pure' if it does not have a numeric coefficient. */
  bool isPureMonomial(TNode m) const;
  bool isPureMonomial(TheoryVar v) const
  {
    return isPureMonomial(getENode(v)->getExpr());
  }
  Numeral getValue(TheoryVar v, bool& computedEpsilon);
  bool checkMonomialAssignment(TheoryVar v, bool& computedEpsilon);
  bool checkMonomialAssignments();
  bool isMonomialLinear(TNode m) const;
  Numeral getMonomialFixedVarProduct(TNode m) const;
  TNode getMonomialNonFixedVar(TNode m) const;
  bool propagateLinearMonomial(TheoryVar v);
  bool propagateLinearMonomials();
  FinalCheckStatus processNonLinear();

  // ------------------------------------------------ model generation
  Numeral d_epsilon;
  void updateEpsilon(const InfNumeral& l, const InfNumeral& u);
  void computeEpsilon();
  void refineEpsilon();

  // ------------------------------------------------ pretty printing
  void printRow(std::ostream& out, size_t rId, bool compact = true) const;
  void printRow(std::ostream& out, const Row& r, bool compact = true) const;
  void printRows(std::ostream& out, bool compact = true) const;
  void printVar(std::ostream& out, TheoryVar v) const;
  void printVars(std::ostream& out) const;
  void printBound(std::ostream& out, Bound* b, size_t indent = 0) const;
  void printAtoms(std::ostream& out) const;
  void printAtom(std::ostream& out, Atom* a, bool showSign) const;

  friend class Antecedents;

 protected:
  // Declarations each part of the port adds, kept in a file of its own.
#include "z3/theory_arith_aux_decls.inc"
#include "z3/theory_arith_core_decls.inc"
#include "z3/theory_arith_eqint_decls.inc"
#include "z3/theory_arith_nlpp_decls.inc"
};

}  // namespace z3
}  // namespace cvc5::internal

#endif /* CVC5__Z3__THEORY_ARITH_H */

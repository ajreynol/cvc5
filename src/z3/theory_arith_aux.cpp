/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The simplex-based arithmetic solver of the ported Z3 core: rows, columns,
 * bounds, auxiliary tableau operations, maximization/minimization, freedom
 * intervals and assume eqs.
 *
 * Ported from Z3 (MIT License, Copyright (c) Microsoft Corporation), file
 * src/smt/theory_arith_aux.h, and recast in cvc5 style. The theory_opt parts
 * (maximize, objectives, conflict recording) are not ported.
 */

#include <utility>

#include "z3/arith_util.h"
#include "z3/smt_context.h"
#include "z3/theory_arith.h"
#include "z3/util/trail.h"

namespace cvc5::internal {
namespace z3 {

// -----------------------------------
//
// Rows
//
// -----------------------------------

TheoryArith::Row::Row()
    : d_size(0), d_baseVar(s_nullTheoryVar), d_firstFreeIdx(-1)
{
}

void TheoryArith::Row::reset()
{
  d_entries.clear();
  d_size = 0;
  d_baseVar = -1;
  d_firstFreeIdx = -1;
}

/**
 * Add a new RowEntry. The result is a reference to the new RowEntry. The
 * position of the new RowEntry in the row is stored in posIdx.
 */
TheoryArith::RowEntry& TheoryArith::Row::addRowEntry(int& posIdx)
{
  d_size++;
  if (d_firstFreeIdx == -1)
  {
    posIdx = static_cast<int>(d_entries.size());
    d_entries.push_back(RowEntry());
    return d_entries.back();
  }
  else
  {
    posIdx = d_firstFreeIdx;
    RowEntry& result = d_entries[posIdx];
    Assert(result.isDead());
    d_firstFreeIdx = result.d_nextFreeRowEntryIdx;
    return result;
  }
}

/** Delete the RowEntry at position idx. */
void TheoryArith::Row::delRowEntry(size_t idx)
{
  RowEntry& t = d_entries[idx];
  Assert(!t.isDead());
  // Z3's behaviour: d_firstFreeIdx is not updated, so dead entries of a row
  // are not reused until the row is compressed.
  t.d_nextFreeRowEntryIdx = d_firstFreeIdx;
  t.d_var = s_nullTheoryVar;
  d_size--;
  Assert(t.isDead());
}

/** Remove holes (i.e., dead entries) from the row. */
void TheoryArith::Row::compress(std::vector<Column>& cols)
{
  size_t i = 0;
  size_t j = 0;
  size_t sz = d_entries.size();
  for (; i < sz; ++i)
  {
    RowEntry& t1 = d_entries[i];
    if (!t1.isDead())
    {
      if (i != j)
      {
        RowEntry& t2 = d_entries[j];
        std::swap(t2.d_coeff, t1.d_coeff);
        t2.d_var = t1.d_var;
        t2.d_colIdx = t1.d_colIdx;
        Assert(!t2.isDead());
        Column& col = cols[t2.d_var];
        col[t2.d_colIdx].d_rowIdx = static_cast<int>(j);
      }
      j++;
    }
  }
  Assert(j == d_size);
  d_entries.resize(d_size);
  d_firstFreeIdx = -1;
}

/** Invoke compress if the row contains too many holes (i.e., dead entries). */
void TheoryArith::Row::compressIfNeeded(std::vector<Column>& cols)
{
  if (size() * 2 < numEntries())
  {
    compress(cols);
  }
}

/** Fill the map var -> pos/idx */
void TheoryArith::Row::saveVarPos(std::vector<int>& resultMap) const
{
  int idx = 0;
  for (const RowEntry& e : d_entries)
  {
    if (!e.isDead())
    {
      resultMap[e.d_var] = idx;
    }
    ++idx;
  }
}

/**
 * Reset the map var -> pos/idx. That is for all variables v in the row, set
 * result[v] = -1. This method can be viewed as the "inverse" of saveVarPos.
 */
void TheoryArith::Row::resetVarPos(std::vector<int>& resultMap) const
{
  for (const RowEntry& e : d_entries)
  {
    if (!e.isDead())
    {
      resultMap[e.d_var] = -1;
    }
  }
}

void TheoryArith::Row::print(std::ostream& out) const
{
  out << "v" << d_baseVar << ", ";
  for (const RowEntry& e : d_entries)
  {
    if (!e.isDead())
    {
      out << e.d_coeff << "*v" << e.d_var << " ";
    }
  }
  out << "\n";
}

TheoryArith::Numeral TheoryArith::Row::getDenominatorsLcm() const
{
  Numeral r(1);
  for (const RowEntry& e : d_entries)
  {
    if (!e.isDead())
    {
      r = lcm(r, denominator(e.d_coeff));
    }
  }
  return r;
}

int TheoryArith::Row::getIdxOf(TheoryVar v) const
{
  int idx = 0;
  for (const RowEntry& e : d_entries)
  {
    if (!e.isDead() && e.d_var == v)
    {
      return idx;
    }
    ++idx;
  }
  return -1;
}

// -----------------------------------
//
// Columns
//
// -----------------------------------

void TheoryArith::Column::reset()
{
  d_entries.clear();
  d_size = 0;
  d_firstFreeIdx = -1;
}

/** Remove holes (i.e., dead entries) from the column. */
void TheoryArith::Column::compress(std::vector<Row>& rows)
{
  size_t i = 0;
  size_t j = 0;
  size_t sz = d_entries.size();
  for (; i < sz; ++i)
  {
    ColEntry& e1 = d_entries[i];
    if (!e1.isDead())
    {
      if (i != j)
      {
        d_entries[j] = e1;
        Row& r = rows[e1.d_rowId];
        r[e1.d_rowIdx].d_colIdx = static_cast<int>(j);
      }
      j++;
    }
  }
  Assert(j == d_size);
  d_entries.resize(d_size);
  d_firstFreeIdx = -1;
}

/**
 * Invoke compress if the column contains too many holes (i.e., dead entries).
 */
void TheoryArith::Column::compressIfNeeded(std::vector<Row>& rows)
{
  if (size() * 2 < numEntries())
  {
    compress(rows);
  }
}

/**
 * Special version of compress, that is used when the column contains only
 * one entry located at position singletonPos.
 */
void TheoryArith::Column::compressSingleton(std::vector<Row>& rows,
                                            size_t singletonPos)
{
  Assert(d_size == 1);
  if (singletonPos != 0)
  {
    ColEntry& s = d_entries[singletonPos];
    d_entries[0] = s;
    Row& r = rows[s.d_rowId];
    r[s.d_rowIdx].d_colIdx = 0;
  }
  d_firstFreeIdx = -1;
  d_entries.resize(1);
}

const TheoryArith::ColEntry* TheoryArith::Column::getFirstColEntry() const
{
  for (const ColEntry& e : d_entries)
  {
    if (!e.isDead())
    {
      return &e;
    }
  }
  return nullptr;
}

TheoryArith::ColEntry& TheoryArith::Column::addColEntry(int& posIdx)
{
  d_size++;
  if (d_firstFreeIdx == -1)
  {
    posIdx = static_cast<int>(d_entries.size());
    d_entries.push_back(ColEntry());
    return d_entries.back();
  }
  else
  {
    posIdx = d_firstFreeIdx;
    ColEntry& result = d_entries[posIdx];
    Assert(result.isDead());
    d_firstFreeIdx = result.d_nextFreeRowEntryIdx;
    return result;
  }
}

void TheoryArith::Column::delColEntry(size_t idx)
{
  ColEntry& c = d_entries[idx];
  Assert(!c.isDead());
  c.d_rowId = s_deadRowId;
  c.d_nextFreeRowEntryIdx = d_firstFreeIdx;
  d_firstFreeIdx = static_cast<int>(idx);
  d_size--;
}

// -----------------------------------
//
// Antecedents
//
// -----------------------------------

// Z3's antecedents::antecedents / ~antecedents (theory_arith_core.h).
TheoryArith::Antecedents::Antecedents(TheoryArith& th)
    : d_th(th), d_a(th.d_antecedents[th.d_antecedentsIndex])
{
  Assert(th.d_antecedentsIndex < 3);
  d_a.reset();
  ++th.d_antecedentsIndex;
}

TheoryArith::Antecedents::~Antecedents() { --d_th.d_antecedentsIndex; }

// -----------------------------------
//
// Bounds
//
// -----------------------------------

std::ostream& TheoryArith::Bound::print(const TheoryArith& th,
                                        std::ostream& out) const
{
  return out << "v" << getVar() << " "
             << (getBoundKind() == B_LOWER ? ">=" : "<=") << " " << getValue();
}

// -----------------------------------
//
// Atoms
//
// -----------------------------------

TheoryArith::Atom::Atom(BoolVar bv,
                        TheoryVar v,
                        const InfNumeral& k,
                        AtomKind kind)
    : Bound(v, InfNumeral(), B_LOWER, true),
      d_bvar(bv),
      d_k(k),
      d_atomKind(kind),
      d_isTrue(false)
{
}

void TheoryArith::Atom::assignEh(bool isTrue, const InfNumeral& epsilon)
{
  d_isTrue = isTrue;
  if (isTrue)
  {
    d_value = d_k;
    d_boundKind = static_cast<BoundKind>(d_atomKind);
    Assert((d_boundKind == B_LOWER) == (d_atomKind == A_LOWER));
  }
  else
  {
    if (getAtomKind() == A_LOWER)
    {
      d_value = d_k;
      d_value -= epsilon;
      d_boundKind = B_UPPER;
    }
    else
    {
      Assert(getAtomKind() == A_UPPER);
      d_value = d_k;
      d_value += epsilon;
      d_boundKind = B_LOWER;
    }
  }
}

std::ostream& TheoryArith::Atom::print(const TheoryArith& th,
                                       std::ostream& out) const
{
  Literal l(getBoolVar(), !d_isTrue);
  th.d_ctx.printLiteral(out, l);
  return out;
}

// -----------------------------------
//
// EqBound
//
// -----------------------------------

std::ostream& TheoryArith::EqBound::print(const TheoryArith& th,
                                          std::ostream& out) const
{
  return out << "#" << d_lhs->getOwnerId() << " " << d_lhs->getExpr() << " = "
             << "#" << d_rhs->getOwnerId() << " " << d_rhs->getExpr();
}

// -----------------------------------
//
// Auxiliary methods
//
// -----------------------------------

bool TheoryArith::atBound(TheoryVar v) const
{
  Bound* l = lower(v);
  if (l != nullptr && getValue(v) == l->getValue())
  {
    return true;
  }
  Bound* u = upper(v);
  return u != nullptr && getValue(v) == u->getValue();
}

bool TheoryArith::isFixed(TheoryVar v) const
{
  Bound* l = lower(v);
  if (l == nullptr)
  {
    return false;
  }
  Bound* u = upper(v);
  if (u == nullptr)
  {
    return false;
  }
  return l->getValue() == u->getValue();
}

void TheoryArith::setBound(Bound* newBound, bool upper)
{
  Assert(newBound);
  Assert(!upper || newBound->getBoundKind() == B_UPPER);
  Assert(upper || newBound->getBoundKind() == B_LOWER);
  TheoryVar v = newBound->getVar();
  setBoundCore(v, newBound, upper);
  if ((propagateEqs() || propagateDiseqs()) && isFixed(v))
  {
    fixedVarEh(v);
  }
}

/**
 * Return the ColEntry that points to a base row that contains the given
 * variable. Return nullptr if no row contains v.
 */
const TheoryArith::ColEntry* TheoryArith::getABaseRowThatContains(TheoryVar v)
{
  while (true)
  {
    const Column& c = d_columns[v];
    if (c.size() == 0)
    {
      return nullptr;
    }
    int quasiBaseRid = -1;
    for (const ColEntry& e : c)
    {
      if (!e.isDead())
      {
        size_t rid = e.d_rowId;
        Row& r = d_rows[rid];
        TheoryVar s = r.getBaseVar();
        if (s == s_nullTheoryVar)
        {
          // skip
        }
        else if (isBase(s))
        {
          return &e;
        }
        else if (quasiBaseRid == -1)
        {
          quasiBaseRid = static_cast<int>(rid);
        }
      }
    }
    if (quasiBaseRid == -1)
    {
      return nullptr;
    }

    quasiBaseRow2BaseRow(quasiBaseRid);
    // There is no guarantee that v is still a variable of row quasiBaseRid.

    // However, this loop will always terminate since we are creating a base
    // row that contains v, or decreasing c.size().
  }
}

/** Return true if all coefficients of the given row are int. */
bool TheoryArith::allCoeffInt(const Row& r) const
{
  for (const RowEntry& e : r)
  {
    if (!e.isDead() && !z3::isInt(e.d_coeff))
    {
      return false;
    }
  }
  return true;
}

/**
 * Return the ColEntry that points to a row that contains the given variable.
 * This row should not be owned by an unconstrained quasi-base variable.
 * Return nullptr if failed.
 *
 * This method is used by moveUnconstrainedToBase.
 */
const TheoryArith::ColEntry* TheoryArith::getRowForEliminating(
    TheoryVar v) const
{
  const Column& c = d_columns[v];
  if (c.size() == 0)
  {
    return nullptr;
  }
  for (const ColEntry& e : c)
  {
    if (!e.isDead())
    {
      const Row& r = d_rows[e.d_rowId];
      TheoryVar s = r.getBaseVar();
      if (isQuasiBase(s) && d_varOccs[s].empty())
      {
        continue;
      }
      if (isInt(v))
      {
        const Numeral& coeff = r[e.d_rowIdx].d_coeff;
        // If coeff == 1 or coeff == -1, and all other coefficients of r are
        // integer, then if we pivot v with the base var of r, we will produce
        // a row that will guarantee an integer assignment for v, when the
        // non-base vars have integer assignment.
        if (!coeff.isOne() && !isMinusOne(coeff))
        {
          continue;
        }
        if (!allCoeffInt(r))
        {
          continue;
        }
      }
      return &e;
    }
  }
  return nullptr;
}

void TheoryArith::moveUnconstrainedToBase()
{
  if (lazyPivotingLvl() == 0)
  {
    return;
  }
  int num = static_cast<int>(getNumVars());
  for (TheoryVar v = 0; v < num; ++v)
  {
    if (d_varOccs[v].empty() && isFree(v))
    {
      switch (getVarKind(v))
      {
        case QUASI_BASE: break;
        case BASE:
          if (isInt(v) && !allCoeffInt(d_rows[getVarRow(v)]))
          {
            // If the row contains non integer coefficients, then v may be
            // assigned to a non-integer value even if all non-base variables
            // are integer. So, v should not be "eliminated".
            break;
          }
          eliminate<false>(v, d_eagerGcd);
          break;
        case NON_BASE:
        {
          const ColEntry* entry = getRowForEliminating(v);
          if (entry)
          {
            Row& r = d_rows[entry->d_rowId];
            Assert(r[entry->d_rowIdx].d_var == v);
            pivot<false>(
                r.getBaseVar(), v, r[entry->d_rowIdx].d_coeff, d_eagerGcd);
            Assert(isBase(v));
            setVarKind(v, QUASI_BASE);
            Assert(isQuasiBase(v));
          }
          break;
        }
      }
    }
  }
}

/** Force all quasi_base rows to become base rows. */
void TheoryArith::elimQuasiBaseRows()
{
  int num = static_cast<int>(getNumVars());
  for (TheoryVar v = 0; v < num; ++v)
  {
    if (isQuasiBase(v))
    {
      quasiBaseRow2BaseRow(getVarRow(v));
    }
  }
}

/** Remove fixed vars from the base. */
void TheoryArith::removeFixedVarsFromBase()
{
  int num = static_cast<int>(getNumVars());
  for (TheoryVar v = 0; v < num; ++v)
  {
    if (isBase(v) && isFixed(v))
    {
      const Row& r = d_rows[getVarRow(v)];
      std::vector<RowEntry>::const_iterator it = r.begin();
      std::vector<RowEntry>::const_iterator end = r.end();
      for (; it != end; ++it)
      {
        if (!it->isDead() && it->d_var != v && !isFixed(it->d_var))
        {
          break;
        }
      }
      if (it != end)
      {
        pivot<true>(v, it->d_var, it->d_coeff, false);
      }
    }
  }
}

/**
 * Try to minimize the number of rational coefficients. The idea is to pivot
 * x_i and x_j whenever there is a row
 *
 *   x_i + 1/n * x_j + ... = 0
 *
 * where
 * - x_i is a base variable
 * - x_j is a non-base variable
 * - x_j is not a fixed variable
 * - The denominator of any other coefficient a_ik divides n (only the
 *   coefficients of non-fixed variables are considered)
 *
 * If there is more than one variable with such properties, preference is
 * given to free variables, then to variables where upper - lower is maximal.
 */
void TheoryArith::tryToMinimizeRationalCoeffs()
{
  int num = static_cast<int>(getNumVars());
  for (TheoryVar v = 0; v < num; ++v)
  {
    if (!isBase(v) || !isInt(v))
    {
      continue;
    }
    Numeral maxDen;
    const Row& r = d_rows[getVarRow(v)];
    std::vector<RowEntry>::const_iterator it = r.begin();
    std::vector<RowEntry>::const_iterator end = r.end();
    for (; it != end; ++it)
    {
      if (it->isDead())
      {
        continue;
      }
      if (it->d_var == v)
      {
        continue;
      }
      if (isFixed(it->d_var))
      {
        continue;
      }
      Numeral nm = numerator(it->d_coeff);
      if (!nm.isOne() && !isMinusOne(nm))
      {
        continue;
      }
      Numeral den = denominator(it->d_coeff);
      if (den > maxDen)
      {
        maxDen = den;
      }
    }
    if (maxDen <= Numeral(1))
    {
      continue;
    }
    // check whether all a_ik denominators divide maxDen
    it = r.begin();
    for (; it != end; ++it)
    {
      if (it->isDead())
      {
        continue;
      }
      if (isFixed(it->d_var))
      {
        continue;
      }
      Numeral den = denominator(it->d_coeff);
      if (!z3::isInt(maxDen / den))
      {
        break;
      }
    }
    if (it != end)
    {
      continue;
    }
    // pick best candidate
    TheoryVar xJ = s_nullTheoryVar;
    Numeral aIJ;
    it = r.begin();
    for (; it != end; ++it)
    {
      if (it->isDead())
      {
        continue;
      }
      if (it->d_var == v)
      {
        continue;
      }
      if (isFixed(it->d_var))
      {
        continue;
      }
      Numeral nm = numerator(it->d_coeff);
      if (!nm.isOne() && !isMinusOne(nm))
      {
        continue;
      }
      Numeral den = denominator(it->d_coeff);
      if (den != maxDen)
      {
        continue;
      }
      if (xJ == s_nullTheoryVar ||
          // TODO (Z3): add extra cases...
          isFree(it->d_var) || (isBounded(xJ) && !isBounded(it->d_var))
          || (isBounded(xJ) && isBounded(it->d_var)
              && (upperBound(xJ) - lowerBound(xJ)
                  > upperBound(it->d_var) - lowerBound(it->d_var))))
      {
        xJ = it->d_var;
        aIJ = it->d_coeff;
        if (isFree(xJ))
        {
          break;
        }
      }
    }
    if (xJ != s_nullTheoryVar)
    {
      pivot<true>(v, xJ, aIJ, false);
    }
  }
}

// -----------------------------------
//
// Derived bounds
//
// -----------------------------------

void TheoryArith::DerivedBound::pushJustification(Antecedents& a,
                                                  const Numeral& coeff,
                                                  bool proofsEnabled)
{
  if (proofsEnabled)
  {
    for (Literal l : d_lits)
    {
      a.pushLit(l, coeff, proofsEnabled);
    }
    for (const ENodePair& e : d_eqs)
    {
      a.pushEq(e, coeff, proofsEnabled);
    }
  }
  else
  {
    a.append(d_lits.size(), d_lits.data());
    a.append(d_eqs.size(), d_eqs.data());
  }
}

std::ostream& TheoryArith::DerivedBound::print(const TheoryArith& th,
                                               std::ostream& out) const
{
  out << "v" << getVar() << " " << (getBoundKind() == B_LOWER ? ">=" : "<=")
      << " " << getValue() << "\n";
  out << "expr: " << th.var2expr(getVar()) << "\n";

  for (const ENodePair& e : d_eqs)
  {
    ENode* a = e.first;
    ENode* b = e.second;
    out << " ";
    out << "#" << a->getOwnerId() << " " << a->getExpr() << " = "
        << "#" << b->getOwnerId() << " " << b->getExpr() << "\n";
  }
  for (Literal l : d_lits)
  {
    out << l << ":";
    th.d_ctx.printLiteral(out, l) << "\n";
  }
  return out;
}

void TheoryArith::JustifiedDerivedBound::pushJustification(Antecedents& a,
                                                           const Numeral& coeff,
                                                           bool proofsEnabled)
{
  for (size_t i = 0; i < d_lits.size(); ++i)
  {
    a.pushLit(d_lits[i], coeff * d_litCoeffs[i], proofsEnabled);
  }
  for (size_t i = 0; i < d_eqs.size(); ++i)
  {
    a.pushEq(d_eqs[i], coeff * d_eqCoeffs[i], proofsEnabled);
  }
}

void TheoryArith::JustifiedDerivedBound::pushLit(Literal l,
                                                 const Numeral& coeff)
{
  for (size_t i = 0; i < d_lits.size(); ++i)
  {
    if (d_lits[i] == l)
    {
      d_litCoeffs[i] += coeff;
      return;
    }
  }
  d_lits.push_back(l);
  d_litCoeffs.push_back(coeff);
}

void TheoryArith::JustifiedDerivedBound::pushEq(const ENodePair& p,
                                                const Numeral& coeff)
{
  for (size_t i = 0; i < d_eqs.size(); ++i)
  {
    if (d_eqs[i] == p)
    {
      d_eqCoeffs[i] += coeff;
      return;
    }
  }
  d_eqs.push_back(p);
  d_eqCoeffs.push_back(coeff);
}

/**
 * Copy the justification of b to target. Only literals and equalities not in
 * lits and eqs are copied. The justification of b is also copied to lits and
 * eqs.
 */
void TheoryArith::accumulateJustification(Bound& b,
                                          DerivedBound& target,
                                          const Numeral& coeff,
                                          LiteralIdxSet& lits,
                                          EqSet& eqs)
{
  Antecedents ante(*this);
  b.pushJustification(ante, coeff, proofsEnabled());
  size_t numLits = ante.lits().size();
  for (size_t i = 0; i < numLits; ++i)
  {
    Literal l = ante.lits()[i];
    if (lits.find(l.index()) != lits.end())
    {
      continue;
    }
    // proofs are disabled
    target.pushLit(l, Numeral(0));
    lits.insert(l.index());
  }
  size_t numEqs = ante.eqs().size();
  for (size_t i = 0; i < numEqs; ++i)
  {
    const ENodePair& p = ante.eqs()[i];
    if (eqs.find(p) != eqs.end())
    {
      continue;
    }
    // proofs are disabled
    target.pushEq(p, Numeral(0));
    eqs.insert(p);
  }
}

TheoryArith::InfNumeral TheoryArith::normalizeBound(TheoryVar v,
                                                    const InfNumeral& k,
                                                    BoundKind kind)
{
  if (isReal(v))
  {
    return k;
  }
  if (kind == B_LOWER)
  {
    return InfNumeral(ceil(k));
  }
  Assert(kind == B_UPPER);
  return InfNumeral(floor(k));
}

/** Create a derived bound for v using the given row as an explanation. */
void TheoryArith::mkBoundFromRow(TheoryVar v,
                                 const InfNumeral& k,
                                 BoundKind kind,
                                 const Row& r)
{
  InfNumeral kNorm = normalizeBound(v, k, kind);
  // proofs are disabled: Z3 allocates a justified_derived_bound otherwise
  DerivedBound* newBound = new DerivedBound(v, kNorm, kind);
  d_boundsToDelete.push_back(newBound);
  d_assertedBounds.push_back(newBound);
  d_tmpLitSet.clear();
  d_tmpEqSet.clear();
  for (const RowEntry& e : r)
  {
    if (!e.isDead())
    {
      TheoryVar w = e.d_var;
      bool useUpper = (kind == B_UPPER);
      if (!isPos(e.d_coeff))
      {
        useUpper = !useUpper;
      }
      Bound* b = getBound(w, useUpper);
      Assert(b);
      accumulateJustification(
          *b, *newBound, e.d_coeff, d_tmpLitSet, d_tmpEqSet);
    }
  }
}

// -----------------------------------
//
// Maximization/Minimization
//
// -----------------------------------

/**
 * Set: row1 <- row1 + coeff * row2, where row1 is a temporary row.
 *
 * Columns do not need to be updated when updating a temporary row.
 */
void TheoryArith::addTmpRow(Row& r1, const Numeral& coeff, const Row& r2)
{
  r1.saveVarPos(d_varPos);

  //
  // loop over variables in row2,
  // add terms in row2 to row1.
  //
#define ADD_TMP_ROW(_SET_COEFF_, _ADD_COEFF_)      \
  for (const RowEntry& e : r2)                     \
  {                                                \
    if (!e.isDead())                               \
    {                                              \
      TheoryVar v = e.d_var;                       \
      int pos = d_varPos[v];                       \
      if (pos == -1)                               \
      {                                            \
        /* variable v is not in row1 */            \
        int rowIdx;                                \
        RowEntry& rEntry = r1.addRowEntry(rowIdx); \
        rEntry.d_var = v;                          \
        _SET_COEFF_;                               \
      }                                            \
      else                                         \
      {                                            \
        /* variable v is in row1 */                \
        RowEntry& rEntry = r1[pos];                \
        Assert(rEntry.d_var == v);                 \
        _ADD_COEFF_;                               \
        if (rEntry.d_coeff.isZero())               \
        {                                          \
          r1.delRowEntry(pos);                     \
        }                                          \
        d_varPos[v] = -1;                          \
      }                                            \
    }                                              \
  }                                                \
  ((void)0)

  if (coeff.isOne())
  {
    ADD_TMP_ROW(rEntry.d_coeff = e.d_coeff, rEntry.d_coeff += e.d_coeff);
  }
  else if (isMinusOne(coeff))
  {
    ADD_TMP_ROW(rEntry.d_coeff = e.d_coeff;
                rEntry.d_coeff = -rEntry.d_coeff, rEntry.d_coeff -= e.d_coeff);
  }
  else
  {
    ADD_TMP_ROW(rEntry.d_coeff = e.d_coeff;
                rEntry.d_coeff *= coeff, rEntry.d_coeff += e.d_coeff * coeff);
  }
#undef ADD_TMP_ROW

  r1.resetVarPos(d_varPos);
}

bool TheoryArith::isSafeToLeave(TheoryVar x,
                                bool inc,
                                bool& hasInt,
                                bool& shared)
{
  shared |= d_ctx.isShared(getENode(x));
  Column& c = d_columns[x];
  hasInt = false;
  bool unbounded = (inc && !upper(x)) || (!inc && !lower(x));
  bool wasUnsafe = false;
  for (const ColEntry& ce : c)
  {
    if (ce.isDead())
    {
      continue;
    }
    const Row& r = d_rows[ce.d_rowId];
    TheoryVar s = r.getBaseVar();
    const Numeral& coeff = r[ce.d_rowIdx].d_coeff;
    if (s != s_nullTheoryVar && isInt(s))
    {
      hasInt = true;
    }
    bool isUnsafe = (s != s_nullTheoryVar && isInt(s) && !z3::isInt(coeff));
    shared |= (s != s_nullTheoryVar && d_ctx.isShared(getENode(s)));
    wasUnsafe |= isUnsafe;
    bool incS = isNeg(coeff) ? inc : !inc;
    unbounded &= !getBound(s, incS);
    if (wasUnsafe && !unbounded)
    {
      return false;
    }
  }

  return !wasUnsafe || unbounded;
}

/**
 * Select tightest variable x_i to pivot with x_j. The goal is to select a x_i
 * such that the value of x_j is increased (decreased) if inc = true (inc =
 * false), and the tableau remains feasible. Store the gain in x_j of the
 * pivoting operation in 'gain'. Note the gain can be too much. That is, it
 * may make x_i infeasible. In this case, instead of pivoting we move x_j to
 * its upper bound (lower bound) when inc = true (inc = false).
 *
 * If no x_i imposes a restriction on x_j, then return s_nullTheoryVar. That
 * is, x_j is free to move to its upper bound (lower bound).
 *
 * Get the equations for x_j:
 *
 *   x_i1 = coeff_1 * x_j + rest_1
 *   ...
 *   x_in = coeff_n * x_j + rest_n
 *
 *   gain_k := (upper_bound(x_ik) - value(x_ik))/coeff_k
 */
bool TheoryArith::pickVarToLeave(
    TheoryVar xJ,  // non-base variable to increment/decrement
    bool inc,
    Numeral& aIJ,         // coefficient of x_i
    InfNumeral& minGain,  // minimal required gain on x_j (integral value on
                          // integers)
    InfNumeral& maxGain,  // maximal possible gain on x_j
    bool& hasShared,      // determine if pivot involves shared variable
    TheoryVar& xI)        // base variable to pivot with x_j
{
  xI = s_nullTheoryVar;
  initGains(xJ, inc, minGain, maxGain);
  hasShared |= d_ctx.isShared(getENode(xJ));
  if (isInt(xJ) && !getValue(xJ).isInt())
  {
    return false;
  }
  Column& c = d_columns[xJ];
  bool emptyColumn = true;
  for (const ColEntry& ce : c)
  {
    if (ce.isDead())
    {
      continue;
    }
    emptyColumn = false;
    const Row& r = d_rows[ce.d_rowId];
    TheoryVar s = r.getBaseVar();
    const Numeral& coeffIJ = r[ce.d_rowIdx].d_coeff;
    if (updateGains(inc, s, coeffIJ, minGain, maxGain)
        || (xI == s_nullTheoryVar && !unboundedGain(maxGain)))
    {
      xI = s;
      aIJ = coeffIJ;
    }
    hasShared |= d_ctx.isShared(getENode(s));
  }

  (void)emptyColumn;
  Assert(!safeGain(minGain, maxGain) || emptyColumn
         || (unboundedGain(maxGain) == (xI == s_nullTheoryVar)));

  return safeGain(minGain, maxGain);
}

bool TheoryArith::unboundedGain(const InfNumeral& maxGain) const
{
  return maxGain.isMinusOne();
}

/*
 * A gain is 'safe' with respect to the tableau if:
 * - the selected variable is unbounded and every base variable where it
 *   occurs is unbounded in the direction of the gain. maxGain == -1 is used
 *   to indicate unbounded variables.
 * - the selected variable is a rational (minGain == -1, maxGain >= 0).
 */
bool TheoryArith::safeGain(const InfNumeral& minGain,
                           const InfNumeral& maxGain) const
{
  return unboundedGain(maxGain) || minGain <= maxGain;
}

/** Ensure that the maximal gain is divisible by divisor. */
void TheoryArith::normalizeGain(const Numeral& divisor,
                                InfNumeral& maxGain) const
{
  Assert(z3::isInt(divisor));
  if (!isMinusOne(divisor) && !maxGain.isMinusOne())
  {
    maxGain = floor(maxGain / divisor) * divisor;
  }
}

/** Initialize gains for x based on the bounds for x. */
void TheoryArith::initGains(
    TheoryVar x,  // non-base variable to increment/decrement
    bool inc,
    InfNumeral& minGain,  // min value to increment, -1 if rational
    InfNumeral& maxGain)  // max value to decrement, -1 if unbounded
{
  minGain = -InfNumeral(1);
  maxGain = -InfNumeral(1);
  if (inc && upper(x))
  {
    maxGain = upperBound(x) - getValue(x);
  }
  else if (!inc && lower(x))
  {
    maxGain = getValue(x) - lowerBound(x);
  }
  if (isInt(x))
  {
    minGain = InfNumeral(1);
  }

  Assert(maxGain.isMinusOne() || !maxGain.isNeg());
  Assert(minGain.isMinusOne() || minGain.isOne());
  Assert(isInt(x) == minGain.isOne());
}

bool TheoryArith::updateGains(
    bool inc,             // increment/decrement x_j
    TheoryVar xI,         // potential base variable to pivot
    const Numeral& aIJ,   // coefficient of x_j in row where x_i is base.
    InfNumeral& minGain,  // min value to increment, -1 if rational
    InfNumeral& maxGain)  // max value to decrement, -1 if unbounded
{
  // x_i = row + a_ij*x_j
  // a_ij > 0, inc -> decrement x_i
  // a_ij < 0, !inc -> decrement x_i
  // a_ij denominator

  Assert(!aIJ.isZero());

  if (!safeGain(minGain, maxGain))
  {
    return false;
  }

  InfNumeral maxInc = InfNumeral(-1);
  bool decrementXI = (inc && isPos(aIJ)) || (!inc && isNeg(aIJ));
  if (decrementXI && lower(xI))
  {
    maxInc = abs((getValue(xI) - lowerBound(xI)) / aIJ);
  }
  else if (!decrementXI && upper(xI))
  {
    maxInc = abs((upperBound(xI) - getValue(xI)) / aIJ);
  }
  Numeral denAIJ(1);
  bool isTighter = false;
  if (isInt(xI))
  {
    denAIJ = denominator(aIJ);
  }
  Assert(isPos(denAIJ) && z3::isInt(denAIJ));

  if (isInt(xI) && !denAIJ.isOne())
  {
    if (minGain.isNeg())
    {
      minGain = InfNumeral(denAIJ);
    }
    else
    {
      minGain = InfNumeral(lcm(minGain.getRational(), denAIJ));
    }
    normalizeGain(minGain.getRational(), maxGain);
  }

  if (isInt(xI) && !maxGain.isInt())
  {
    maxGain = InfNumeral(floor(maxGain));
    normalizeGain(minGain.getRational(), maxGain);
  }

  if (!maxInc.isMinusOne())
  {
    if (isInt(xI))
    {
      maxInc = floor(maxInc);
      normalizeGain(minGain.getRational(), maxInc);
    }
    if (unboundedGain(maxGain))
    {
      maxGain = maxInc;
      isTighter = true;
    }
    else if (maxGain > maxInc)
    {
      maxGain = maxInc;
      isTighter = true;
    }
  }

  Assert(maxGain.isMinusOne() || !maxGain.isNeg());
  Assert(minGain.isMinusOne() || !minGain.isNeg());
  return isTighter;
}

/** Check if bound change affects interface equality. */
bool TheoryArith::hasInterfaceEquality(TheoryVar x)
{
  TheoryVar num = static_cast<TheoryVar>(getNumVars());
  ENode* r = getENode(x)->getRoot();
  for (TheoryVar v = 0; v < num; ++v)
  {
    if (v == x)
    {
      continue;
    }
    ENode* n = getENode(v);
    if (d_ctx.isShared(n) && n->getRoot() == r)
    {
      return true;
    }
  }
  return false;
}

/**
 * Maximize (Minimize) the given temporary row.
 * Return true if succeeded.
 */
TheoryArith::MaxMinT TheoryArith::maxMin(Row& r,
                                         bool max,
                                         bool maintainIntegrality,
                                         bool& hasShared)
{
  d_stats.d_maxMin++;
  size_t bestEfforts = 0;
  bool inc = false;

  Numeral aIJ, currAIJ, coeff, currCoeff;
  InfNumeral minGain, maxGain, currMinGain, currMaxGain;
  size_t round = 0;
  MaxMinT result = OPTIMIZED;
  hasShared = false;
  size_t maxEfforts = 10 + (static_cast<unsigned>(d_ctx.getRandomValue()) % 20);
  while (bestEfforts < maxEfforts && !d_ctx.getCancelFlag())
  {
    TheoryVar xJ = s_nullTheoryVar;
    TheoryVar xI = s_nullTheoryVar;
    bool hasBound = false;
    maxGain.reset();
    minGain.reset();
    ++round;

    (void)round;
    for (const RowEntry& e : r)
    {
      if (e.isDead())
      {
        continue;
      }
      TheoryVar currXJ = e.d_var;
      TheoryVar currXI = s_nullTheoryVar;
      Assert(isNonBase(currXJ));
      currCoeff = e.d_coeff;
      bool currInc = isPos(currCoeff) ? max : !max;
      if ((currInc && upper(currXJ)) || (!currInc && lower(currXJ)))
      {
        hasBound = true;
      }
      if ((currInc && atUpper(currXJ)) || (!currInc && atLower(currXJ)))
      {
        // variable cannot be used for max/min.
        continue;
      }
      bool safeToLeave = pickVarToLeave(currXJ,
                                        currInc,
                                        currAIJ,
                                        currMinGain,
                                        currMaxGain,
                                        hasShared,
                                        currXI);

      if (!safeToLeave)
      {
        hasBound = true;
        bestEfforts++;
      }
      else if (currXI == s_nullTheoryVar)
      {
        // we can increase/decrease currXJ as much as we want.
        xI = s_nullTheoryVar;  // unbounded
        xJ = currXJ;
        inc = currInc;
        minGain = currMinGain;
        maxGain = currMaxGain;
        break;
      }
      else if (currMaxGain > maxGain)
      {
        xI = currXI;
        xJ = currXJ;
        aIJ = currAIJ;
        coeff = currCoeff;
        maxGain = currMaxGain;
        minGain = currMinGain;
        inc = currInc;
      }
      else if (currMaxGain.isZero() && (xI == s_nullTheoryVar || currXI < xI))
      {
        xI = currXI;
        xJ = currXJ;
        aIJ = currAIJ;
        coeff = currCoeff;
        maxGain = currMaxGain;
        minGain = currMinGain;
        inc = currInc;
        // continue
      }
    }

    if (!hasBound && xI == s_nullTheoryVar && xJ == s_nullTheoryVar)
    {
      hasShared = false;
      bestEfforts = 0;
      result = UNBOUNDED;
      break;
    }

    if (xJ == s_nullTheoryVar)
    {
      result = OPTIMIZED;
      break;
    }

    if (minGain.isPos() && !minGain.isOne())
    {
      ++bestEfforts;
    }
    if (xI == s_nullTheoryVar)
    {
      // can increase/decrease xJ as much as we want.

      if (inc && upper(xJ))
      {
        if (maxGain.isZero())
        {
          return BEST_EFFORT;
        }
        Assert(!unboundedGain(maxGain));
        updateValue(xJ, maxGain);
        continue;
      }
      if (!inc && lower(xJ))
      {
        if (maxGain.isZero())
        {
          return BEST_EFFORT;
        }
        Assert(!unboundedGain(maxGain));
        Assert(maxGain.isPos());
        maxGain.neg();
        updateValue(xJ, maxGain);
        continue;
      }
      //
      // NB (Z3). As it stands this is a possibly unsound conclusion for
      // shared theories. The tradeoff is non-termination for unbounded
      // objectives in the presence of sharing.
      //
      hasShared = false;
      bestEfforts = 0;
      result = UNBOUNDED;
      break;
    }

    if (!isFixed(xJ) && isBounded(xJ)
        && (upperBound(xJ) - lowerBound(xJ) == maxGain))
    {
      // can increase/decrease xJ up to upper/lower bound.
      if (!inc)
      {
        maxGain.neg();
      }
      updateValue(xJ, maxGain);
      continue;
    }

    pivot<true>(xI, xJ, aIJ, false);

    Assert(isNonBase(xI));
    Assert(isBase(xJ));

    bool incXI = inc ? isNeg(aIJ) : isPos(aIJ);
    if (!moveToBound(xI, incXI, bestEfforts, hasShared))
    {
      // can't move bound fully
    }

    Row& r2 = d_rows[getVarRow(xJ)];
    coeff = -coeff;
    addTmpRow(r, coeff, r2);
    Assert(r.getIdxOf(xJ) == -1);
  }
  return (bestEfforts > 0 || d_ctx.getCancelFlag()) ? BEST_EFFORT : result;
}

/**
 * Move the variable xI maximally towards its bound as long as bounds of
 * other variables are not violated. Returns false if an integer bound was
 * truncated and no progress was made.
 */
bool TheoryArith::moveToBound(
    TheoryVar xI,         // variable to move
    bool inc,             // increment variable or decrement
    size_t& bestEfforts,  // is bound move a best effort?
    bool& hasShared)      // does move include shared variables?
{
  InfNumeral minGain, maxGain;
  if (isInt(xI) && !getValue(xI).isInt())
  {
    ++bestEfforts;
    return false;
  }
  initGains(xI, inc, minGain, maxGain);
  Column& c = d_columns[xI];
  for (const ColEntry& ce : c)
  {
    if (ce.isDead())
    {
      continue;
    }
    const Row& r = d_rows[ce.d_rowId];
    TheoryVar s = r.getBaseVar();
    const Numeral& coeff = r[ce.d_rowIdx].d_coeff;
    updateGains(inc, s, coeff, minGain, maxGain);
    hasShared |= d_ctx.isShared(getENode(s));
  }
  bool result = false;
  if (safeGain(minGain, maxGain))
  {
    Assert(!unboundedGain(maxGain));
    if (!inc)
    {
      maxGain.neg();
    }
    updateValue(xI, maxGain);
    if (!minGain.isPos() || minGain.isOne())
    {
      ++bestEfforts;
    }
    result = !maxGain.isZero();
  }
  if (!result)
  {
    ++bestEfforts;
  }
  return result;
}

/**
 * Add an entry to a temporary row.
 *
 * Columns do not need to be updated when updating a temporary row.
 */
template <bool invert>
void TheoryArith::addTmpRowEntry(Row& r, const Numeral& coeff, TheoryVar v)
{
  int rIdx;
  RowEntry& rEntry = r.addRowEntry(rIdx);
  rEntry.d_var = v;
  rEntry.d_coeff = coeff;
  if (invert)
  {
    rEntry.d_coeff = -rEntry.d_coeff;
  }
}

/**
 * Maximize/Minimize the given variable. The bounds of v are updated if the
 * procedure succeeds.
 */
TheoryArith::MaxMinT TheoryArith::maxMin(TheoryVar v,
                                         bool max,
                                         bool maintainIntegrality,
                                         bool& hasShared)
{
  Assert(!isQuasiBase(v));
  if ((max && atUpper(v)) || (!max && atLower(v)))
  {
    return AT_BOUND;  // nothing to be done...
  }
  d_tmpRow.reset();
  if (isNonBase(v))
  {
    addTmpRowEntry<false>(d_tmpRow, Numeral(1), v);
  }
  else
  {
    Row& r = d_rows[getVarRow(v)];
    for (const RowEntry& e : r)
    {
      if (!e.isDead() && e.d_var != v)
      {
        addTmpRowEntry<true>(d_tmpRow, e.d_coeff, e.d_var);
      }
    }
  }
  MaxMinT r = maxMin(d_tmpRow, max, maintainIntegrality, hasShared);
  if (r == OPTIMIZED)
  {
    mkBoundFromRow(v, getValue(v), max ? B_UPPER : B_LOWER, d_tmpRow);
  }
  return r;
}

/**
 * Maximize & Minimize variables in vars.
 * Return false if an inconsistency was detected.
 */
bool TheoryArith::maxMin(const std::vector<TheoryVar>& vars)
{
  bool succ = false;
  bool hasShared = false;
  for (TheoryVar v : vars)
  {
    if (maxMin(v, true, false, hasShared) == OPTIMIZED && !hasShared)
    {
      succ = true;
    }
    if (maxMin(v, false, false, hasShared) == OPTIMIZED && !hasShared)
    {
      succ = true;
    }
  }
  if (succ)
  {
    // process new bounds
    bool r = propagateCore();
    return r;
  }
  return true;
}

// -----------------------------------
//
// Freedom intervals
//
// -----------------------------------

/**
 * See Model-based theory combination paper.
 * Return false if failed to build the freedom interval.
 *
 * If xJ is an integer variable, then m will contain the lcm of the
 * denominators of a_ij. We only consider the a_ij coefficients for x_i.
 */
bool TheoryArith::getFreedomInterval(TheoryVar xJ,
                                     bool& infL,
                                     InfNumeral& l,
                                     bool& infU,
                                     InfNumeral& u,
                                     Numeral& m)
{
  if (isBase(xJ))
  {
    return false;
  }

  const InfNumeral& xJVal = getValue(xJ);
  Column& c = d_columns[xJ];

  infL = true;
  infU = true;
  l.reset();
  u.reset();
  m = Numeral(1);
#define IS_FIXED()                \
  {                               \
    if (!infL && !infU && l == u) \
    {                             \
      goto fi_succeeded;          \
    }                             \
  }
#define SET_LOWER(VAL)            \
  {                               \
    const InfNumeral& _VAL = VAL; \
    if (infL || _VAL > l)         \
    {                             \
      l = _VAL;                   \
      infL = false;               \
    }                             \
    IS_FIXED();                   \
  }
#define SET_UPPER(VAL)            \
  {                               \
    const InfNumeral& _VAL = VAL; \
    if (infU || _VAL < u)         \
    {                             \
      u = _VAL;                   \
      infU = false;               \
    }                             \
    IS_FIXED();                   \
  }

  if (lower(xJ))
  {
    SET_LOWER(lowerBound(xJ));
  }
  if (upper(xJ))
  {
    SET_UPPER(upperBound(xJ));
  }

  for (const ColEntry& ce : c)
  {
    if (!ce.isDead())
    {
      Row& r = d_rows[ce.d_rowId];
      TheoryVar xI = r.getBaseVar();
      if (xI != s_nullTheoryVar && !isQuasiBase(xI))
      {
        const Numeral& aIJ = r[ce.d_rowIdx].d_coeff;
        const InfNumeral& xIVal = getValue(xI);
        if (isInt(xI) && isInt(xJ) && !z3::isInt(aIJ))
        {
          m = lcm(m, denominator(aIJ));
        }
        Bound* xILower = lower(xI);
        Bound* xIUpper = upper(xI);
        if (isNeg(aIJ))
        {
          if (xILower)
          {
            InfNumeral newL = xJVal + ((xIVal - xILower->getValue()) / aIJ);
            SET_LOWER(newL);
          }
          if (xIUpper)
          {
            InfNumeral newU = xJVal + ((xIVal - xIUpper->getValue()) / aIJ);
            SET_UPPER(newU);
          }
        }
        else
        {
          if (xIUpper)
          {
            InfNumeral newL = xJVal + ((xIVal - xIUpper->getValue()) / aIJ);
            SET_LOWER(newL);
          }
          if (xILower)
          {
            InfNumeral newU = xJVal + ((xIVal - xILower->getValue()) / aIJ);
            SET_UPPER(newU);
          }
        }
      }
    }
  }
fi_succeeded:
#undef IS_FIXED
#undef SET_LOWER
#undef SET_UPPER
  return true;
}

// -----------------------------------
//
// Implied eqs
//
// -----------------------------------

/**
 * Try to check whether v1 == v2 is implied by the current state.
 * If it is return true.
 */
bool TheoryArith::tryToImplyEq(TheoryVar v1, TheoryVar v2)
{
  Assert(v1 != v2);
  Assert(getValue(v1) == getValue(v2));
  if (isQuasiBase(v1) || isQuasiBase(v2))
  {
    return false;
  }
  d_tmpRow.reset();

  if (isNonBase(v1))
  {
    addTmpRowEntry<false>(d_tmpRow, Numeral(1), v1);
  }
  else
  {
    Row& r = d_rows[getVarRow(v1)];
    for (const RowEntry& e : r)
    {
      if (!e.isDead() && e.d_var != v1)
      {
        addTmpRowEntry<true>(d_tmpRow, e.d_coeff, e.d_var);
      }
    }
  }

  d_tmpRow.saveVarPos(d_varPos);

#define ADD_ENTRY(COEFF, VAR)                      \
  {                                                \
    int pos = d_varPos[VAR];                       \
    if (pos == -1)                                 \
    {                                              \
      addTmpRowEntry<false>(d_tmpRow, COEFF, VAR); \
    }                                              \
    else                                           \
    {                                              \
      RowEntry& rEntry = d_tmpRow[pos];            \
      Assert(rEntry.d_var == VAR);                 \
      rEntry.d_coeff += COEFF;                     \
      if (rEntry.d_coeff.isZero())                 \
      {                                            \
        d_tmpRow.delRowEntry(pos);                 \
      }                                            \
      d_varPos[VAR] = -1;                          \
    }                                              \
  }

  if (isNonBase(v2))
  {
    ADD_ENTRY(Numeral(-1), v2);
  }
  else
  {
    Row& r = d_rows[getVarRow(v2)];
    for (const RowEntry& e : r)
    {
      if (!e.isDead() && e.d_var != v2)
      {
        Numeral c = e.d_coeff;
        c = -c;
        ADD_ENTRY(c, e.d_var);
      }
    }
  }
#undef ADD_ENTRY
  d_tmpRow.resetVarPos(d_varPos);

  Assert(d_tmpRow.size() > 0);

  // Z3 has the actual implied-equality check under #if 0.
  return false;
}

// -----------------------------------
//
// Assume eqs
//
// The revamped assume eqs try to perturbate the current assignment using
// pivoting operations.
//
// -----------------------------------

namespace {
const int s_range = 10000;  // Z3's RANGE
}

/**
 * Performs a random update on v using its freedom interval.
 * Return true if it was possible to change.
 */
bool TheoryArith::randomUpdate(TheoryVar v)
{
  if (isFixed(v) || !isNonBase(v))
  {
    return false;
  }
  bool infL, infU;
  InfNumeral l, u;
  Numeral m;
  getFreedomInterval(v, infL, l, infU, u, m);
  if (infL && infU)
  {
    InfNumeral newVal = InfNumeral(d_random() % (s_range + 1));
    setValue(v, newVal);
    return true;
  }
  if (isInt(v))
  {
    if (!infL)
    {
      l = ceil(l);
      if (!m.isOne())
      {
        l = m * ceil(l / m);
      }
    }
    if (!infU)
    {
      u = floor(u);
      if (!m.isOne())
      {
        u = m * floor(u / m);
      }
    }
  }
  if (!infL && !infU && l >= u)
  {
    return false;
  }
  if (infU)
  {
    Assert(!infL);
    InfNumeral delta = InfNumeral(d_random() % (s_range + 1));
    InfNumeral newVal = l + m * delta;
    setValue(v, newVal);
    return true;
  }
  if (infL)
  {
    Assert(!infU);
    InfNumeral delta = InfNumeral(d_random() % (s_range + 1));
    InfNumeral newVal = u - m * delta;
    setValue(v, newVal);
    return true;
  }
  if (!isInt(v))
  {
    Assert(!infL && !infU);
    Numeral delta = Numeral(d_random() % (s_range + 1));
    InfNumeral newVal = l + ((delta * (u - l)) / Numeral(s_range));
    setValue(v, newVal);
    return true;
  }
  else
  {
    unsigned range = s_range;
    Numeral r = (u.getRational() - l.getRational()) / m;
    if (r < Numeral(s_range))
    {
      // r is a non-negative integer here (l and u are multiples of m)
      range = static_cast<unsigned>(r.getNumerator().getUnsignedLong());
    }
    InfNumeral newVal =
        l
        + m
              * (InfNumeral(static_cast<int>(static_cast<unsigned>(d_random())
                                             % (range + 1))));
    setValue(v, newVal);
    return true;
  }
}

void TheoryArith::mutateAssignment()
{
  Assert(d_toPatch.empty());
  removeFixedVarsFromBase();
  int numVars = static_cast<int>(getNumVars());
  d_varValueTable.reset();
  d_tmpVarSet.clear();
  std::vector<TheoryVar> candidates;
  for (TheoryVar v = 0; v < numVars; ++v)
  {
    ENode* n1 = getENode(v);
    if (!isRelevantAndShared(n1))
    {
      continue;
    }
    TheoryVar other = d_varValueTable.insertIfNotThere(v);
    if (other == v)
    {
      continue;  // first node with the given value...
    }
    ENode* n2 = getENode(other);
    if (n1->getRoot() == n2->getRoot())
    {
      continue;
    }
    if (!isFixed(v))
    {
      candidates.push_back(v);
    }
    else if (!isFixed(other) && d_tmpVarSet.find(other) == d_tmpVarSet.end())
    {
      d_tmpVarSet.insert(other);
      candidates.push_back(other);
    }
  }

  if (candidates.empty())
  {
    return;
  }
  d_tmpVarSet.clear();
  d_tmpVarSet2.clear();
  for (TheoryVar v : candidates)
  {
    Assert(!isFixed(v));
    if (isBase(v))
    {
      Row& r = d_rows[getVarRow(v)];
      for (const RowEntry& e : r)
      {
        if (!e.isDead() && e.d_var != v && !isFixed(e.d_var)
            && randomUpdate(e.d_var))
        {
          break;
        }
      }
    }
    else
    {
      randomUpdate(v);
    }
  }
  Assert(d_toPatch.empty());
}

/**
 * This method is redefined, because the theory of arithmetic contains
 * underspecified operators such as division by 0. (/ a b) is essentially an
 * uninterpreted function when b = 0. Thus, 'a' must be considered a shared
 * var if it is the child of an underspecified operator.
 */
bool TheoryArith::isShared(TheoryVar v) const
{
  if (d_underspecifiedOps.empty())
  {
    return false;
  }
  ENode* n = getENode(v);
  ENode* r = n->getRoot();
  for (ENode* parent : r->getConstParents())
  {
    TNode o = parent->getExpr();
    // Z3's OP_DIV, OP_IDIV, OP_REM, OP_MOD (cvc5 has no rem)
    if (arith::isDiv(o) || arith::isIdiv(o) || arith::isMod(o))
    {
      return true;
    }
  }
  return false;
}

bool TheoryArith::assumeEqs()
{
  // See comment in d_liberalFinalCheck declaration
  if (d_liberalFinalCheck)
  {
    mutateAssignment();
  }

  size_t oldSz = d_assumeEqCandidates.size();
  d_varValueTable.reset();
  bool result = false;
  int num = static_cast<int>(getNumVars());
  for (TheoryVar v = 0; v < num; ++v)
  {
    ENode* n = getENode(v);
    if (!isRelevantAndShared(n))
    {
      continue;
    }
    TheoryVar other = s_nullTheoryVar;
    other = d_varValueTable.insertIfNotThere(v);
    if (other == v)
    {
      continue;
    }
    ENode* n2 = getENode(other);
    if (n->getRoot() == n2->getRoot())
    {
      continue;
    }
    d_assumeEqCandidates.push_back({other, v});
    result = true;
  }

  if (result)
  {
    d_ctx.pushTrail(RestoreVector<std::vector<std::pair<TheoryVar, TheoryVar>>>(
        d_assumeEqCandidates, oldSz));
  }
  return delayedAssumeEqs();
}

bool TheoryArith::delayedAssumeEqs()
{
  if (d_assumeEqHead == d_assumeEqCandidates.size())
  {
    return false;
  }

  d_ctx.pushTrail(ValueTrail<size_t>(d_assumeEqHead));
  while (d_assumeEqHead < d_assumeEqCandidates.size())
  {
    std::pair<TheoryVar, TheoryVar> p = d_assumeEqCandidates[d_assumeEqHead];
    TheoryVar v1 = p.first;
    TheoryVar v2 = p.second;
    ENode* n1 = getENode(v1);
    ENode* n2 = getENode(v2);
    d_assumeEqHead++;
    if (getValue(v1) == getValue(v2) && n1->getRoot() != n2->getRoot()
        && assumeEq(n1, n2))
    {
      ++d_stats.d_assumeEqs;
      return true;
    }
  }
  return false;
}

// -----------------------------------
//
// var_value_table (int_hashtable<var_value_hash, var_value_eq>)
//
// -----------------------------------

TheoryVar TheoryArith::VarValueTable::insertIfNotThere(TheoryVar v)
{
  // var_value_hash: get_value(v).hash()
  size_t h = d_th.getValue(v).hash();
  std::vector<TheoryVar>& bucket = d_table[h];
  for (TheoryVar w : bucket)
  {
    // var_value_eq. Note getValue of a quasi-base variable returns a
    // reference to a shared temporary, as in Z3.
    if (d_th.getValue(w) == d_th.getValue(v)
        && d_th.isIntSrc(w) == d_th.isIntSrc(v))
    {
      return w;
    }
  }
  bucket.push_back(v);
  return v;
}

// Explicit instantiations of the member templates defined in this file.
template void TheoryArith::addTmpRowEntry<false>(Row&,
                                                 const Numeral&,
                                                 TheoryVar);
template void TheoryArith::addTmpRowEntry<true>(Row&,
                                                const Numeral&,
                                                TheoryVar);

}  // namespace z3
}  // namespace cvc5::internal

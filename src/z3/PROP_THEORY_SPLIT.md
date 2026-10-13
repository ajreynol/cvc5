# Stage 1B audit: the propositional/theory boundary inside `SmtContext`

Date: 2026-10-12

Source snapshot: `8a1ca4ad2c` (Stage 1A), plus the capability changes that
follow it.

Status: steps 1–4 of the sequence in section 8 are done. The rest of this
document describes the state before them, except where marked.

This is the dependency audit that section 7 of
[ARCHITECTURE_PLAN.md](ARCHITECTURE_PLAN.md) asks for before `SmtContext` is
divided into a propositional implementation and a theory implementation. It
records:

- who owns each piece of state today;
- every interaction that crosses the intended boundary, grouped by the
  plan's interaction table;
- how relevancy and internalization should be allocated;
- an order of extraction steps, each of which preserves behavior.

The function names are those in `smt_context.{h,cpp}`, `internalizer.cpp`
and the satellite files. Line numbers are omitted because the extraction
steps will invalidate them.

## 1. Findings in brief

- **The Boolean engine is cohesive and can be cut out.** The following form
  one tight cluster that touches theory state only through a small number of
  calls: assignment, watch lists, clauses, BCP, first-UIP conflict analysis,
  the case split queue, restarts, lemma GC and clause simplification. The
  search driver (`search`, `boundedSearch`, `propagate`, `restart`,
  `decide`) belongs with it, in the same way that cvc5's SAT solver drives
  `TheoryProxy`.
- **The E-graph, theory dispatch and quantifiers form the other cluster.**
  Theory plugins use 48 distinct `SmtContext` methods. All of them are public
  and none relies on friendship. Most belong to the E-graph or to
  internalization; about 20 belong to the Boolean side and 7 to relevancy.
- **Theory delivery is already a queue.** The Boolean side pushes assigned
  atoms onto `d_atomPropagationQueue`, after a relevancy gate in
  `assignCore`. The theory side drains the queue in `propagateAtoms`. This is
  the natural counterpart of `TheoryProxy::enqueueTheoryLiteral`.
- **Explanations are eager, but explaining an equality reads the E-graph.** A
  justification copies its literals and enode pairs when it is created.
  During conflict analysis, `ConflictResolution::eq2Literals` turns each enode
  pair into literals by walking the E-graph's proof forest (`d_trans`). That
  walk is the one place where the Boolean side reads theory state in its own
  code. It should become an explainer owned by the theory side.
- **Relevancy belongs with the propositional side**, as a component it owns
  with an explicit interface for the theory side (section 6). Relevancy is
  the most re-entrant component: one call to `markAsRelevant` can reach the
  case split queue, the quantifier manager and every theory synchronously.
- **Internalization should be split as cvc5 splits CNF conversion from
  pre-registration** (section 6). Boolean structure goes to the
  propositional side; enodes, theory atoms, equalities and quantifiers go to
  the theory side.
- **Some infrastructure is shared and should remain so, explicitly.** The
  trail stack, the region allocator, the scope levels, `Params` and the
  statistics are used by both sides. They play the role that
  `context::Context` plays between cvc5's SAT solver and its theories
  (section 7).
- **Dead paths and a few lifecycle defects turned up** (section 9). Removing
  the dead paths first makes the boundary smaller.

## 2. Ownership of today's `SmtContext` state

Key: **P** is the propositional side, **T** the theory side, **R** relevancy,
and **S** shared infrastructure.

| State | Owner | Notes |
|---|---|---|
| `d_assignment`, `d_assignedLiterals`, `d_qhead`, `d_watches`, `d_litOccs`, `d_litScores` | P | |
| `d_bdata`: scope level, justification, phase, marks, internalization level, true-first | P | Read by T for levels and assignment |
| `d_bdata` atom-kind flags (`d_enode`, `d_eq`, `d_quantifier`, `d_notifyTheory`) | T | P reads only their union, `isAtom`, to decide what to enqueue (section 4.2) |
| `d_activity`, `d_bvarInc`, `d_birthdate`, phase cache fields, `d_random` | P | |
| `d_auxClauses`, `d_lemmas`, `d_clausesToReinit`, `d_unitsToReassert`, `d_simpQhead`, `d_simpCounter` | P | |
| `d_conflict`, `d_notL`, `d_conflictResolution` | P | The proof-forest walk is now `d_explainer` (T, step 2) |
| `d_caseSplitQueue` | P | Consumes `relevantEh` and, optionally, `isExtDiseq` |
| restart, lemma-GC and search counters (`d_numConflicts`…`d_lemmaGcThreshold`, `d_agility`, `d_lubyIdx`) | P | |
| `d_expr2BoolVar`, `d_boolVar2Expr` | P | The Node↔BoolVar map |
| `d_thCaseSplitSets`, `d_literal2CaseSplitSets`, `d_allThCaseSplitLiterals` | none | Dead; removed in step 1 |
| `d_app2ENode`, `d_enodes`, `d_decl2ENodes`, `d_declIds`, `d_cgTable`, `d_trueENode`, `d_falseENode`, `d_isDiseqTmp`, `d_tmpENode` | T | The E-graph |
| `d_eqPropagationQueue`, `d_thEqPropagationQueue`, `d_thDiseqPropagationQueue` | T | |
| `d_atomPropagationQueue` | T | P feeds it, T drains it |
| `d_theories`, `d_theorySet`, `d_finalCheckIdx`, `d_cvc5Bridge` | T | |
| `d_qmanager`, `d_fingerprints` | T | The fingerprints should move into the quantifier manager |
| `d_dynAckManager` | T | Needs P's lemma clauses with a deletion hook |
| `d_generation`, `d_stickyGenerationUpdates`, `d_cachedGeneration`, `d_cacheGenerationVisited` | T | `cacheGeneration` runs during P's backjump (section 4.8) |
| `d_unsupported`, `d_modelUnsoundTheories`, `d_incompleteTheories` | T | Theory status (section 4.9). The first two are now `d_theoryStatus` (step 3); the third was dead and is removed (step 1) |
| `d_relevancyPropagator`, `d_relevancyLvl` | R | Owned by P (section 6) |
| `d_trailStack`, `d_region`, `d_scopeLvl`, `d_baseLvl`, `d_searchLvl`, `d_scopes`, `d_baseScopes` | S | P sets the levels and T reads them |
| `d_params`, `d_stats`, `d_regStats` | S | |
| `d_assertedFormulas`, `d_assertedFormulasQhead`, `d_assertedInconsistent`, `d_hasQuantifiers` | P | The input queue (section 9 for its scoping) |
| `d_normalizer`, `d_connNormalizer`, `d_assertionRewriter`, `d_nnf`, `d_ngPushAppIte`, `d_patternInference` | T | Used by `AssertionPreparation` and by instance internalization |
| `d_lastSearchResult`, `d_lastSearchFailure`, `d_unknown`, `d_searching`, `d_setupDone` | P | The driver's state. T contributes failure reasons |

## 3. The search loop, seen from the boundary

**Propagation fixpoint (`propagate`).** Every iteration runs these steps in
order, and stops as soon as the context is inconsistent:

1. `bcp` (P).
2. `propagateThCaseSplit(qhead)` (P). It is dead today.
3. `propagateRelevancy(qhead)` (R). Every literal assigned since `qhead`
   goes to `RelevancyPropagator::assignEh`, which can call back
   `relevantEh`.
4. `propagateAtoms` (T). Drains the atom queue into Boolean enode merges,
   `addEq` / `addDiseq`, `Theory::assignEh` and `QuantifierManager::assignEh`.
5. `propagateEqs` (T). Merges in the E-graph. A merge can call `assign` on P.
6. `propagateThEqs`, then `propagateThDiseqs` (T). These call
   `Theory::newEqEh` and `Theory::newDiseqEh`.
7. `propagateTheories` (T). Calls `Theory::propagate`.
8. `QuantifierManager::propagate` (T). E-matching, then instantiation, which
   internalizes instances.
9. If a resource limit has been exceeded, `d_qhead` is rewound to `qhead` and
   the loop returns. Otherwise it repeats while `canPropagate` holds, which
   checks P's queue head, R, and every T queue.

Theories run only after BCP has saturated. Atoms assigned during steps 4–8
reach the theories in the next iteration.

**`boundedSearch`.** It loops `propagate`, then `resolveConflict`, restart and
limit checks, lemma GC and `DynAckManager::propagateEh` (T). At base level it
then calls `simplifyClauses`, then `decide`. When nothing is left to decide it
calls `finalCheck` (T):

- the quantifier manager is consulted first;
- the theories are then consulted round-robin, with the quantifier manager in
  the last slot;
- the first `FC_CONTINUE` wins.

**`restart`.** When the result is L_TRUE and the input has quantifiers,
`restart` calls `QuantifierManager::checkModel`. Otherwise it pops to the
search level, then calls `Theory::restartEh`, then
`QuantifierManager::restartEh`. Both can raise a conflict.

**`pushScope`.** P increments `d_scopeLvl`, then pushes the region (S), the
trail (S), and P's scope limits. R pushes. T pushes the quantifier manager,
the fingerprints, the case split queue (P), and then each theory with
`pushScopeEh`.

**`popScopeCore`.** The current order is load-bearing and must be
reproduced exactly:

1. `cacheGeneration` (T, reads enode and quantifier generations).
2. `QuantifierManager::pop` (T).
3. Case split queue pop (P).
4. Clause and conflict reset, then deletion of aux clauses (P).
5. Relevancy pop (R).
6. Fingerprints pop (T).
7. `unassignVars` (P).
8. Trail pop (S). This undoes E-graph merges, `mkBoolVar` / `mkENode`, flag
   trails, and the trail entries of theories and the quantifier manager, in
   one LIFO order.
9. `Theory::popScopeEh` (T). It runs after both the Boolean unassignment and
   the E-graph undo.
10. `delJustifications`.
11. Clearing of T's queues.
12. Region pop (S).
13. Conflict-resolution reset (P).
14. `reinitClauses` (P), which fully re-internalizes dead lemma atoms through
    T.
15. `reassertUnits` (P).

Nothing notifies the theories when an individual literal is unassigned. They
rely on `popScopeEh`.

## 4. Interactions across the boundary, by the plan's categories

### 4.1 Term and atom registration

**Today.** Internalization creates Boolean variables and enodes together.
`internalizeFormulaCore` makes a Boolean variable, makes an enode when the
formula is outside a gate or has arguments, and emits the gate clauses and
relevancy watches. `internalizeEq`, `internalizeTheoryAtom` and
`internalizeQuantifier` register the atom with T.

`Theory::internalizeAtom` must create the Boolean variable itself, by calling
`mkBoolVar` and then `setVarTheory`. Theories also call `mkENode`,
`attachThVar`, `setEnodeFlag` and `internalize` directly, including from
`propagate`, `newEqEh` and `finalCheckEh`. Registration therefore produces
further work during the search.

The search internalizes in these places:

- quantifier instances (`QiQueue` → `internalizeInstance`);
- ground pattern terms (MAM);
- dynamic Ackermann equalities;
- `assumeEq`;
- theory axioms and splits;
- P's own `reinitClauses`, `reassertUnits` and `resolveConflict`, which
  re-create atoms that a pop deleted.

**Contract.** P provides `mkBoolVar(Node)` and the clause API. T provides
atom registration: a Boolean variable already exists, and T is told what kind
of atom it is. This corresponds to `CnfStream` calling `TheoryProxy::preRegister`.
P asks T to re-create the atoms of a surviving lemma after a pop. The map from
Boolean variables to enodes stays keyed by Node id on both sides, as
`d_expr2BoolVar` and `d_app2ENode` are today.

**Complications.**

- Theories call the low-level internalizer steps directly. They should go
  through one atom-registration call.
- Flag trails are conditional on internalization levels, which assumes that
  an object created in the current scope is deleted whole on pop.

### 4.2 Assigned literals delivered to the theory side

**Today.** `assignCore` pushes an atom onto `d_atomPropagationQueue` in three
cases:

- relevancy is off;
- relevancy is at level 1 and the atom is not a quantifier;
- the literal is already relevant.

`relevantEh` re-enqueues atoms that were already assigned when they become
relevant. This applies to quantifiers, and to every atom when the relevancy
level is at least 2.

**Contract.** P enqueues; T drains in its `propagate` step. The queue is T's
inbox. P needs only `isAtom(var)`. The atom-kind flags that drive dispatch
move to T.

### 4.3 Equality and disequality information

**Today.** This is entirely internal to T: `addEq`, `mergeTheoryVars`,
`addDiseq`, the three equality queues, `newEqEh` / `newDiseqEh`, `assignEq`,
and `QuantifierManager::addEqEh`.

Three things cross the boundary:

- **T reads P's assignment.** `pushNewThDiseqs` reads the assignment of an
  equality parent.
- **T assigns P's literals.** `reinsertParentsIntoCgTable` assigns equality
  atoms whose arguments merged, `propagateBoolENodeAssignment` /
  `propagateBoolVarENode` copy Boolean values across a class, and `mkENode`
  assigns an `isTrueEq` atom.
- **A merge spreads relevance.** `addEq` marks the merged class relevant.

**Contract.** T reads assignments through P's query API and propagates
through `assign(lit, Justification*)`.

### 4.4 Propagations back to the Boolean search

**Today.** All propagations go through `assign(Literal, Justification*)`. The
justification kinds are:

- **E-graph:** `EqPropagationJustification`, `EqRootPropagationJustification`
  and `MpIffJustification`.
- **Theories:** `ExtTheoryPropagationJustification`, plus
  `GomoryCutJustification`, which arithmetic subclasses.
- **Axioms:** a null justification.

Justifications live in the region and die when it pops.
`getFromTheory()` is read only by `mergeTheoryVars`, to avoid echoing an
equality back to the theory that produced it.

**Contract.** P's `assign` and `setConflict` take a `Justification*` whose
lifetime is the current scope. P never inspects one except through the
explainer described next.

### 4.5 Conflicts, lemmas and explanations

**Today.** Theories raise conflicts with
`setConflict(ExtTheoryConflictJustification)`. Their clauses go through
`mkThAxiom`, which creates scope-local `CLS_TH_AXIOM` clauses, or through
`mkClause`. `mkThLemma` has no callers.

`ConflictResolution` is a friend of `SmtContext`. It does two jobs:

- **First-UIP analysis**, which reads levels, marks, activity and
  justifications.
- **Explanation.** `Justification::getAntecedents` calls back `markLiteral`,
  `markEq` and `markJustifiedEq`. `eq2Literals` then walks the proof forest
  (`d_trans`, `getRoot`, congruence arguments), and while doing so calls
  `DynAckManager::usedCgEh` / `usedEqEh`. Explanation also runs when the
  conflict level is computed.

**Contract.** Divide `ConflictResolution` along those two jobs:

- First-UIP analysis, minimization and levels stay with P.
- `justification2Literals` and `eq2Literals` become a T-owned explainer.

The interface is roughly `explain(Justification*) → literals`, and it is used
for both antecedents and levels. The dynamic Ackermann hooks become internal
to T. Lemmas from T reach P as clause requests carrying a kind, a
justification and an optional deletion hook; dynamic Ackermann needs the
hook.

### 4.6 Check scheduling

**Today.** The order is the fixpoint in section 3, followed by
`finalCheck`, `initSearch` (`Theory::initSearchEh`,
`QuantifierManager::initSearchEh`) and restart.

**Contract.** P's driver calls a T entry point for steps 4–8 of
`propagate`, a `canPropagate` query, `finalCheck`, `initSearch` and
`restart`, and `checkModel` for an L_TRUE result with quantifiers. These
correspond to `TheoryProxy::theoryPropagate`, `theoryNeedCheck`,
`theoryCheck(effort)` and `notifyRestart`.

**Complication.** `QuantifierManager::finalCheckEh` calls
`SmtContext::canPropagate` for the whole context. It needs P's part of that
answer.

### 4.7 Relevance and decisions

**Decisions.** `decide` takes the next case split from the queue. `guess`
does three things:

- forces quantifiers to the phase false;
- reads `tryTrueFirst`, which T sets through `assumeEq` and the arithmetic
  equality adapter;
- under `PS_THEORY` with the phase cache off, calls `Theory::getPhase`.

`addTheoryAwareBranchingInfo` and theory case splits have no callers.

**Relevance.** Section 6 covers relevance.

**Contract.** P asks T for a phase hint. T sets the true-first flag on P's
variable data.

### 4.8 Backtracking and restarts

**Today.** Section 3 gives the order. Two points cross the boundary in
unusual ways:

- **Generations are cached across the backjump.** `cacheGeneration` reads
  the generations of enodes and quantifiers before a backjump, and
  `mkENode` / `internalizeQuantifier` restore them when P re-creates atoms.
- **Relevance of conflict literals is preserved.** `recordRelevancy` /
  `restoreRelevancy` re-mark the literals of the conflict clause after the
  pop.

**Contract.** T's `push` is called inside P's push. T's pop has two parts:

- before unassignment: `cacheGeneration` and the quantifier manager's pop;
- after the trail undo: `popScopeEh` and clearing T's queues.

The shared trail is undone between them. The generation cache is T state
that P's backjump triggers, through a "prepare for backjump to level n"
call.

### 4.9 Final status

The result combines inputs from both sides:

- **From P:** L_FALSE, the conflict and restart limits, and cancellation or
  resource limits through `getCancelFlag`.
- **From T:**
  - `FC_GIVEUP` from a theory, reported as `THEORY`;
  - `checkModel` answering UNKNOWN, reported as `QUANTIFIERS`;
  - `checkFinalize` downgrading L_TRUE to unknown when the input is marked
    unsupported or when a theory marked the model unsound during
    internalization or a final check;
  - `setReasonUnknown`, which sets only the message.

**Contract.** T exposes a theory status: whether a model is sound, whether
the input is supported, and a failure reason. P's driver combines it with
its own outcome. `Z3PropEngine::checkSat` already translates the combined
outcome.

## 5. Components outside `SmtContext`

| Component | Side | What crosses the boundary |
|---|---|---|
| Theory plugins: arithmetic, datatypes and `Cvc5Bridge` | T | They read P's assignment, levels and `inconsistent`. They call `assign`, `setConflict`, `mkClause`, `mkThAxiom`, `mkBoolVar` and `setVarTheory`. They mark and query relevance and install relevancy handlers (arithmetic's equality adapter). They push onto the trail and allocate in the region. `Cvc5Bridge` polls the assignment of its own variable list instead of using `assignEh`. `TheoryDatatype` keeps a private trail. |
| `QuantifierManager`, MAM, `QiQueue`, checkers, `EnumInst` | T | Boolean values, `inconsistent`, the scope level (for cost), relevance (hot in MAM), instance internalization, and `canPropagate` for the whole context. The context's `d_inForcedRematch` field is used as a flag between the quantifier manager and `QiQueue`. |
| `RelevancyPropagator` | R, owned by P | Reads P's assignment on its hot path. Reads T's equivalence classes, because relevance is shared by a class. Calls back `relevantEh`, which reaches P's queues, the case split queue and T. |
| `CaseSplitQueue` | P | Receives `relevantEh` (used by the relevancy-based queues, which the Verus preset selects). Uses `isExtDiseq` only when the `d_lookaheadDiseq` parameter is set; it is off by default. |
| `ConflictResolution` | split | First-UIP goes to P; the proof-forest explainer goes to T (section 4.5). |
| `DynAckManager` | T | Lemma clauses with a deletion hook, the conflict count, a hook after each conflict, and marking relevance. |
| `Setup` (auto configuration) | S | Runs once, at the first check or push. Chooses P's heuristics (phase, restarts, initial activity) and the relevancy level from features of the input, and registers T's plugins. |

## 6. The two open allocations

### Relevancy: owned by the propositional side

**Why P.**

- Its main input is P's assignment, read through `findAssignment` at about
  ten places on the hot path.
- Its rules follow the Boolean gate structure.
- Its scopes are search scopes.
- Most of the sources that mark relevance are P's clause machinery: BCP for
  lemmas, `reinitClauses`, `reassertUnits` and `restoreRelevancy`.
- It decides which assignments reach T, through the gate in `assignCore`.

Placing it with T would instead move all of those Boolean reads, and the
gate, across the boundary.

**What T needs from it.**

- Querying and marking relevance (`isRelevant`, `markAsRelevant`), which are
  hot in MAM. These are direct calls, not virtual ones.
- Installing handlers and dependencies (`addRelevancyEh`,
  `addRelevancyDependency`, `addRelWatch`).
- The `relevantEh` notification.

**What it needs from T.**

- The members of an equivalence class, for marking a whole class.
- The `relevantEh` sink. Today a single `SmtContext::relevantEh` fans out to
  P's atom queue, the case split queue, the quantifier manager and the
  theories, in that order. That order is part of the behavior and must be
  kept. The audit did not establish whether it is required for correctness.

**Re-entrancy.** A call to `markAsRelevant` from anywhere (a theory, MAM, BCP
or `addEq`) synchronously re-enters both sides. The extraction must allow
that re-entrancy unchanged. Queueing the events would change the order of
marking.

### Internalization: split as CNF conversion and pre-registration

**P owns:** Boolean variables, the gate constraints (`mkNotCnstr` …
`mkIteCnstr`), root clauses, the handling of asserted roots in
`internalizeAssertion` and `assertDefault`, the clause store with its reinit
and internalization-level bookkeeping, and the relevancy watches installed
for gates (R).

**T owns:** enodes, terms, theory atoms, equality and distinct atoms,
quantifier registration, `applySortCnstr`, `attachThVar`, generations, and
the check that a theory is supported.

**Where they meet:**

- **A Boolean formula used as a term.** It needs an enode and the
  true/false-merge flag (`setMergeTf`). This is T registering a variable
  that P owns.
- **Term ITEs** (`internalizeIteTerm`). These are T, using P's clause API.
- **Assertions made during the search.** Instances, theory axioms and
  dynamic Ackermann go through P's API for asserting formulas and clauses at
  the current scope.

## 7. Shared infrastructure that remains shared

| Infrastructure | Why it is shared | Treatment |
|---|---|---|
| `TrailStack` | One LIFO undo log for both sides. Its order fixes the order of undo between E-graph merges, `mkBoolVar` and theory trail entries. | Keep one log, owned with the scope levels and driven by P's push and pop, as `context::Context` is in cvc5. List it as a remaining dependency. |
| `Region` | Justifications, relevancy handlers and quantifier statistics are allocated with the lifetime of a scope. | Keep it shared, with P driving its push and pop. |
| Scope levels: `d_scopeLvl`, `d_baseLvl`, `d_searchLvl` | P sets them. T reads them for internalization levels, the cost function and the arithmetic equality adapter. | P owns them; T reads them. |
| `Params`, `Statistics` | Setup and the counters span both sides. | Keep them in `SharedBackend`. Plugin statistics should eventually move to the plugins. |

## 8. Proposed extraction sequence

Each step is a reviewable change that does not alter behavior. The check for
each step is the one used in Stage 1A: identical answers and identical
`z3::` counters on the local comparison set (444 quantified regressions under
both presets; runs that time out excepted), identical results under
`--rlimit`, the `regress0/z3` tests, and the benchmark comparison.

1. **Remove dead paths.** *Done; see FIDELITY.md, "Imported code retired
   before the propositional/theory split".*
   - Theory case splits (`mkThCaseSplit`, `propagateThCaseSplit` and their
     three fields).
   - `mkThLemma`, `addTheoryAwareBranchingInfo`, `hasCaseSplits`,
     `hasThJustification` and `CaseSplitQueue::internalizeInstanceEh`.
   - `d_incompleteTheories`, which is written but never read.
   - The `Theory` hooks the core never calls.
   - The unused `d_watches` parameter of `ConflictResolution`.

   This makes the boundary smaller before anything moves.
2. **Extract the explainer.** Move `justification2Literals` and `eq2Literals`
   out of `ConflictResolution` into a T-side class. Conflict analysis then
   reaches the E-graph through a single call. *Done: `z3::Explainer` in
   `explainer.{h,cpp}` owns the marking interface, the caches of explained
   justifications and equalities, and the proof-forest walk. Conflict
   resolution calls `explain`, `getCheckpoint` and `rollback`, and no longer
   reads an enode. `Justification::getAntecedents` takes the explainer.*
3. **Extract the theory status.** `d_unsupported`, `d_modelUnsoundTheories`
   and the reasons for a theory giving up become one T-side object that
   `checkFinalize` consults. *Done for the first two:
   `z3::TheoryStatus` in `theory_status.{h,cpp}` holds them and decides,
   through `canConfirmModel`, whether an assignment may be reported as a
   model. The reasons a theory gives up are still set in `finalCheck` and
   `restart`, which mix the two sides; they move with the driver in step
   4(b).*
4. **Extract the Boolean engine into `z3::PropCore`.** This is the largest
   step, so it should be done in two commits:
   - (a) Move P's state and its leaf methods: assignment, watches, clause
     store, `bcp`, the backtracking of clauses, simplification and GC.
     `SmtContext` keeps forwarding methods for the 20 or so Boolean methods
     that plugins use, so the plugins do not change.
   - (b) Move the driver (`search`, `boundedSearch`, `propagate`, `restart`,
     `decide`, `resolveConflict`) into `PropCore`. It calls `SmtContext`
     through the scheduling and backtracking contract of sections 4.6
     and 4.8.

   `SmtContext` is then the theory side. It can be renamed, which is
   cosmetic.

   *4(a) done: `z3::PropCore` in `prop_core.{h,cpp}` owns the Boolean
   variables and their data, the assignment, the watches, the clause store
   with its reinitialization and delayed units, the conflict, the activity
   and phase heuristics, the case split queue and the scope levels, together
   with the methods on them: `mkBoolVar`, `assign`, `bcp`, `mkClause`,
   `simplifyClauses`, the lemma GC and `guess`. The method bodies moved
   unchanged. `SmtContext` holds it as the member `d_prop` and keeps
   forwarders under the same names, so neither the plugins nor the theory
   side's own code changed. `PropCore` calls the theory side only for the
   services listed in its class comment. `pushScope` and `popScopeCore`
   still sequence both sides, calling `PropCore` for its part at the same
   point as before. The justification limit of a scope is now kept by
   `SmtContext`.*

   *4(b) done: `PropCore` now holds the search driver as well:
   - `search`, `boundedSearch`, `propagate`, `restart`, `decide` and
     `resolveConflict`;
   - the conflict resolution object, and the restart, GC and conflict
     counters;
   - the cancel flag and the failure reason;
   - the push and pop of scopes.*

   *`SmtContext` keeps the entry points (`check`, `push`, `pop` and the input
   queue). It answers the driver through a scheduling and backtracking
   contract:*
   - *`theoryPropagate` and `hasPendingTheoryWork` for the propagation
     fixpoint;*
   - *`finalCheck`, which now reports its failure reason to the driver instead
     of setting it;*
   - *`initSearchEh`, `restartEh`, `checkModel`, `notifyConflictResolved` and
     `clearPropagationQueues`;*
   - *`pushTheoryScope`, `popTheoryScopeBegin` and `popTheoryScopeEnd`.*

   *To group the theory side's steps, three were reordered relative to
   Z3's:*
   - *The case split queue is pushed before the theory side, rather than
     between the fingerprints and the theories.*
   - *The quantifier manager is popped after the propositional side's
     clauses, rather than before them.*
   - *The theory side's `initSearchEh` runs before the propositional side's
     counters are reset.*

   *Each of these touches only its own state. The comparison confirms it:
   answers and counters are unchanged. The fields `d_lastSearchResult`,
   `d_searchFinalized` and `d_numSimplifications` were never read and are
   removed.*
5. **Give relevancy an owner.** `RelevancyPropagator` becomes a component of
   `PropCore`, with an explicit interface to T: the members of a class and
   the `relevantEh` sink. The order of the fan-out is preserved.
6. **Split internalization** along section 6. Theories register atoms
   through one call instead of five low-level ones.
7. **Wire the ownership.**
   - `Z3PropEngine` owns `PropCore`.
   - `Z3TheoryEngine` owns the theory side.
   - `SharedBackend` shrinks to the shared infrastructure of section 7.
   - Each remaining dependency that crosses the boundary is recorded in the
     progress record.

   This completes Stage 1B.

During Stage 1B the calls across the boundary stay non-virtual and inlinable.
Several of them are on the hottest paths: `assign`, `getAssignment`,
`isRelevant`, and the atom queue. The contract of each side is its documented
public API. Abstract interfaces should wait until a second implementation
exists; for the propositional branch, cvc5's `CDCLTSatSolver` interface is
the candidate.

## 9. Defects and inconsistencies found

None of these is a refactoring step. Each should be fixed in a change of its
own, so that its effect on the comparison can be seen.

1. **`nonGroundInternalize` asserts a proxy equality during the search.** It
   adds `z3proxy = e` to `d_assertedFormulas`, which has no scoping (see
   FIDELITY.md). On backtracking, the Boolean variables and clauses of the
   proxy are undone, but the proxy is never re-internalized. Its only caller
   is `Theory::mkLiteral`, from `TheoryDatatype`. Whether the path can be
   reached is unclear.
2. **`d_unknown` is never reset.** A later check can report a stale reason.
   It is printed only at verbosity 1.
3. **The theory status is sticky.** The records in `TheoryStatus` are
   never cleared within a context, so a mark that a theory makes on one
   branch persists through later branches and checks. This only weakens a
   result to unknown, but it is not scoped.
4. **The `attachThVar` comment disagrees with the code.** The comment says
   `newEqEh` and `newDiseqEh` may fire before the method returns; the code
   only queues them.
5. **`GomoryCutJustification::getFromTheory` has no effect** on the delivery
   of assignments, because only `mergeTheoryVars` reads it.
6. **`Cvc5Bridge` tags every justification as `THEORY_ARITH`**, including
   for bit-vectors.
7. **README.md is stale on unfired patterns.** It says that a pattern which
   will never fire leads to a call to `markModelUnsound`. No such call
   exists. It is harmless, because `checkModel` never confirms sat when the
   input has quantifiers.
8. **The setup can register no theories.** If the context is already
   inconsistent at the first check, `setupContext` returns before
   registering any. This may be faithful to Z3; it has not been checked.

# Audit: the propositional branch against cvc5's propositional engine

Date: 2026-10-13

Source snapshot: `40697de526` (end of Stage 1B)

Status: audit only. No code changed.

After Stage 1B, Z3's Boolean search is `z3::PropCore`. It sits behind
`Z3PropEngine`, and drives the theory side, `z3::SmtContext`, through an
explicit contract. This document:

- maps each part of `PropCore` onto cvc5's propositional engine;
- names the architectural differences that matter;
- proposes experiments in an order where each one attributes the port's
  performance to a single component, starting with those that need no code.

It is the first step down the propositional branch of section 12 of
[ARCHITECTURE_PLAN.md](ARCHITECTURE_PLAN.md).

Two notes on the cvc5 side apply throughout:

- **Default engine.** Unless stated otherwise, "cvc5" means the native engine
  on a quantified logic with default options: CaDiCaL as the CDCL(T) solver
  (MiniSat with `--incremental`), the justification decision heuristic, and
  `--inst-when=full-last-call`. The baseline used so far for comparison adds
  `--user-pat=strict --no-cbqi`.
- **Presets.** "Under the Verus presets" means `--z3-preset=verus` or
  `verus-best`. These turn auto configuration off, so `Setup`'s per-logic
  overrides do not apply. They select:
  - the relevancy case split queue and relevancy level 2;
  - delayed units;
  - an eager instantiation threshold of 100;
  - the parameter defaults: in-out geometric restarts with an initial
    threshold of 100 and a factor of 1.1, and conservative phase caching.

## 1. Component map

| `PropCore` part | The port (Z3) | cvc5 | Difference that matters |
|---|---|---|---|
| Variables, assignment, BCP | Two watched literals. Binary clauses are kept in the watch lists. Clauses are auxiliary (scope-local) or lemmas. | MiniSat or CaDiCaL. | Mechanical. |
| Lifetime of atoms | **Scoped.** A Boolean variable or enode made at scope *n* is deleted when *n* is popped. Lemmas over deleted atoms are re-internalized (`reinitClauses`), and the generations of their terms are cached and restored. | **Persistent** until a user pop. `TheoryPreregistrar::notifyBacktrack` re-preregisters literals made above the backtrack level, but the SAT variable and its clauses survive. | Fundamental (I2). |
| Lifetime of theory clauses | Theory axioms and **quantifier instances** are auxiliary clauses at the current scope, **deleted on backtracking**. Fingerprints are scoped, so an instance is re-derived when matched again. `CLS_TH_LEMMA` and learned clauses live until GC. | Every theory lemma, **including instances**, is permanent: nothing outside `src/z3` sets `LemmaProperty::REMOVABLE`. Only learned clauses and explanation clauses are reduced. | Possibly large for quantifiers (I1). |
| Explanations | Eager. A propagation carries a `Justification` object made at propagation time; `Explainer` expands it during conflict analysis. | Lazy. `TheoryProxy::explainPropagation` is called on demand from conflict analysis and minimization (MiniSat `reason()`, CaDiCaL `cb_add_reason_clause_lit`). | Mechanical, but required for hosting (I6). |
| Conflict analysis | First UIP with minimization. Dynamic Ackermann hooks on used congruences. | First UIP with deep minimization; minimization asks for lazy explanations. | Comparable. |
| Decisions | Case split queue. The default is activity-delay-new; **the Verus presets use the relevancy queue**. Phase: conservative caching by default, always-false under AUFLIA auto config. Random initial activity while searching. Theory phase hints. | **Justification heuristic.** It walks the input assertions and lemmas, decides the first unjustified atom with the polarity that satisfies the formula, and stops the search on a partial assignment once everything is justified. VSIDS and phase saving are largely bypassed under it: a decision from the decision engine keeps its own polarity unless a theory froze the phase. | Probably significant (I5). |
| Restarts | In-out geometric (100, 1.1) under Verus; geometric 1.5 under AUFLIA auto config; Luby for QF_UF; adaptive agility. A restart with a model runs the quantifier `checkModel`. | MiniSat: Luby, 25·3^k (`--restart-int-base`, `--restart-int-inc`). CaDiCaL: its own policy, not exposed. | Tunable. |
| Clause GC | Two strategies: delete half by activity, or an old/new split with a count of unassigned literals. Run at restarts or every so many conflicts. | MiniSat `reduceDB`: half by activity of the removable clauses, by clause count. Theory lemmas are never reduced. | Interacts with I1. |
| Base-level simplification | Deletes satisfied clauses at the base level, including lemmas. | MiniSat removes only satisfied removable clauses. | Minor. |
| **Relevancy** | **Three roles** (section 2, I3). | **No counterpart.** The nearest are the justification heuristic's partial assignment; `--term-db-mode=relevant-all-delay` (the default), which restricts E-matching to terms in asserted facts; and the `RelevanceManager`, which is computed only after a full assignment and only with `--relevance-filter`. | Fundamental (I3). |
| Scheduling of theory work | After every BCP fixpoint: atoms, equalities, theories, then **E-matching and instantiation in the quantifier manager**. Instances below the eager threshold are made during propagation; the rest wait for the final check. | STANDARD checks run after every BCP fixpoint, but **no native module instantiates at STANDARD effort**. E-matching runs at FULL (alternate rounds) and at LAST_CALL. | Probably significant (I4). |
| Encoding of the Boolean structure | Gates are encoded as the theory side's walk meets them, with relevancy watches. A formula in a term position gets an enode merged with true or false. The input is flattened first (`pushAssertion`: top-level conjunctions split, ITEs and simple distributions turned into clauses). | `CnfStream` (Tseitin) over the preprocessed input. Boolean terms are purified by term formula removal. Atoms are preregistered eagerly by default. | Shapes relevancy and decisions. |
| Delayed units | A unit learned deep in the search is reasserted after each backtrack instead of jumping to the base level. On under Verus. | MiniSat jumps to the level where a lemma becomes unit. CaDiCaL re-notifies fixed theory literals after backtracking. | Tunable. |
| Dynamic Ackermann | Theory side, run after each conflict. | None; only static `--ackermann`. | Theory branch. |

## 2. High-level issues

**I1. Instances are scope-local in Z3 and permanent in cvc5.** The port
deletes a quantifier instance when the scope it was made in is popped, and
makes it again when E-matching finds it again. cvc5 keeps every instance for
the rest of the user scope. These are opposite trade-offs:

- *Z3:* a smaller clause database and propagation over current instances, at
  the cost of rediscovering instances after backjumps.
- *cvc5:* no rediscovery, at the cost of a growing set of permanent clauses.

Nothing measured so far separates their effect.

**I2. Atoms are scope-local in Z3 and persistent in cvc5.** The
re-internalization machinery exists for this: `reinitClauses`, the lemma's
saved atoms, the generation cache and `reassertUnits`. A cvc5 SAT solver
cannot host the theory side unchanged. Either the theory side stops relying
on atoms disappearing on backtrack, or the host emulates it. It is also why
the generation cache crosses the boundary (Stage 1B dependency 8).

**I3. Relevancy is a filter between the two sides, with three roles.** Under
the Verus presets all three are active:

1. **Delivery.** At level 2, only relevant assigned atoms reach the theories
   and the quantifier manager (`assignCore`, `relevantEh`).
2. **E-matching.** The matching engine considers only relevant enodes; there
   are about a dozen `isRelevant` tests in `mam.cpp`, and the checkers have
   more.
3. **Decisions.** The relevancy case split queue branches on relevant
   atoms.

cvc5 has nothing that plays roles 1 and 3 at the SAT level. Role 2 is
approximated by `--term-db-mode`. This is the strongest single candidate for
explaining a difference in E-matching behavior. The existing switches cannot
separate the roles, because relevancy below 2 also forces the activity case
split queue (`mkCaseSplitQueue`).

**I4. Instantiation happens during propagation in Z3, and at full or last
call in cvc5.** The port runs E-matching after every BCP fixpoint and
instantiates eagerly up to the eager threshold, which is 100 under Verus, so
nearly everything is eager. cvc5 instantiates only on complete or justified
assignments. This is a scheduling choice that the propositional side's
driver controls. The matching itself belongs to the theory branch.

**I5. Different decision heuristics with a similar intent.** The relevancy
queue and cvc5's justification heuristic both steer the search by the
structure of the input. They do so differently: relevancy is propagated
through gates, while justification walks the formula. Activity-based
splitting, the port's default outside Verus, is closer to plain VSIDS.

**I6. Eager versus lazy explanations.** This is mechanical: the explainer
can answer `explainPropagation` from a variable's justification. It must
still be in place before the theory side can run under cvc5's SAT solver.

**I7. What hosting under cvc5's `PropEngine` requires.** The next
architectural level (plan, section 12) puts native propositional
orchestration over the port's theory side. That needs:

- I2 resolved, and I6 implemented;
- a policy for I1 and I3;
- the Stage 1B dependencies 1–5 removed: the combined allocation,
  `ConflictResolution` and `CaseSplitQueue` holding the theory-side handle,
  and the shared infrastructure.

## 3. Proposed sequence

Each step changes one thing against a fixed baseline. Use both
`verus-best`, the one that solves benchmarks, and `verus`, the one to compare
with Z3. These change the search, so counters will differ. Compare solved
counts, per-benchmark times and the `z3::` counters that explain the change
(instances, conflicts, decisions, matches).

### Phase A: measure the switches that already exist (no code)

| Experiment | Switch | Isolates | Note |
|---|---|---|---|
| A1 | `--z3-case-split=activity`, and separately `activity-delay-new` | the decision heuristic (I5) | Under Verus the baseline is the relevancy queue. |
| A2 | `--z3-relevancy=0 --z3-case-split=activity`, compared with A1 | relevancy's delivery and E-matching roles (I3, roles 1 and 2) | A1 is the control, since relevancy below 2 forces the activity queue. |
| A3 | `--z3-phase-selection=always-false`, and `caching` | the phase | |
| A4 | `--z3-restart-strategy=luby` (try `--z3-restart-initial=25`) | the restart policy | Closest to MiniSat's; the port has no counterpart of `--restart-int-inc`. |
| A5 | `--z3-delay-units=false` | delayed units | |
| A6 | `--z3-qi-eager-threshold=0 --z3-qi-lazy-threshold=100` | when instances are made (I4) | Close to cvc5's final-check-only instantiation, without its alternation of rounds. The lazy threshold must be raised with it: a delayed instance whose cost is above the lazy threshold (20 by default) is never made. An instance the checker finds in conflict is still made eagerly (`d_qiPromoteUnsat`). |

These take an afternoon of benchmark time and split the Boolean side's
contribution into its parts before anything is written.

### Phase B: small changes inside `PropCore`, each behind an option that is off by default

When an option is off, answers and counters must stay identical, as in
Stage 1B.

- **B1. Separate the roles of relevancy (I3).**
  - An option for the quantifier manager and the checkers to ignore
    relevancy, matching all enodes.
  - An option for `assignCore` to deliver every assigned atom.
  - With A2, this tells whether relevancy matters through decisions,
    delivery or matching.
- **B2. Make instances permanent (I1).** Add instances as lemmas that
  survive backtracking (as cvc5 does), and keep their fingerprints across
  pops. This tests the lifetime trade-off directly.
- **B3. A justification-style case split queue (I5).** Walk the asserted
  formulas and branch on the first unjustified atom, with the satisfying
  polarity. This is cvc5's decision behavior inside the port's search.
- **B4. A MiniSat-style policy for restarts and GC.** Luby 25·3^k, and
  removal by activity triggered by the size of the clause database.

### Phase C: native propositional orchestration over the port's theory side

Run cvc5's `PropEngine` (MiniSat first, for its determinism and its
documented restart and reduction behavior) over `SmtContext`, through a
`TheoryProxy`-compatible adapter.

- **The adapter's mapping:**
  - pre-registration goes to the theory side's internalizing walk;
  - `theoryPropagate` goes to `theoryPropagate`;
  - `explainPropagation` goes to `Explainer`;
  - `theoryCheck` at FULL goes to `finalCheck`.
- **Prerequisites:**
  1. `ConflictResolution` and `CaseSplitQueue` take `PropCore&` instead of
     `SmtContext&`.
  2. `SmtContext`'s Boolean API becomes an interface, so that the theory
     side can run over either propositional side.
  3. I2 is resolved: atoms persist, and the generation cache and
     re-internalization are no longer needed under the native host.
  4. A decision for I1 and I3. Relevancy can be kept as a component between
     the SAT solver and the theory side, so its effect can be switched on
     and off under the native host as well.

This replaces `Z3PropEngine`/`PropCore` as the highest Z3-specific layer on
the propositional branch. What remains Z3-specific on that branch are the
components deliberately kept, such as relevancy, if the measurements say so.

## 4. Reading the outcomes

- **A2 or B1 lose substantially:** relevancy filtering is a key ingredient.
  A native counterpart then needs a relevancy component between the SAT
  solver and the theories, or much stronger filtering in the term database.
- **B2 loses:** the scope-local lifetime of instances matters, through the
  size of the clause database or the economy of re-instantiation.
- **A6 loses:** eager instantiation during propagation matters. That points
  at `--inst-when` on the cvc5 side.
- **A1 or B3 lose:** the decision heuristic matters.
- **None of these matters much:** the advantage is on the theory side (the
  E-graph, the matching engine, the instantiation queue and its costs), and
  the theory branch is the one to audit next.

In each case the result is a statement about one component that can be
checked against Z3 and against cvc5, which is the purpose of the
experiment.

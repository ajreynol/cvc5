# Z3-style relevancy for cvc5's E-matching: motivation and plan

This is a handoff for implementing and testing an experiment in a new
branch. It is self-contained: you do not need the branch it came from, but
pointers to it are given where they help.

## Summary

Experiments on a port of Z3's SMT core into cvc5 show that the largest
single reason Z3 does well on Verus-style quantified benchmarks is that
**E-matching only considers terms that are relevant to the current
assignment**, in the sense of Z3's relevancy propagation. cvc5 already has
a weaker filter of the same kind, and a component, the `RelevanceManager`,
that computes nearly the right notion of relevance. The task is to connect
the two behind an opt-in option, check that the result is sound, and give
the user command lines to measure it.

## 1. Background

### Where the evidence comes from

Branch `eagerInst-z3-1` of this repository contains a port of Z3's SMT core
(`src/z3/`, enabled with `--z3`). It is used to find out which components of
Z3 make it effective on Verus benchmarks, so that cvc5 can adopt them. Its
document `src/z3/PROPOSITIONAL_BRANCH.md` (section 3, "Results") describes
the experiments. Each turns one component of the port off or replaces it
with cvc5's counterpart, against the configuration `--z3
--z3-preset=verus-best`, on the user's quantified benchmark set (60 s).

### What Z3's relevancy does

Z3 marks formulas relevant starting from roots, which are the input
assertions and every quantifier instance (Z3 asserts an instance `(or (not
q) body)` like an input formula). Relevance flows down through the Boolean
structure under the current assignment:

- for a true OR, the first true child;
- for an AND, every child;
- for an ITE, the condition and the branch it selects.

The subterms of a relevant atom become relevant. Relevancy has three roles
in Z3:

1. **Delivery:** only relevant atoms are given to the theories.
2. **Matching:** E-matching and the instance checker only consider relevant
   terms.
3. **Decisions:** the case split queue only branches on relevant atoms.

### The results

| Outcome | What was changed |
|---|---|
| no difference | phase selection; restart policy; delayed units; **delivery not filtered by relevancy**; **justification-order decisions** instead of relevancy-order |
| somewhat worse | activity decisions with delivery unfiltered; activity decisions delaying new variables |
| worse | instances kept permanently (confounded with relevancy, see below); **instance checker not filtered by relevancy** (many unknowns) |
| much worse | activity (VSIDS) decisions; relevancy off entirely; no instantiation during propagation; **E-matching not filtered by relevancy** |

What this says, role by role:

- **Matching is the key role.** Turning off relevancy for E-matching alone
  is about as bad as turning off relevancy entirely. Turning it off for the
  instance checker alone also costs; that checker skips an instance it
  judges already satisfied.
- **Delivery does not matter.** cvc5 has no counterpart and needs none.
- **Decisions must follow the formula, but justification order is as good
  as relevancy order.** cvc5's default for quantified logics is already the
  justification heuristic.
- **Instantiating during propagation matters too.** cvc5 only instantiates
  at full or last-call effort. That is a separate, larger change and is out
  of scope here.

### What cvc5 does today

cvc5's term database decides which ground terms E-matching may use,
through `TermDb::hasTermCurrent`. Under `--term-db-mode=relevant`, and the
default `relevant-all-delay`, a term is admitted if it is a subterm of any
asserted literal, or if it took part in any equality merge. The default mode
also falls back to all terms before it gives up. So cvc5 admits the terms of
every assigned literal, while Z3 admits only those of the literals the
assignment needs to satisfy the roots. A literal assigned by propagation
inside a disjunct that is not needed contributes terms in cvc5 and not in
Z3. The hypothesis to test is that this difference matters.

## 2. Goal

Add an opt-in mode in which **E-matching's term database admits only the
terms of literals that the `RelevanceManager` selects as relevant**, with
quantifier instances as relevance roots, as in Z3. Default behavior must not
change. Then measure the mode against cvc5's existing modes.

## 3. What exists in cvc5

Line numbers are as of `master` at `f02ce28e6d`; search by name if they
have moved.

**`RelevanceManager`** (`src/theory/relevance_manager.{h,cpp}`):

- It is created by `TheoryEngine::finishInit` when `--relevance-filter` (or
  difficulty) is on, and registered as a `TheoryEngineModule`.
- Its roots are the preprocessed input assertions
  (`notifyPreprocessedAssertions`), and lemmas sent with
  `LemmaProperty::NEEDS_JUSTIFY` when `--relevance-filter` is on
  (`notifyLemma`). Today only skolemization lemmas use that property in
  quantifiers (`QuantifiersEngine`, `QUANTIFIERS_SKOLEMIZE`).
- `computeRelevance` justifies every root against the SAT assignment
  (`justify`): AND and OR short-circuit in child order, the condition of an
  ITE selects its branch, and EQUAL and XOR need both sides. An atom is
  relevant (`d_rset`) when it has a SAT value that agrees with its polarity
  in the root. Atoms with no polarity, under EQUAL, XOR or an ITE condition,
  are relevant whenever assigned. This is close to Z3's notion.
- `d_rset` and the justification cache `d_jcache` are SAT-context dependent.
- `isRelevant(lit)` asserts that we are inside a full-effort check.
  `RelevanceManager::check` sets that flag when the effort is FULL, and
  `postCheck` clears it. `TheoryEngine::check` calls the modules' `check`
  before the theory loop, and runs the quantifiers engine's last-call check
  inside the same call, before `postCheck`. So relevance is available to
  quantifiers at both full and last-call effort.
- **Cost trap:** `isRelevant` calls `computeRelevance()` on every call, and
  that loops over all roots. The loop is cached per root, but it is still
  O(#roots) per query, so querying once per asserted literal is
  O(#facts × #roots).
- **Failure:** if a root justifies to false, `d_fullEffortCheckFail` is set
  and every literal counts as relevant for the rest of the check. In debug
  builds this also hits `DebugUnhandled` in `computeRelevanceFor`.
- `TheoryEngine::isRelevant` returns true when there is no relevance
  manager. Theories reach it through `Valuation::isRelevant`.
- `--relevance-filter` has few other effects: lemma roots,
  `checkTheoryAssertionsWithModel` with `--check-models`, and the nonlinear
  solver's `--nl-rlv`, which `SetDefaults` ties to it.

**`TermDb`** (`src/theory/quantifiers/term_database.{h,cpp}`):

- `d_trackRlv` is true for the `relevant` and `relevant-all-delay` modes.
- `d_has_map` is the set of admitted terms. It is SAT-context dependent,
  and `setHasTerm(n)` adds `n` and all its subterms.
- It is filled from two places:
  - `eqNotifyMerge`, around line 285, adds both terms of every merge in the
    master equality engine, during propagation;
  - `reset(effort)`, around lines 700–735, at the start of each
    quantifiers round, adds every asserted fact of every theory
    (`d_qstate.factsBegin(theoryId)`).
- `hasTermCurrent(n)` is consulted when building the term indices
  (`computeUfTerms`, `computeUfEqcTerms`), by
  `CandidateGeneratorQE::getNextCandidateInternal`, by
  `QuantConflictFind::reset_round`, and by `QuantifiersEngine::shouldRecheck`.
- `QuantifiersEngine::shouldRecheck`, around line 220, implements the
  "all-delay" fallback: when nothing else applies, it adds every term in
  the equality engine and asks for another round.

**Instantiation** (`src/theory/quantifiers/instantiate.cpp`,
`Instantiate::addInstantiationInternal`): an instance is built as
`(=> q body)`, rewritten, and sent with
`d_qim.addPendingLemma(lem, id, p, ...)`, where `p` is
`LemmaProperty::INPROCESS` (or `LOCAL`), around lines 289–345.
`LemmaProperty` supports `|`. `--inst-no-entail` (on by default) skips
instances that the equality engine entails, which is cvc5's counterpart of
Z3's instance checker.

## 4. Plan

Branch from `master`; the adapter does not depend on the Z3 port. Keep every
change opt-in.

### Step 1: options

In `src/options/quantifiers_options.toml`, add two modes to
`--term-db-mode` (names are a suggestion):

- `relevance`: admit only the terms of asserted literals that the
  relevance manager selects, and no terms from merges. There is no fallback,
  as in Z3.
- `relevance-all-delay`: the same, with the fallback of `relevant-all-delay`
  to all terms before giving up.

In `src/smt/set_defaults.cpp`, turn on `--relevance-filter` with
`SET_AND_NOTIFY` when either mode is selected, as is done for the nonlinear
relevance mode.

### Step 2: compute the relevant selection once per check

Add to `RelevanceManager` a way to compute the selection once and then
query it cheaply. For example, a flag `d_computedThisCheck`, set by
`computeRelevance` and cleared in `check()`, plus a method that returns
whether a literal is in `d_rset` without recomputing (and true if
`d_success` is false). Do not change the existing `isRelevant`, which other
users rely on.

Compute the selection at the **start** of the quantifiers round
(`TermDb::reset`), before any instance of the round is sent. Instances sent
during the round become roots immediately (`notifyLemma`), and a new
instance can be false under the current assignment, since it may be in
conflict. If relevance were recomputed after that, the root would justify
to false and the whole check would fall back to "everything relevant", or
abort in a debug build. So roots added during a check must not take part
until the next check. Either compute once per check and never again in that
check, or queue new roots in `notifyLemma` and add them in `check()`.

### Step 3: the term database

When the new mode is active:

- `TermDb::eqNotifyMerge`: do not call `setHasTerm`.
- `TermDb::reset`: for each asserted fact, call `setHasTerm` only if the
  relevance manager selects it. Reach the manager through
  `d_qstate.getValuation()` (add a method next to `Valuation::isRelevant`
  for the cheap query of step 2), or through `TheoryEngine`.
- `hasTermCurrent` needs no change if `d_trackRlv` is true for the new
  modes.
- `QuantifiersEngine::shouldRecheck`: apply the fallback for
  `relevance-all-delay` only.

`d_has_map` is SAT-context dependent and only grows within a context. A term
admitted earlier in the same context stays admitted. That matches Z3, where
relevance is monotone within a scope.

### Step 4: instances as roots

In `Instantiate::addInstantiationInternal`, when the new mode is active, add
`LemmaProperty::NEEDS_JUSTIFY` to `p` (`p |= ...`). Then the instance
`(=> q body)` is a root; with `q` true, justification goes into `body`, and
the literals that satisfy it become relevant, as in Z3.

Without this, the terms of instance bodies are relevant only if the input
needs them, and every matching chain that goes through an instance breaks.
Expect that to be much worse, but it can be measured with a third mode or a
flag, which is useful as a control.

### Step 5: statistics

Add counters (cvc5 `IntStat`/`TimerStat` in the existing statistics
objects) so that runs explain themselves:

- facts considered and facts admitted by `TermDb::reset`;
- checks in which the relevance manager failed (`d_success` false);
- time spent computing relevance;
- fallbacks taken in `shouldRecheck`.

### Later, optional variants

Do not do these in the first round, but keep them in mind:

- **All lemmas as roots,** not only instances. Z3 marks the literals of
  theory lemmas relevant, while the plan above does not admit terms that
  only theory lemmas introduce, such as datatype selectors. If the new mode
  loses on datatype-heavy problems, try this.
- **Quantifier activation by relevance.** Z3 only instantiates quantified
  formulas that are relevant and true. cvc5 instantiates every asserted one.
- **Entailment by relevant terms only.** Restrict `--inst-no-entail`'s
  entailment check to relevant terms; this was the port's second
  finding.

## 5. Soundness and completeness

- Restricting the term database only removes instances, so unsat answers
  stay sound. Check that when E-matching saturates in `relevance` mode
  without the fallback, cvc5 reports unknown and never sat. The existing
  `relevant` mode, also without a fallback, is the reference for how that
  is handled.
- A relevance-manager failure must degrade to "everything relevant", which
  is cvc5's current behavior, never to "nothing relevant".
- With assertions on, run every quantified regression in each new mode and
  compare each answer with the regression's `EXPECT`. Any sat/unsat
  disagreement is a bug.

## 6. Verification

1. Build a production build and an assertion build (for example
   `./configure.sh debug` or `--assertions`).
2. **Default unchanged:** on `test/regress/cli/regress{0,1}/quantifiers`, run
   the default mode and `--term-db-mode=relevant` before and after the
   change. Answers and statistics must be identical. Compare under a
   resource limit (`--rlimit`) rather than a time limit, so that timeouts
   compare deterministically.
3. **New modes, with assertions:** run the same regressions with
   `--term-db-mode=relevance` and `relevance-all-delay`. Report wrong answers
   and crashes, and check any crash against the default mode before
   attributing it to the change.
4. **A targeted example:** write a small benchmark in which a trigger term
   occurs only in a disjunct that is assigned but not needed, for example
   `(or A (P (f c)))` with `A` true and the disjunct assigned by
   propagation. Show, with the new counters or a trace, that `(f c)` is not
   admitted in the new mode and is admitted in `relevant` mode. Add it as a
   regression test.
5. `ctest -R regress0/quantifiers` (or a sample of it) passes, and the new
   options appear in `--help`.

## 7. Measurements for the user to run

The user runs benchmarks on their own machine. Give them command lines,
one per line, in this format:

```
solve_dir_rec_par_cvc5 -t 60 ajr-cvc5 cvc5_solve.sh quant-<prefix>-<config>-cvc5 -q --user-pat=strict --no-cbqi <options>
```

Ask the user for `<prefix>` (they have used `101326-5`). Always use
`--user-pat=strict --no-cbqi` as the cvc5 baseline; that is the user's
standing instruction for these comparisons. All runs use the binary built
from the new branch, so they include its own baseline:

| config | options |
|---|---|
| `cvc5base` | (none) |
| `tdbrel` | `--term-db-mode=relevant` |
| `tdball` | `--term-db-mode=all` |
| `rlv` | `--term-db-mode=relevance` |
| `rlvdelay` | `--term-db-mode=relevance-all-delay` |
| `rlvnoinst` | `rlv` without instances as roots (the control of step 4), if implemented as a flag |

Reading them:

- **`rlv` or `rlvdelay` clearly better than `cvc5base`:** the port's matching
  advantage carries over, and the mode is a candidate default for quantified
  logics.
- **About the same:** check whether `tdball` is close to `tdbrel`. If cvc5's
  own filter barely matters on these benchmarks, the advantage needs
  something else from Z3, most likely instantiation during propagation.
- **Worse:** look at the failure and fallback counters, at `rlvnoinst`
  (relevance missing from instances), and at problems where theory lemmas
  introduce the terms matching needs (the "all lemmas as roots" variant).

## 8. Working agreements

- The user does the benchmarking and decides on performance; implement,
  verify soundness, and hand over command lines.
- Do not commit or push unless the user asks.
- The point is to learn which component matters, more than to win every
  benchmark. Keep the change minimal and the switches orthogonal, so that
  each run changes one thing.
- Follow cvc5's code style and run `clang-format` on changed files.

## References

- Branch `eagerInst-z3-1`: `src/z3/PROPOSITIONAL_BRANCH.md`, section 3, has
  the experiments and results summarized above. The relevancy switches are
  `--no-z3-relevancy-match` (E-matching), `--no-z3-relevancy-check` (instance
  checker) and `--no-z3-relevancy-deliver` (delivery).
- Z3's relevancy in the port: `src/z3/relevancy.{h,cpp}`, and
  `PropCore::assertRoot` and `PropCore::assignCore` in `src/z3/prop_core.cpp`.
- cvc5: `src/theory/relevance_manager.{h,cpp}`,
  `src/theory/quantifiers/term_database.cpp`,
  `src/theory/quantifiers/instantiate.cpp`,
  `src/theory/quantifiers_engine.cpp` (`shouldRecheck`),
  `src/theory/theory_engine.cpp` (`check`, `finishInit`).

# Proposal: `--z3-replay`, trusted confirmation of the port's unsat answers

Date: 2026-10-15

Branch: forked from `eagerInst-z3-1` (at `1ca8138236` plus the warning fixes
that followed it).

Status: proposal, not implemented.

## 1. Why

Every answer of `--z3` comes from untrusted code: the ported core
(E-graph, theories, quantifier stack, `PropCore`) and the code that
integrates it with cvc5 (the hosted engine, `HostCore`, the theory slots of
Stage 3). Nothing checks an "unsat".

This mattered concretely. Stage 3 (`--z3-theory-engine=cvc5`,
ARCHITECTURE_PLAN.md section 16) first appeared far better than both the
port's own search and the hosted engine:

| 10 s, `verus-best` | port's own search | hosted (host3) | Stage 3, first version |
|---|---|---|---|
| Development set (88 hard Verus benchmarks) | 87 in 169 s | 74 in 280 s | 88 in 92 s |
| Every tenth benchmark of `quant-07-25` (613) | 586 | 572 | 612 |

The gain came from a soundness bug. `TheoryEngine`'s sharing machinery
asked the core to explain literals that cvc5 had asserted (assumptions).
The core answered with empty explanations, so the reason clauses CaDiCaL
learned dropped assumptions: 60,760 times on 76 of the 88 benchmarks. It is
fixed (ARCHITECTURE_PLAN.md section 16, "Progress").

None of the checks run at the time caught it:
- the quantified regressions with assertions on gave no wrong answers;
- no declared status was contradicted, since the Verus benchmarks are all
  unsat;
- every literal of every explanation was true in cvc5's assignment.

It took a step-by-step comparison of two searches to find it.

`--z3-replay` settles this kind of question for good, for any configuration
of the port: an unsat answer is confirmed by cvc5's own solver, or reported
as unknown.

## 2. The idea

Under `--z3-replay`:

1. `SetDefaults` turns `--z3` off for the main solver, which is then plain
   cvc5.
2. At each `check-sat`, the main solver gives its preprocessed assertions to
   a subsolver with `--z3` on (and the user's other options, such as
   `--z3-preset` and `--z3-theory-engine`).
3. If the subsolver answers unsat, the main solver asks it for the
   instantiations it made, as pairs (quantified formula, term vector).
4. The main solver adds the instantiation lemma `q => q[x := t]` for each
   pair, through its own quantifiers engine (`Instantiate::addInstantiation`),
   and solves natively.
5. The answer is the main solver's:
   - unsat: confirmed;
   - unknown, or a timeout: unconfirmed, reported as unknown;
   - sat: the port answered unsat on a satisfiable problem, a bug to report
     loudly.

**The trust argument is simple.** The main solver only ever adds lemmas of
the form `q => q[x := t]`, where `q` is a quantified formula it has
asserted and the lemma is built by its own instantiation code. Such a lemma
is valid for any terms `t`. A mistake in the port, in the recording of
instantiations, or in the mapping back to the main solver's quantified
formulas can therefore only make the replay fail to confirm. It can never
make it confirm a wrong unsat.

Two consequences:
- **Terms the main solver does not know are harmless.** Examples are the
  port's skolems (`z3sk`) or its names for quantified subformulas
  (`z3name`). Instantiating with them is valid, merely useless, since they
  act as fresh constants.
- **Only instantiations need replaying.** The port's other lemmas (theory
  axioms, dynamic Ackermann lemmas, splits on equalities between shared
  terms) are re-derived by cvc5's own theories, or are tautologies.

The port has no proofs or unsat cores, so it reports every instantiation it
made, not just the useful ones. That is sound, since each lemma is valid,
just larger. The main solver's own unsat core can say afterwards which
instantiations mattered.

## 3. Prior art in this tree

- **`theory/quantifiers/inst_strategy_sub_conflict.cpp`** does the main half
  of this already, at a quantifiers-module level. It:
  - calls a subsolver on the asserted literals;
  - takes `getRelevantQuantTermVectors` from it on unsat;
  - replays each pair through `Instantiate::addInstantiation`;
  - skips quantified formulas the main solver does not have, noting that
    "there is no strong guarantee that our preprocessor will preserve the
    shapes of all quantified formulas".

  Follow it.
- **`smt/smt_driver.{h,cpp}`**: `SmtDriver` implements a check-sat on top of
  the SMT solver. `SmtDriverSingleCall` preprocesses, asserts and checks
  once; `SmtDriverDeepRestarts` (`smt/smt_driver_deep_restarts.cpp`) does
  more. `SolverEngine::finishInit` (`smt/solver_engine.cpp`, around line
  210) picks the driver from the options.
- **`theory/smt_engine_subsolver.h`**: `initializeSubsolver` and
  `SubsolverSetupInfo`, for a subsolver with modified options and an
  optional time limit.
- **`SolverEngine::getInstantiationTermVectors(map)`** already forwards to
  a "status solver" (`SolverEngineState::getStatusSolver`) when another
  `SolverEngine` produced the last answer.

## 4. Design

### 4.1 Option and defaults

- `--z3-replay` (z3 options, expert, bool).
- `SetDefaults::setDefaultsPre`: if `z3Replay` is set, turn `z3` off for
  this solver (`SET_AND_NOTIFY`) and remember that the driver must run the
  port as a subsolver. `checkZ3Capabilities` does not apply to the main
  solver, which is ordinary cvc5. The subsolver gets the original options
  with `z3` on and `z3Replay` off.
- `SetDefaults` also resets `--ee-mode=none` for solvers that are not
  `--z3 --z3-theory-engine=cvc5`, so a main solver copied from Stage 3
  options is fine.

### 4.2 The driver

A new `SmtDriverZ3Replay` (`smt/smt_driver_z3_replay.{h,cpp}`), selected in
`SolverEngine::finishInit` when `z3Replay` is set. Its `checkSatNext(ap)`:

1. `d_smt.preprocess(ap)`, as the single-call driver does.
2. Run the subsolver on the preprocessed assertions (`initializeSubsolver`,
   then `assertFormula` for each, then `checkSat`). Give it a share of the
   time limit; the main solver needs the rest.
3. If the result is not unsat, answer unknown. (Or fall back to native
   solving, as an option; not needed for the experiment.)
4. If unsat:
   1. take `getInstantiationTermVectors` from the subsolver;
   2. hand the pairs to the replay module (4.4);
   3. `d_smt.assertToInternal(ap)`, then `d_smt.checkSatInternal()`.
5. Map the result as in section 2. Count and trace:
   - pairs received, and pairs whose quantified formula is not one of the
     main solver's;
   - lemmas added;
   - the replay time.

A trace or warning such as `z3-replay: confirmed / unconfirmed / REFUTED`
makes the runs easy to read.

Preprocessing runs twice: in the main solver, then in the subsolver on
already preprocessed input. The pairs come back keyed by the subsolver's
input, which is the main solver's preprocessed assertions, only if the
second preprocessing leaves quantified formulas unchanged. Check this
first, for instance by comparing the subsolver's `-o post-asserts` with its
input on the Verus sample. It is likely, since the passes have already run
once, but not guaranteed (quantifier rewriting, term formula removal). If it
fails often, record which input formula each quantified formula came from,
or skip the subsolver's preprocessing.

### 4.3 The port: recording instantiations

**Where instances are made.** Every instance goes through
`InstancePolicy::mkLemma` (`z3/instance_policy.cpp`), whichever made the
match: the MAM, the quick checker, or enumerative instantiation. It knows
the port's quantifier `q` and the bindings, enodes whose `getExpr()` are
terms of the port's E-graph. Record `(q, terms)` there, without duplicates.
`QuantifierManager` (`z3/quantifier_manager.{h,cpp}`) is a natural owner of
the record. Record every instance made, including those undone by
backtracking: the refutation may depend on them through learned clauses.

**Serving the query.** `SolverEngine::getInstantiationTermVectors` under
`--z3` must reach the record. Today it asks cvc5's quantifiers engine, which
has seen nothing. Where the port's state lives depends on the mode:
- `Z3TheoryEngine::getBackend()` for the port's own search and the hosted
  engine;
- `SlotBackend::getBackend()` (`z3/theory_slot.h`) for Stage 3.

Both lead to `SmtContext::getQuantifierManager()`. A small accessor on the
theory engine or the engine factory, used by `SolverEngine` when `--z3` is
on, is enough. `--dump-instantiations` stays refused for users.

**Mapping the port's quantifiers back to the input.** The pairs must name
quantified formulas of the subsolver's input. The port instantiates its own
prepared versions, built by `AssertionPreparation::apply`
(`z3/assertion_preparation.cpp`). Per assertion, it runs:
- `Nnf::convert` (`z3/nnf.*`), negation normal form with skolemization:
  - an existential in a positive position becomes skolem terms (`z3sk`);
  - a negated universal becomes an existential, and so on;
  - a quantified subformula below an atom is replaced by a Boolean name
    (`z3name`) with a definition, asserted separately.
- `AssertionRewriter` (`z3/ast.h`), which rewrites ground parts with cvc5's
  rewriter and rebuilds a quantifier from its rewritten body. It
  deliberately avoids cvc5's quantifier rewriter, so no miniscoping,
  variable elimination or prenexing: the bound variables survive in order.
- `NgPushAppIte` (`z3/push_app_ite.h`), Z3's lifting of term ITEs.
- `ConnectiveNormalizer`.
- `QuantifierNormalizer` (`z3/ast.h`), which renames bound variables to
  canonical ones by de Bruijn level, so that alpha-equivalent quantifiers
  become the same node. The map is many-to-one: any of the originals can be
  used for the replay.
- `PatternInference` (`z3/pattern_inference.*`), which adds patterns and
  sometimes weights.
- `AssertionRewriter` again.

For a universal at the top of an assertion, the variables keep their order,
so the term vector maps positionally. Two ways to build the map, from
simple to exact:
- **Structural pairing:** pair the quantified subformulas of each input
  assertion with those of its prepared form in the same traversal order
  (and polarity), and check that the numbers and types of variables agree.
- **Provenance through the passes:** each pass that rebuilds a quantifier
  records old node to new node, and the maps are composed. This is precise,
  and handles the definitions NNF adds for named quantifiers.

**Two cases to leave for later and only count at first:**
- **Nested quantifiers.** A quantifier inside an instance body is
  instantiated as part of that instance: `SmtContext::internalizeInstance`
  normalizes the body (`z3/smt_context.cpp`). Its counterpart in the main
  solver is the nested quantifier inside the main solver's own instance of
  the outer one. Replaying it needs the parent pair and the position of the
  nested quantifier.
- **Existentials the port skolemized.** Their instances have no counterpart;
  only the skolem terms that appear in other term vectors matter, and those
  are harmless, as said in section 2.

### 4.4 The main solver: the replay module

A quantifiers module, `InstStrategyZ3Replay`, registered in cvc5's
quantifiers engine when `--z3-replay` is on. It holds the pairs the driver
handed over. At its first check (standard effort is fine), it calls
`Instantiate::addInstantiation(q, terms, InferenceId::QUANTIFIERS_INST_Z3_REPLAY)`
for each pair whose `q` is asserted, as `InstStrategySubConflict` does, and
then does nothing more. Going through `Instantiate` builds the lemma with
cvc5's own code and preprocesses it like any other lemma. Add the new
`InferenceId`.

Whether the main solver should also do its own E-matching is a choice.
- **On:** it confirms more, and stays trusted.
- **Off** (`--no-e-matching` in the experiment): a confirmation then means
  the port's instances suffice, which is the cleaner reading for
  attribution.

Make it an option of the experiment.

## 5. Stage A, if a quicker check is wanted first

A weaker replay, at the level of the port's prepared assertions:
- **What the subsolver hands back:** its prepared assertions and every
  instance lemma `(or (not q') body')` as formulas.
- **What the main solver checks:** that these are unsatisfiable with
  instantiation off, the quantified formulas being treated as opaque.

This trusts `AssertionPreparation`, which is mostly cvc5's rewriter and
negation normal form, and needs no mapping. It does check the whole search,
which is the part Stage 3 changed. It is about a day of work and could ship
as `--z3-replay=prepared` before the trusted mode.

## 6. Steps and acceptance

1. **Plumbing:** the option, the defaults, and the driver with a subsolver
   but no replay (step 4 of 4.2 skipped). Native configurations are
   unchanged. `--z3` without replay is unchanged (identical answers and
   `z3::` counters on the comparison set: the 447 quantified regressions
   with both `default` and `verus-best`, timeouts compared under `--rlimit`).
2. **Recording and serving** the port's instantiations, with the mapping for
   top-level quantifiers. Report the share of pairs mapped, on the Verus
   sample.
3. **The replay module.** Measure the confirmation rate on the quantified
   regressions and on the 613-benchmark sample, for each mode:
   - the port's own search (`--z3 --z3-preset=verus-best`);
   - hosted (`--z3-prop-engine=cvc5`);
   - Stage 3 (`--z3-theory-engine=cvc5`).

   Also measure the time the replay adds.
4. **Nested quantifiers and skolem translation,** if the confirmation rate
   calls for them.

Acceptance:
- **Never wrong:** with `--z3-replay`, an answer is unsat only if cvc5's own
  solver found it.
- **Bugs reported:** any "sat" from the main solver after a port unsat is
  reported as a bug.
- **Coverage measured:** the confirmation rate is reported per mode.

## 7. What to look for

- **The confirmation rate per mode,** and how it moves when the port
  changes. A change that raises the solved count but lowers the
  confirmation rate deserves the suspicion the first Stage 3 results
  deserved (section 1).
- **A "sat" from the main solver** is the strongest signal. Keep the
  benchmark, the subsolver's options and the pairs, for a reproduction.

## 8. Open questions

- **What to feed the subsolver:** preprocessed or original assertions (see
  4.2). Original assertions put cvc5's quantifier preprocessing, which does
  restructure quantifiers, between the port and the main solver's
  quantified formulas.
- **How to split the time limit** between the subsolver and the main solver,
  and what to answer when the main solver times out after a port unsat
  (unknown, with a distinct trace).
- **Several `check-sat` calls:** `--z3` supports them with assertions in
  between, and `reset-assertions`. A fresh subsolver per `check-sat`, with
  all current assertions, is the simple answer.
- **`getInstantiationTermVectors` against `getRelevantQuantTermVectors`.**
  The port can only give all instantiations; the main solver's unsat core
  (with `--produce-unsat-cores` on the main solver only) could report which
  ones mattered, which is useful for attribution in its own right.

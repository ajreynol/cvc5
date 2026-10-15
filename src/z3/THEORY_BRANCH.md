# Audit: the theory branch, and the quantifier stack against cvc5's

Date: 2026-10-14

Source snapshot: `d7b68ff497`

Status: Phase A measured (section 6); Phase C in progress, steps 1 to 4
done.

The propositional branch has been measured
([PROPOSITIONAL_BRANCH.md](PROPOSITIONAL_BRANCH.md), section 3). Of the
propositional components, only relevancy matters, and only through
E-matching and the instance checker; decisions must follow the formula, but
justification order does as well. Instantiating during propagation also
matters. A Z3-style relevancy filter for cvc5's term database
(branch `z3-relevance-1`) did not improve cvc5, which suggests that
relevancy is a companion of the port's eager, incremental matching rather
than an advantage by itself.

That moves the search to the theory branch, and within it to the
quantifier stack. This document:

- maps the theory side, `SmtContext` and its plugins, onto cvc5;
- compares the quantifier stack with cvc5's `QuantifiersEngine` in detail;
- names the issues and some defects found on the way;
- proposes measurements that need no code, then the extraction of the
  quantifier stack behind an explicit contract, as Stage 1B did for
  `PropCore`.

Throughout, "cvc5" means the native engine with the user's baseline,
`--user-pat=strict --no-cbqi` (in this cvc5, `--cbqi` is conflict-based
instantiation), and "Verus" means `--z3 --z3-preset=verus` or `verus-best`.

## 1. The theory side at a glance

| Component | Lines | Under Verus |
|---|---|---|
| E-graph core: `smt_context`, `internalizer`, `enode`, `cg_table` | 5,959 | |
| Justifications and `Explainer` | 1,052 | |
| Theory interface, `TheoryStatus`, `Setup` | 1,007 | `Setup` registers native arithmetic, the bit-vector bridge, datatypes |
| Arithmetic (`theory_arith_*`, a port of Z3's `theory_mi_arith`) | 9,370 | native (`--z3-arith=native`) |
| Datatypes (`theory_datatype`) | 1,327 | native |
| The cvc5 bridge (`theory_cvc5`) | 1,717 | always for bit-vectors; also the nonlinear fallback under `verus-best` |
| Dynamic Ackermann (`dyn_ack`) | 550 | on |
| **Quantifier stack** (`quantifier_manager`, `mam`, `qi_queue`, `checker`, `quick_checker`, `enum_inst`, `cost_function`, `fingerprints`, `pattern_inference`, `quantifier_stat`) | 9,261 | |

Arrays, strings, floating point and sets have no plugin: their atoms mark
the model unsound, so "sat" becomes "unknown"
(`SmtContext::checkTheorySupported`).

## 2. The quantifier stack against cvc5

| Aspect | The port (Z3) | cvc5 | Difference that matters |
|---|---|---|---|
| Activation | A quantifier reaches the stack when it is assigned true and is relevant (`PropCore::assignCore`, `relevantEh`). Its patterns are compiled each time it is assigned, into trail-scoped code trees (`DefaultQmPlugin::assignEh`). | Every asserted quantified formula is active. Triggers are made at registration and regenerated periodically. | Recompilation after backjumps; relevance gates which quantifiers are matched at all. |
| Patterns | User patterns; pattern inference under `verus-best` (`PatternInference`). Unary patterns are matched eagerly. **Multi-patterns are matched lazily**: beyond `--z3-qi-max-eager-multipatterns` (default 0, plus one if the quantifier has no unary pattern) they go to a lazy matcher that runs only at final check, at most twice per search (`d_qiMaxLazyMultipatternMatching`). | `--user-pat=strict`: user patterns only, no auto-generated triggers for those formulas. Every multi-trigger is matched every round (`InstMatchGeneratorMultiLinear`). | T3. |
| Matching engine | The MAM: one code tree per head symbol, interpreted over candidates. **Incremental**: a new relevant enode becomes a candidate (`relevantEh`); a merge adds the parents reachable through an inverted path index (`addEqEh`); 64-bit label sets on enodes filter both. | Generators re-enumerate matches from scratch every round over the term database's tries (`InstMatchGenerator::resetInstantiationRound`). `--ieval=use` (default) prunes a partial match early when the instance would be entailed. | T1. The MAM finds each new match once, when the term or merge appears; cvc5 rediscovers every match every round. |
| Timing | Matching and eager instantiation run at the end of every theory propagation (`SmtContext::theoryPropagate`, last step), i.e. after every BCP fixpoint. Delayed instances wait for final check. | E-matching runs at FULL effort in two of every three rounds (`--inst-when=full-last-call`, phase 3) and at LAST_CALL. **Never at STANDARD effort.** | T1; measured by A6. |
| Instance queue | Each match gets a cost, `(+ weight generation)` by default (`--z3-qi-cost`); the terms an instance creates get generation = cost (`--z3-qi-new-gen`). Cost at most the eager threshold (100 under Verus): instantiated now. Above it: delayed, and at final check made only if at most the lazy threshold (20). **So under Verus an instance costing over 100 is never made**, unless the checker finds it in conflict. | No queue. Every match found in a round is sent. Instantiation levels (`--inst-max-level`, unlimited by default) are the nearest counterpart; setting one also turns `--cegqi` off. | T2. The thresholds cap the depth of instantiation chains, which breaks matching loops. |
| Deduplication | Fingerprints: (quantifier, binding enodes), looked up with the bindings and their roots; **scoped**, popped with the scope (`FingerprintSet`). | An instantiation trie per formula, on exact terms, **permanent** (`Instantiate::recordInstantiationInternal`), plus the lemma cache. | Tied to instance lifetime (T8). |
| Instance checker | `Checker::isSat` skips an instance that is already satisfied (`--z3-qi-checker`, on); `isUnsat` makes a delayed instance at once when it is in conflict (`d_qiPromoteUnsat`, on, no option). Both look only at relevant terms and atoms. `QuickChecker` is off under Verus. | `--inst-no-entail` rejects an instance whose body the equality engine entails; `--ieval=use` rejects it during matching. Neither restricts itself to relevant terms. | T4; B1g showed the restriction to relevant terms matters. |
| Instance lifetime | An instance is an auxiliary clause of the scope it is made in, deleted on backtracking. | Permanent lemma (`LemmaProperty::INPROCESS`, never `REMOVABLE`). | T8; B2a was ambiguous. |
| Generations | Every enode has a generation; a class keeps the minimum; generations of recreated terms are cached across backjumps (`cacheGeneration`). | Instantiation levels, only computed when `--inst-max-level` is set. | Part of T2. |
| Model checking | No MBQI: `checkModel` returns unknown whenever there are quantifiers. | With strict user patterns and no MBQI, E-matching saturation also ends in unknown. | None for unsat answers. |
| Conflict-driven instances | Promotion by `Checker::isUnsat` of delayed instances. | Conflict-based instantiation, off in the baseline (`--no-cbqi`). | Small under Verus, where few instances are delayed. |

### Measured so far

- **A6** (`--z3-qi-eager-threshold=0 --z3-qi-lazy-threshold=100`): much
  worse. Timing matters.
- **B1f** (E-matching ignores relevancy): much worse. **B1g** (the checker
  ignores relevancy): worse, with many unknowns.
- **On `regress1/quantifiers/z3.620661-no-fv-trigger.smt2`** under
  `verus-best`, the baseline reaches generation 100, the cap. With
  `--z3-qi-cost=0` or `weight`, which remove the cap, it makes 5,305
  instances instead of 771 and gives up instead of answering unsat.

## 3. The rest of the theory side against cvc5

| Aspect | The port (Z3) | cvc5 |
|---|---|---|
| Equality reasoning | One E-graph for all theories: enodes with congruence roots, parent lists and theory variable lists; a congruence table per symbol; a proof forest for explanations (`Explainer`). | Distributed equality engines with a master engine for quantifiers (`--ee-mode=distributed`). |
| Equalities to literals | Merges assign equality atoms directly, and true/false classes assign their Boolean members. | Through theory propagation. |
| Dynamic Ackermann | On: congruences used in conflicts become lemmas after each resolved conflict. | No counterpart (only static `--ackermann`). |
| Theory combination | Model-based: native arithmetic proposes equalities between shared terms with equal values (`assumeEqs`). | Care graph (`--tc-mode=care-graph`). |
| Arithmetic | Native port of Z3's simplex-based solver. Z3's nonlinear strategies are not ported; under `verus-best` a nonlinear subproblem goes to the bridge. | cvc5's own linear and nonlinear solvers. |
| Bit-vectors | Always through the bridge. | Native. |
| Final check | Round-robin over the theories and the quantifier stack, starting where the last one left off. | Fixed order, quantifiers last, then last call. |

## 4. Issues

**T1. Eager, incremental matching against rounds from scratch.** The MAM
finds a match when the term or merge that makes it appears, at the end of
every propagation, and never revisits it. cvc5 rediscovers every match
every round, at full effort only. A6 shows that the timing matters. The
open question is whether it is the timing, the incrementality that makes
the timing affordable, or the queue policy that rides on both (T2).

**T2. The instance queue caps instantiation depth.** Under Verus, cost is
weight plus generation, new terms take the instance's cost as their
generation, and anything costing over 100 is never instantiated unless it
is in conflict. That bounds every chain of instances at about 100 steps,
which breaks matching loops; the measurement above shows a loop that
explodes without it. cvc5 has no such bound by default.

**T3. Multi-patterns are matched lazily.** By default only unary patterns
(and one multi-pattern when there is no unary one) are matched eagerly; the
rest wait for final check and are rematched at most twice per search. cvc5
matches every multi-trigger every round.

**T4. The instance checker.** It skips instances that the relevant part of
the assignment already satisfies. B1g says its restriction to relevant
terms matters; whether the checker itself matters is not yet measured.
cvc5's counterparts (`--inst-no-entail`, `--ieval`) are not restricted to
relevant terms.

**T5. The bridge runs at every final check under `verus-best`.** With the
nonlinear fallback on, native arithmetic registers every arithmetic atom
with the cvc5 bridge (`TheoryArith::registerNlFallbackAtom`), whose comment
says they are consulted only when the nonlinear check gives up. But the
bit-vector bridge, registered in every configuration, owns the bridge and
runs one subsolver call over all registered atoms at every final check
(`TheoryCvc5::finalCheckEh`). On a two-atom linear problem, `verus-best`
makes one bridge call and `verus` none. Part of what has been credited to
"nonlinear arithmetic and the fallback" in `verus-best` may therefore be a
cvc5 check of the arithmetic, with its model-based combination
(`separateSharedValues`), at every final check.

**T6. Relevancy feeds the matcher.** The MAM's candidates and label sets
come from relevancy notifications, and its merge events arrive before
members are re-rooted. A boundary around the quantifier stack has to carry
these events, in this order.

**T7. The MAM depends on the inside of an enode.** It reads the owner,
symbol, root, class list, congruence root, generation, arguments, marks,
label hash, label sets and parent lists, and is a friend of `ENode`. Hosting
it over cvc5's equality engine would need an adapter for all of these, and
for the merge event with both roots before re-rooting.

**T8. Instance lifetime and deduplication.** Instances and fingerprints are
scoped together, so an instance is made again after a backjump. B2a was
worse, but it also changed how relevancy treats instances; the lifetime on
its own is unmeasured.

## 5. Defects and inconsistencies found

Each is to be fixed in a change of its own; none affects the Verus runs
except the first.

1. **The bridge comment** (T5): `registerNlFallbackAtom` says the atoms are
   consulted only when the nonlinear check gives up; they are consulted at
   every final check.
2. **The lazy matcher never clears its new patterns**
   (`Mam::hasWork`): they are cleared only on pop, and the lazy matcher's
   `match` is never called. While a lazy multi-pattern exists in the
   scope, `--z3-force-rematch` and `--z3-enum-inst` never run. Both are off
   under Verus.
3. **`--z3-force-rematch`** says it ignores relevancy, but calls
   `rematch(false)`, which skips irrelevant enodes.
4. **`--z3-enum-inst-fallback`** is read but never used.
5. **Statistics:** `z3::instances` counts every instance, not only those
   from E-matching; `z3::lazyInstances` counts delayed instances that were
   made, not dropped ones; native arithmetic's statistics are not exported.
6. **Stale names:** `README.md` and `smt_context.h` refer to
   `SmtContext::checkFinalize`, and `FIDELITY.md` to
   `SmtContext::pushAssertion`; both are `PropCore`'s. `ModelGenerator` is
   declared and befriended but never defined.
7. **cvc5, for reference:** `--relevant-triggers` has no effect, since
   `QuantRelevance::d_syms_quants` is read but never written.

## 6. Proposed sequence

### Phase A: measure the switches that exist (no code)

All on top of `--z3 --z3-preset=verus-best`.

| Run | Switches | Isolates | Compare with |
|---|---|---|---|
| A6b | `--z3-qi-eager-threshold=10` | how much eagerness (T1) | baseline, A6 |
| q1 | `--z3-qi-eager-threshold=0 --z3-qi-lazy-threshold=100 --no-z3-relevancy-match` | whether relevancy matters only because matching is eager (T1, T6) | A6 |
| q2 | `--z3-qi-eager-threshold=1000` | the depth cap (T2) | baseline |
| q3 | `--no-z3-qi-checker` | the instance checker (T4) | baseline |
| q4 | `--z3-qi-max-eager-multipatterns=8` | lazy multi-patterns (T3) | baseline |
| q5 | `--no-z3-arith-nl-fallback` | the fallback together with the bridge at every final check (T5) | baseline, and `verus` |
| q6 | `--z3-qi-cost=0` | no queue policy at all, as in cvc5 (T2) | baseline, q2 |

If q2 or q6 lose, the cap matters, and cvc5 has a direct test:
`--inst-max-level=100` against the baseline, both with `--no-cegqi`, since
setting a level turns `--cegqi` off.

**Results** (2026-10-14, on `verus-best`, against its baseline):

| Outcome | Runs |
|---|---|
| no difference | B3c (justification decisions with every assigned atom delivered), q2 (cap raised to 1000), q4 (eager multi-patterns; perhaps slightly better, +7) |
| somewhat worse | q3 (no instance checker), q6 (no cost policy) |
| worse | A6b (eager threshold 10, Z3's default), q5 (no nonlinear fallback) |
| much worse | q1 (no eager instances and no relevancy for matching) |

What they say:

- **Eagerness is a slope, not a switch.** Lowering the eager threshold from
  100 to 10 already loses (A6b), and deferring every instance loses much
  more (A6).
- **Some bound on instantiation depth matters, but not its value.** Raising
  the cap from 100 to 1000 changes nothing (q2); removing the cost policy
  altogether loses somewhat (q6).
- **The instance checker helps somewhat** (q3), and only when restricted
  to relevant terms (B1g).
- **The nonlinear fallback matters** (q5). Whether it is the fallback or the
  bridge call at every final check (T5) is still open.
- **Multi-pattern laziness is not worth pursuing** (q4).
- **B3c confirms** that cvc5-style decisions together with cvc5-style
  delivery cost nothing, as long as relevancy is kept for matching.

### Phase B: switches that need a little code (off by default)

- **The bridge at final check** (T5): consult the atoms registered by the
  nonlinear fallback only when the nonlinear check gives up, as the comment
  intends. With q5, this separates the fallback from the per-final-check
  bridge call.
- **Matching in rounds** (T1): no matching during propagation; at final
  check, rematch every tree over every relevant enode, as cvc5's schedule
  does, and instantiate what is found. Compared with A6, this tells whether
  the loss is in when instances are made or in incremental matching.
- **Instance lifetime without the relevancy confound** (T8): permanent
  instances whose root is marked relevant as a scoped instance's is.

### Phase C: extract the quantifier stack behind a contract

As Stage 1B did for `PropCore`, in steps that each leave answers and
`z3::` counters unchanged.

1. **Name the contract.** Inbound, from the theory side: a quantifier is
   asserted (`assignEh`) or deleted (`del`), an enode becomes relevant, two
   classes merge (with both roots, before re-rooting), propagation reaches a
   fixpoint (`propagate`), final check (eager and lazy), scopes, search
   start and restart, and the queries `isShared` and the generation of a
   quantifier. Outbound, the services the stack uses, about 35 methods of
   `SmtContext`:
   - **term view:** the enodes of a symbol, congruence lookup, roots,
     classes, parents, disequality, symbol ids, generations, internalizing a
     ground pattern term;
   - **Boolean view:** assignments and whether a literal is internalized;
   - **relevance view:** the matching and checking predicates, marking
     relevant;
   - **instance sink:** rewriting an instance and asserting it with its
     generation;
   - **infrastructure:** the trail, statistics, cancellation and resource
     limits.
2. **Route the stack through it.** `SmtContext` implements the outbound
   interface; the stack calls nothing else. Measure the cost of the
   indirection, as Stage 1B did for `PropCore`.
3. **Give the stack its own state.** The fingerprints move from
   `SmtContext` into the stack; pattern inference moves to assertion
   preparation, its only user.
4. **Separate matching from policy.** The MAM reports matches (quantifier,
   bindings, generations) to a sink; the queue, with its costs and
   thresholds, is one policy behind that sink. A cvc5-like policy, which
   sends every match, becomes a second implementation rather than a
   parameter setting.
5. **Separate scheduling.** When to match and when to instantiate is
   decided in one place, the plugin's `propagate` and final check, so that
   rounds (Phase B) are a scheduling policy.
6. **Wrap the enode accesses of the MAM** (T7) behind accessors, which is
   the precondition for running it over another E-graph.

**Progress.**

From 2026-10-15 on, experiments on the theory side run under cvc5's
propositional engine (`--z3-prop-engine=cvc5`, ARCHITECTURE_PLAN.md section
15) and are compared with its default configuration, since what counts is
what holds under cvc5's search. The steps that should not change behavior
are checked in both modes: steps 1 to 4 leave answers and `z3::` counters
unchanged under cvc5's propositional engine as well (447 runs with
`verus-best`, 7 that time out compared under `--rlimit`).

- **Steps 1 and 2: done** (2026-10-15). The outbound contract is
  `QuantifierServices` ([quantifier_services.h](quantifier_services.h)),
  which `SmtContext` implements; the stack (`QuantifierManager` and its
  plugin, `Mam`, `QiQueue`, `Checker`, `QuickChecker`, `EnumInst`) holds
  that interface and no longer includes `smt_context.h`. It has 40
  methods, in the groups above: the term view (13), the Boolean view (6),
  the relevance view (6), the instance sink (3), and the infrastructure
  (8, with the trail through `getTrailStack`). The other four loop back into
  the stack, as in Z3, where the stack reaches itself through
  `smt::context`: `addInstance` and the generation of a quantifier are the
  quantifier manager's, and `addFingerprint` and `containsInstance` use the
  fingerprints, which `SmtContext` holds; step 3 removes them. The inbound
  contract is `QuantifierManager`'s interface, unchanged. On the way:
  `QuantifierManager` is no longer a friend of `SmtContext`; the forced
  rematch flag, which only the stack uses, moved into `QuantifierManager`;
  and `ENode::setLblHash` takes the trail instead of the context.
  `SmtContext` is `final`, so the rest of the theory side still calls it
  directly. Answers and `z3::` counters are unchanged on the comparison set
  (894 runs, the 15 that time out compared under `--rlimit`). On ten Verus
  benchmarks the core solves in 1 to 6 s, run one at a time and three times
  each, the time ratio is 0.994: the indirection costs nothing measurable.
- **Step 3: done** (2026-10-15), for the stack's own state. The
  fingerprints moved from `SmtContext` into `QuantifierManager`, which
  pushes and pops them where `SmtContext` did. `Mam` (and its compiler),
  `EnumInst` and `QuickChecker` hold the quantifier manager, so the four
  services that looped back into the stack left the contract, which is now
  36 methods, all of the theory side. Pattern inference stays in
  `SmtContext`: it is a preprocessing utility, like the normalizers and
  NNF that also live there, rather than state of the stack, and it depends
  on `SmtContext`'s parameters and lifetime, which `AssertionPreparation`
  outlives; moving the preprocessing utilities together is a separate
  cleanup. Answers and `z3::` counters unchanged (894 runs, 16 compared
  under `--rlimit`).
- **Step 4: done** (2026-10-15). Matching, the decision of when to make an
  instance, and making it are separate. The MAM and the quick checker
  report a match to the quantifier manager, which drops the ones made in
  scope (by fingerprint) and gives the others to an `InstancePolicy`
  ([instance_policy.h](instance_policy.h)); the base class makes an
  instance (substitution, rewriting, the clause `(or (not q) ...)`, the
  permanent instances, internalization). `QiQueue` is Z3's policy and the
  default. `Cvc5InstancePolicy` makes every match, with no cost and no
  threshold, its terms one generation above the match's, as cvc5's
  instantiation levels count, and keeps the instance checker, as cvc5's
  `--inst-no-entail` does; it has two timings, which are the switch
  `--z3-qi-policy`:
  - `eager`: at the next propagation, Z3's timing without its triage;
  - `cvc5`: in rounds, at final checks, every match found since, cvc5's
    timing, with matching still incremental.

  `z3` against `eager` measures the triage; `eager` against `cvc5`, the
  timing; and `cvc5` is how the port's matcher would instantiate under
  cvc5's quantifiers engine, which is what Phase D would start from.
  Neither bounds a matching loop, as cvc5 does not. With the default,
  answers and `z3::` counters are unchanged (894 runs, 15 compared under
  `--rlimit`); on the ten Verus benchmarks, the time ratio of steps 3 and 4
  together is 0.990. Neither new timing gives a wrong answer or a new
  failure on the quantified regressions with assertions.

  **First reading, under the port's own search** (development set of 88
  hard Verus benchmarks, 10 s;
  to be confirmed on the full set): `z3` solves 87 in 169 s, `eager` 88 in
  162 s, `cvc5` 38 in 563 s. The gain is in the timing: making instances
  during propagation rather than in rounds at final checks. Z3's triage
  (costs, thresholds, the lazy queue) adds nothing here, as Phase A's q2
  suggested. For Phase D, this is the branch where cvc5 needs a quantifiers
  module that instantiates at standard effort.

  **Full set, under the port's own search** (60 s, 2026-10-15): `eager` is
  close to the default `z3`,
  solving nearly as many in nearly the same time; `cvc5` is bad. Under the
  Verus presets, Z3's policy differs from `eager` only by a depth cap: the
  weight of a quantifier is 1 (unless pattern inference raised it), so an
  instance costs its generation plus 1 and its terms get that generation,
  as with `eager`; a match costing at most the eager threshold (100) is
  made at once, as with `eager`; a costlier one is made only if the checker
  finds it in conflict, since the lazy threshold (20) is below the eager
  one and the final check never makes a delayed instance. So the cost
  function and the lazy queue do nothing here, and the cap at about 100
  generations accounts for what `z3` gains over `eager`.

  **Under cvc5's propositional engine** (60 s, 2026-10-15): `eager` is
  significantly worse than the default (host3eager against host3). The
  depth cap matters there: cvc5 keeps every instance clause it is sent,
  across branches, while the core's own search deletes instances on
  backtracking, so without the cap the chains of instances accumulate.
  The reading under the core's own search did not transfer, which is why
  theory-side experiments now run under cvc5's propositional engine.

### Phase D: toward cvc5

What Phase D is depends on Phases A to C:

- **If the depth cap (T2) carries the gain,** it can go to cvc5 directly as
  instantiation levels, without changing when cvc5 instantiates.
- **If eager, incremental matching (T1) carries it,** cvc5 needs a
  quantifiers module that runs at STANDARD effort with an incremental
  matcher. Its prerequisites are the equality engine's merge and new-class
  notifications (`MasterNotifyClass` already relays them to quantifiers),
  incremental relevance (the `RelevanceManager` computes only at full
  effort), generations, and a queue. Hosting the port's MAM there through an
  adapter for T7 is one way to get the matcher.
- **If neither matters,** the rest of the theory side is next: dynamic
  Ackermann, the model-based combination of native arithmetic, and the
  bridge.

## 7. Reading the outcomes

- **q1 about as bad as A6:** relevancy for matching only matters because
  matching is eager. For cvc5 it comes with eager matching, not before it.
- **q2 or q6 worse:** the depth cap matters; try `--inst-max-level` in cvc5.
- **q3 worse:** the instance checker matters; compare `--inst-no-entail` and
  `--ieval` in cvc5.
- **q4 better:** lazy multi-patterns cost answers; worse: they are part of
  the gain.
- **q5 and the Phase B bridge switch:** how much of `verus-best`'s gain over
  `verus` is the per-final-check bridge rather than the fallback.
- **Rounds (Phase B) about as bad as A6:** the loss is in when instances
  are made; much better than A6: incremental matching matters in its own
  right.

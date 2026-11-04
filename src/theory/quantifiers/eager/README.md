# The eager E-matching core (`--eager-e-matching`)

A port of Z3's E-matching core, which runs as the first module of cvc5's
quantifiers engine (`EagerEMatching`). cvc5's own prop engine and theories do
the ground reasoning, and cvc5's quantifiers engine registers the quantified
formulas and skolemizes those asserted false (the core takes that lemma when
the formula is relevant to it); the core keeps a shadow of the ground state (an
E-graph, and a Boolean mirror of the SAT assignment for Z3's relevancy), sends
quantifier instances and delayed units to cvc5 as lemmas, and asks it for
decisions. Since it sends only lemmas, it never explains anything, and keeps no
justifications.

Its lemmas have proofs (`LemmaProofGenerator`), made when they are asked for:
an instance is sent as cvc5's instantiation lemma, proven by `INSTANTIATE`, a
skolemization with the proof of cvc5's `Skolemize`, and a delayed unit by
weakening; cvc5's preprocessing proves the form the core takes them in.

## Layout

All of the port is in `src/theory/quantifiers/eager/`, in the namespace
`cvc5::internal::theory::quantifiers::eager`:

- the cvc5 integration: `EagerEMatching` (the module of the quantifiers
  engine, and the boundary with cvc5), `RelevancyTracker` (the
  `TheoryEngineModule` that hands it every asserted literal) and
  `LemmaProofGenerator`;
- the coordinator: `SmtContext` (internalizer, propagation and scopes);
- the Boolean side, over cvc5's `prop::SatLiteral`: `PropCore` (variables,
  assignment, clauses, watch lists, Boolean propagation) and
  `RelevancyPropagator`, which spreads relevancy along the E-graph's
  equivalence classes;
- the theory side: `EGraph`, `mam` (E-matching), `QiQueue`, the checker and
  the quantifier manager;
- the shared pieces: the trail stack (on a `context::Context` of its own),
  the statistics, and `QuantifierNormalizer`.

Relevancy is not separable from the rest: it runs on the core's trail stack,
over the core's renamed terms and its E-graph, and `PropCore` exists only as
the Boolean mirror it propagates on.

The core takes the input as cvc5's preprocessing leaves it, from
`ppNotifyAssertions`. It renames the quantified variables to the canonical
ones it expects (`QuantifierNormalizer`) at its boundary: `EagerEMatching`
renames the formulas, atoms and literals that come from cvc5 (`toCore`), and
gives cvc5 its own atoms back in the lemmas and queries it sends (`toHost`). cvc5
preprocesses the core's lemmas as any other, and the core takes them in that
form.

## Ownership

Each class owns the ones below it; `(-> X)` is a reference it keeps to X.
`EagerEMatching` drives `SmtContext`, which calls it back only to send its
instances, skolemizations and lemmas (`mkInstance`, `mkSkolemization`,
`sendLemma`). `SmtContext` drives the others; their references to it are for
notifications (`PropCore`: an atom assigned, a term relevant, a variable
deleted; `EGraph`: a merge, of Boolean classes, a conflict) and for what it
coordinates (the trail stack, relevancy, the statistics).

```
QuantifiersEngine (cvc5)
└── EagerEMatching            the module of cvc5's quantifiers engine, and
    │                             the boundary with cvc5: facts, checks,
    │                             lemmas and their proofs, following
    │                             the SAT context
    ├── LemmaProofGenerator
    ├── PopNotify                 a ContextNotifyObj on the SAT context
    │                                                   (-> EagerEMatching)
    ├── RelevancyTracker          registered with TheoryEngine::addModule:
    │                             the literals the SAT solver asserts
    │                                                   (-> EagerEMatching)
    └── SmtContext                the core: input, internalization,
        │                         propagation and scopes   (-> EagerEMatching)
        ├── Statistics
        ├── TrailStack            its own context::Context, and the memory of
        │                         the enodes, relevancy handlers, fingerprints
        │                         and code trees
        ├── PropCore              the Boolean side     (-> SmtContext)
        │   └── RelevancyPropagator                     (-> PropCore, SmtContext)
        ├── EGraph                the enodes, congruence closure, generations,
        │   │                     and the merges of the master equality engine
        │   │                                           (-> SmtContext)
        │   └── CgTable, TmpENode
        ├── QuantifierNormalizer
        └── QuantifierManager                           (-> SmtContext)
            ├── QiQueue                                 (-> QuantifierManager,
            │   │                                           SmtContext)
            │   └── Checker                             (-> SmtContext, EGraph)
            ├── FingerprintSet                          (-> TrailStack)
            └── Mam (MamImpl: LabelHasher,
                CodeTreeManager, Compiler, Interpreter, CodeTreeMap)
                                                        (-> SmtContext, EGraph,
                                                            QuantifierManager,
                                                            TrailStack)
```

## Hooks in cvc5

Outside this directory, the port touches:

- `QuantifiersModules` makes `EagerEMatching` under `--eager-e-matching`,
  first, then cvc5's own modules as their options select them.
  `--eager-e-matching` sets
  `--inst-when=last-call-delay`, so that these instantiate only on a complete
  model, once the core and every theory are done, and turns off
  conflict-based instantiation (`--cbqi`).
  `QuantifiersModule::finishInit` and `notifyMasterMerge` give it the theory
  engine and the merges of the master equality engine.
- `TermDb` and `InstEvaluatorManager` do not reset at standard effort, where
  only the core checks, at every check.
- `TheoryEngineModule::notifyFact` / `needsFacts` and
  `TheoryEngine::addModule` are used by `RelevancyTracker`.
- `Skolemize::getSkolemizationLemma` gives the core the lemma with which the
  quantifiers engine skolemized a formula, with its proof.
- `PropEngine` uses `FormulaLitPolicy::TRACK_AND_NOTIFY_VAR` under
  `--eager-e-matching`, so Boolean variables reach the core.
  `PropEngine::getPropDecisions` skips the activation literals of user
  scopes, which have no node.
- `SetDefaults::checkEagerEMatchingCapabilities` refuses what the core does
  not support: `--deep-restart`, sygus (and so interpolants and abducts),
  oracles, and `--dump-instantiations` without proofs (the instantiations are
  read from the proof). Unsat cores default to `--unsat-cores-mode=sat-proof`,
  since deciding on the input as assumptions first hurts the core's search.
  `setDefaultsQuantifiers` sets `--pre-skolem-quant=agg`: the existentials
  nested in quantified formulas get skolem functions of the enclosing
  variables, as in Z3's negation normal form, which `QuantifiersPreprocess`
  now also applies to quantified formulas with patterns. It also sets
  `--inst-when=last-call-delay` and turns off `--cbqi`, as above.

## Incremental solving

The core's scope level is cvc5's SAT context level minus one, so its level 0
is below every user scope, and each user push is a scope of the core, as in
Z3, where the user scopes are the base level of the search. Each check-sat
internalizes the new assertions at the scope of their user level (`presolve`,
`SmtContext::setupSearch`), and a user pop pops them with the scope: the
asserted formulas and the encoded distincts are on the core's trail. What
outlives the scopes of the core is in cvc5's user context: the lemmas sent
(cvc5 drops a lemma with the pop of the user scope of its atoms) and the
forms of the instances (cvc5's preprocessing gives the definitions of their
skolems again after a pop). Delayed units count the decision levels of the
activation literals of the user scopes as the base of the search.
`reset-assertions` pops the SAT context to level 0, and the core is then made
again.

## Next step: arithmetic equalities as matching hints

The worst files of the Verus set (in `quant-07-25/slow`: cs56, cs59, cs65,
cs77, cs100, cs101, cs102, cs150, cs151 ...) run out of resources under
`--eager-e-matching`, while Z3 solves them in about 0.1s with a similar
number of instances. The core's maximum instance generation there reaches the eager
threshold (101) where Z3's stays at 6 to 31: a matching loop over the
sequence axioms (`axiom_seq_add_index*`) and `prelude_add`/`prelude_sub`
nests terms `Add(%I(I(Sub(%I(I(Add ... i ... len ... len)))))` without end.
Z3 breaks it with the equalities its arithmetic propagates to the E-graph
(`smt.arith.propagate_eqs`, on by default): each new term is found equal to
`i` and joins an existing class, so it makes no new match. With
`smt.arith.propagate_eqs=false`, Z3 loops in the same way (cs65: generation
101 and 28,504 instances instead of 774; cs56, cs59, cs150 and cs151 time out).
cvc5's linear arithmetic propagates no such equalities: theory combination
finds them only at full effort, as one split per pair of shared terms with
equal values (38,612 splits on cs65 in a single round).

Z3 propagates two kinds of cheap equalities (`theory_arith_eq.h`):

- fixed: two variables whose bounds fix them to the same value;
- offset: a row `x - y + k = 0` whose other variables are all fixed, gives
  `x = y - k`; two variables with the same offset from `y` are equal.

A prototype (2026-10-30, not committed) did this and gained 6 files on the
388 Verus files (373 to 379 at `--rlimit=10000000`, none lost; cs65 went from
out of resources to 0.6s), at +5% time and +14% instances on the commonly
solved files:

- In `TheoryArithPrivate`, `assertionCases` records each variable whose bound
  is asserted. At the end of `postCheck` (when there is no conflict), each
  recorded variable that is now fixed is entered in a value table, and the
  rows of its column (`Tableau::colIterator`) are checked: a row with one
  non-fixed variable fixes it (value table), a row with two non-fixed
  variables of opposite coefficients is an offset (offset table keyed by
  `(y, k)`), with offset 0 an equality. Both tables are `CDHashMap`s in the
  SAT context, so they are popped with the bounds they depend on. The
  equalities between variables that have nodes (`ArithVariables::asNode`) are
  collected. A first version that scanned the whole tableau at every check
  was too slow (14 files lost to timeouts): it must be incremental.
- `EagerEMatching::checkCore` merges the collected pairs into the E-graph after
  `applyMasterMerges`, mapping each term to the core's term of its class in
  the master equality engine, as the master merges are; the pairs are
  dropped when the SAT context pops. The merges are not explained: they only
  steer matching, and an instance is valid whatever led to it, so soundness
  does not depend on them.

To do:

- A proper interface between arithmetic and the core instead of a shared
  global list, e.g. a callback registered with the theory engine, or an
  equality notification on the master equality engine's side.
- cs150 and cs151 still loop: there `len` is not fixed, and the offset only
  appears after substituting one row in another (`A = S + len`,
  `S = i - len`). Check which rows Z3 examines (`propagate_cheap_eq`,
  `fixed_var_eh`, and after pivoting) and do the same.
- Measure before going further whether plain cvc5 (without
  `--eager-e-matching`) would gain from the same equalities, now asserted to the equality engine with an
  explanation (the fixed bounds of the row), by counting how many of them
  relate terms the master equality engine does not already have equal. Its
  lazy instantiation does not loop on these files (it solves cs65 in about 1s),
  so the gain may be small.

Also measured: only about half of the arithmetic literals and 12% to 33% of
the datatype literals that cvc5 asserts to its theories are relevant to the
core. Z3 asserts only relevant literals to its theories, so filtering cvc5's
theory facts by the core's relevancy is the next larger lever.

## Size

C++ lines (code lines exclude blank and comment lines, as cloc counts them),
as of this README:

| Directory | Files | Code | Comment | Blank |
|---|---:|---:|---:|---:|
| `src/theory/quantifiers/eager/` | 36 | 8848 | 2182 | 1198 |

The rest of cvc5 changes by 213 added and 13 deleted lines over 19 C++ files,
most of them in `smt/set_defaults.cpp` (the capability checks).

# The ported Z3 core (`--z3`)

A port of Z3's E-matching core, which runs as the only module of cvc5's
quantifiers engine (`Z3Module`). cvc5's own prop engine and theories do the
ground reasoning, and cvc5's quantifiers engine registers the quantified
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

## Layout and inclusion rules

| Directory | Contents | May include (from the port) |
|---|---|---|
| `src/z3/util/` | Data structures and the term interface: literals, the trail stack (on a `context::Context` of its own), approximate sets, `ast.h` (incl. `QuantifierNormalizer`), and `statistics` | nothing outside `z3/util/` |
| `src/z3/relevancy/` | The Boolean side: `PropCore` (assignment, clauses, watch lists, propagation), `RelevancyPropagator`, and `RelevancyTracker` (the `TheoryEngineModule` that hands it every asserted literal) | `z3/util/`, and `SmtContext` |
| `src/z3/quantifiers/` | The theory side and the cvc5 integration: `SmtContext` (E-graph, internalizer, and the boundary with cvc5 in `host.cpp`), `mam` (E-matching), `QiQueue`, the checker, the quantifier manager, `LemmaProofGenerator`, `ShadowFeed`, `Z3Module` | anything |

`PropCore` and `RelevancyPropagator` reach the theory side, `SmtContext`,
directly, so the two directories depend on each other.

The core takes the input as cvc5's preprocessing leaves it, from
`ppNotifyAssertions`. It renames the quantified variables to the canonical
ones it expects (`QuantifierNormalizer`) at its boundary: `SmtContext` renames
the formulas, atoms and literals that come from cvc5 (`toCore`), and gives
cvc5 its own atoms back in the lemmas and queries it sends (`toHost`). cvc5
preprocesses the core's lemmas as any other, and the core takes them in that
form.

All of the port's classes are in the namespace `cvc5::internal::z3`.

## Ownership

Each class owns the ones below it; `(-> X)` is a reference it keeps to X.

```
QuantifiersEngine (cvc5)
└── Z3Module                      the module of cvc5's quantifiers engine
    └── SmtContext                the core, and its boundary with cvc5
        │                         (host.cpp): lemmas, splits, and following
        │                         the SAT context (syncLevel)
        ├── Statistics
        ├── TrailStack            its own context::Context, and the memory of
        │                         the enodes, relevancy handlers, fingerprints
        │                         and code trees
        ├── PropCore                                    (-> SmtContext)
        │   └── RelevancyPropagator                     (-> PropCore, SmtContext)
        ├── QuantifierNormalizer
        ├── CgTable, TmpENode
        ├── QuantifierManager                           (-> SmtContext)
        │   ├── QiQueue                                 (-> QuantifierManager,
        │   │   │                                           SmtContext)
        │   │   └── Checker                             (-> SmtContext)
        │   ├── FingerprintSet                          (-> TrailStack)
        │   ├── QuantifierStatGen                       (-> TrailStack)
        │   └── Mam x2, eager and lazy (MamImpl: LabelHasher,
        │       CodeTreeManager, Compiler, Interpreter, CodeTreeMap)
        │                                               (-> SmtContext,
        │                                                   QuantifierManager,
        │                                                   TrailStack)
        ├── LemmaProofGenerator
        ├── SplitStrategy         registered with cvc5's DecisionManager
        ├── PopNotify             a ContextNotifyObj on the SAT context
        │                                               (-> SmtContext)
        ├── RelevancyTracker      registered with TheoryEngine::addModule:
        │                         the literals the SAT solver asserts
        │                                               (-> SmtContext)
        └── ShadowFeed            the merges of the master equality engine,
                                  which Z3Module forwards (notifyMasterMerge)
                                                        (-> SmtContext)
```

## Hooks in cvc5

Outside the directories above, the port touches:

- `QuantifiersModules` makes `Z3Module` under `--z3`, first, then cvc5's own
  modules as their options select them. `--z3` sets
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
- `DecisionManager::STRAT_QUANT_Z3_SPLIT`: the core asks cvc5 to decide the
  atoms its relevancy needs assigned through a decision strategy.
- `PropEngine` uses `FormulaLitPolicy::TRACK_AND_NOTIFY_VAR` under `--z3`, so
  Boolean variables reach the core.
- `SetDefaults::checkZ3Capabilities` refuses what the core does not support:
  `--incremental`, `--deep-restart`, sygus (and so interpolants and abducts),
  oracles, and `--dump-instantiations` without proofs (the instantiations are
  read from the proof). Unsat cores default to `--unsat-cores-mode=sat-proof`,
  since deciding on the input as assumptions first hurts the core's search.
  `setDefaultsQuantifiers` sets `--pre-skolem-quant=agg`: the existentials
  nested in quantified formulas get skolem functions of the enclosing
  variables, as in Z3's negation normal form, which `QuantifiersPreprocess`
  now also applies to quantified formulas with patterns. It also sets
  `--inst-when=last-call-delay` and turns off `--cbqi`, as above.

## Size

C++ lines (code lines exclude blank and comment lines, as cloc counts them),
as of this README:

| Directory | Files | Code | Comment | Blank |
|---|---:|---:|---:|---:|
| `src/z3/util/` | 8 | 651 | 287 | 157 |
| `src/z3/relevancy/` | 12 | 2274 | 514 | 373 |
| `src/z3/quantifiers/` | 27 | 7714 | 1606 | 990 |
| **Total** | 47 | **10639** | 2407 | 1520 |

The rest of cvc5 changes by 257 added and 18 deleted lines over 21 C++ files,
most of them in `smt/set_defaults.cpp` (the capability checks) and
`theory/quantifiers/quantifiers_preprocess.cpp` (pre-skolemization of
quantified formulas with patterns).

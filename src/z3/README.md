# The ported Z3 core (`--z3`)

A port of Z3's E-matching core, which runs as cvc5's quantifiers engine
(`Z3QuantifiersEngine`). cvc5's own prop engine and theories do the ground
reasoning; the core keeps a shadow of the ground state (an E-graph, and a
Boolean mirror of the SAT assignment for Z3's relevancy) and sends quantifier
instances, splits and delayed units to cvc5 as lemmas.

## Layout and inclusion rules

| Directory | Contents | May include (from the port) |
|---|---|---|
| `src/z3/util/` | Data structures and the term interface: literals, regions, trails, hashing, `types.h`, `ast.h` (incl. `QuantifierNormalizer`), `params`, `statistics`, and `AssertionTarget`, the interface the preprocessing pass uses | nothing outside `z3/util/` |
| `src/z3/relevancy/` | The Boolean side: `PropCore` (assignment, clauses, watch lists, propagation), `RelevancyPropagator`, the base `Justification`, `RelevancyTracker` (the `TheoryEngineModule` that hands it every asserted literal), and `TheorySide`, the interface through which it reaches the theory side | `z3/util/` only |
| `src/z3/quantifiers/` | The theory side and the cvc5 integration: `SmtContext` (E-graph, internalizer), `mam` (E-matching), `QiQueue`, the checker, the quantifier manager, `HostCore`, `ShadowFeed`, `SharedBackend`, `Z3QuantifiersEngine` | anything |
| `src/preprocessing/z3/` | The `z3-prep` pass (`Z3AssertionPreparation`) and what only it uses: `Nnf`, `ConnectiveNormalizer`, `AssertionRewriter` | `z3/util/` only |

The rules are kept by two interfaces:

- `TheorySide` (`relevancy/theory_side.h`): what `PropCore` and
  `RelevancyPropagator` need from the theory side. `SmtContext` implements it.
- `AssertionTarget` (`util/assertion_target.h`): what the preprocessing pass
  needs from the core (reset it, its quantifier normalizer, cvc5's
  preprocessing, asserting a prepared formula). `Z3QuantifiersEngine`
  implements it, and the pass finds it through the quantifiers theory.

All of the port's classes are in the namespace `cvc5::internal::z3`.

## Hooks in cvc5

Outside the directories above, the port touches:

- `TheoryQuantifiers` constructs `Z3QuantifiersEngine` under `--z3`.
- `QuantifiersEngine` has virtual methods, for the subclass.
- `TheoryEngineModule::notifyFact` / `needsFacts` and
  `TheoryEngine::addModule` are used by `RelevancyTracker`.
- `Theory::checksWithoutFacts`: the quantifiers theory is checked even without
  new facts.
- `PropEngine` uses `FormulaLitPolicy::TRACK_AND_NOTIFY_VAR` under `--z3`, so
  Boolean variables reach the core. The `UNPROCESSED` lemma property keeps
  cvc5 from preprocessing lemmas the core has already preprocessed.
- `Skolemize::getSkolemizationLemma` lets the core reuse cvc5's native
  skolemization lemma.
- `SetDefaults::checkZ3Capabilities` refuses what the core does not support
  (`--incremental`, models, proofs, unsat cores, and others).
- `ProcessAssertions` runs `z3-prep` last.

## Size

C++ lines (code lines exclude blank and comment lines, as cloc counts them),
as of this README:

| Directory | Files | Code | Comment | Blank |
|---|---:|---:|---:|---:|
| `src/z3/util/` | 17 | 1480 | 556 | 352 |
| `src/z3/relevancy/` | 14 | 2439 | 577 | 427 |
| `src/z3/quantifiers/` | 31 | 8838 | 1654 | 1135 |
| `src/preprocessing/z3/` | 8 | 559 | 250 | 82 |
| **Total** | 70 | **13316** | 3037 | 1996 |

The rest of cvc5 changes by 311 added and 38 deleted lines over 18 C++ files,
most of them in `smt/set_defaults.cpp` (the capability checks) and
`theory/quantifiers/theory_quantifiers.cpp`.

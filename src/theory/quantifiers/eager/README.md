# Eager E-matching (z3-faithful) + Inner SMT solver

Status: **scaffolding**. This directory holds a fresh implementation of
eager E-matching, modelled as closely as possible on z3's
`smt::mam` / `smt::quantifier_manager` / `smt::qi_queue`, together with an
`InnerSmtSolver` that owns the instances produced by matching.

Nothing here is shared with cvc5's existing (lazy) instantiation machinery:
`theory/quantifiers/ematching/*`, `TermDb`, `Trigger`, `InstMatchGenerator`,
`Instantiate`, `InstMatchTrie`, ... are all untouched and continue to run in
parallel. The only contact points with the rest of cvc5 are

1. notifications from the **master equality engine**, and
2. the conflicts/lemmas that the `InnerSmtSolver` chooses to export.

## 1. Goals / non-goals

Goals:

* Be *faithful to z3*. Where z3 makes a heuristic choice (when to compile a
  pattern, when to run the matcher, which candidate enodes to try, how to
  filter, how to cost and delay an instance, what generation to assign), we
  make the same choice, and we say in a comment which z3 function we are
  mirroring. Deviations must be deliberate and documented in section 8.
* Keep the new state **separate**. Eager E-matching maintains its own e-graph,
  its own trail and its own instance store. It observes the rest of cvc5; it
  does not mutate it.
* Keep the existing cvc5 pipeline intact: lazy instantiation (everything cvc5
  does for instantiation today) runs unchanged, concurrently with this module.

Non-goals (for now): proofs for the instances the inner solver uses
internally, model construction, higher-order matching, MBQI interaction.

## 2. z3 reference architecture

Reference: the z3 source tree at `~/z3` (`src/smt`, `src/util`). Every claim
below was read out of that source, not recalled; line numbers are from that
checkout and will drift, the function names will not.

| z3 component | file | role |
| --- | --- | --- |
| `mam` interface | `mam.h` | `add_pattern`, `relevant_eh`, `add_eq_eh`, `match`, `rematch`, `on_match`, `push_scope`/`pop_scope` |
| instruction set | `mam.cpp:112` | `INIT1..INITN, BIND1..BINDN, YIELD1..YIELDN, COMPARE, CHECK, FILTER, CFILTER, PFILTER, CHOOSE, NOOP, CONTINUE, GET_ENODE, GET_CGR1..GET_CGRN, IS_CGR` |
| `code_tree` | `mam.cpp:381` | one tree per top-level pattern function symbol, holds pending candidate enodes |
| `code_tree_manager` | `mam.cpp:606` | allocation of instructions/trees in a region |
| `compiler` | `mam.cpp:790` | multi-pattern -> code tree, and *insertion* of a new pattern into an existing tree (prefix sharing) |
| `interpreter` | `mam.cpp:1859` | the abstract machine: registers, bindings, `backtrack_stack` |
| `code_tree_map` | `mam.cpp:2897` | `func_decl -> code_tree`, scoped |
| `path` / `path_tree` | `mam.cpp:3020` / `3060` | inverted path index, used on merges |
| `mam_impl` | `mam.cpp:3122` | owns trees, `m_pc`/`m_pp` tables, label filters, `m_to_match` |
| `quantifier_manager` (+ `default_qm_plugin`) | `smt_quantifier.{h,cpp}` | drives the mam from solver events; `add_instance` -> fingerprint -> queue |
| `qi_queue` | `qi_queue.{h,cpp}` | instance cost, eager threshold, delayed entries, scoped instance store |
| `fingerprint_set` | `fingerprints.{h,cpp}` | duplicate-instance filter, keyed on (q, binding roots) |
| labels on enodes | `smt_enode.h:83,102-103` | `m_lbl_hash`, `m_lbls`, `m_plbls` |
| `approx_set` | `util/approx_set.h` | 64-bit bitset of label hashes |

### 2.1 Two matchers, two triggers for work

`default_qm_plugin` keeps **two** mams: `m_mam` (eager) and `m_lazy_mam`.
`assign_eh(q)` (i.e. when `q` is assigned true) adds each multi-pattern to one
of them: unary patterns and the first `qi.max_eager_multipatterns` (default 0,
+1 if the quantifier has no unary pattern) multi-patterns go to the eager mam,
the rest to the lazy mam. The lazy mam only maintains labels
(`relevant_eh(e, lazy=true)`) and is `rematch()`-ed at final check, at most
`qi.max_lazy_multipattern_matching` (default 2) times.

So "eager" in z3 means: *unary patterns, and at most one multi-pattern per
quantifier, are matched during propagation; the rest wait for final check.*

### 2.2 Where matching work comes from

Two, and only two, sources, both incremental:

* **A new term becomes relevant** — `mam::relevant_eh(n, lazy)`
  (`mam.cpp:4005`). Updates `n`'s class label sets, and if `n` is an
  application whose symbol has a code tree, pushes `n` as a *candidate* onto
  that tree (`add_candidate`, `mam.cpp:3191`). The tree is queued in
  `m_to_match`.
* **Two classes merge** — `mam::add_eq_eh(r1, r2)` (`mam.cpp:4032`).
  Runs `process_pc(r1,r2)`, `process_pc(r2,r1)`, `process_pp(r1,r2)`, then
  unions the label sets (`r2_lbls |= r1_lbls`, `r2_plbls |= r1_plbls`, both
  trailed). `process_pc`/`process_pp` (`mam.cpp:3755`,`3715`) consult the
  `m_pc[h1][h2]` / `m_pp[h1][h2]` path-tree tables indexed by *label hashes*
  and call `collect_parents` (`mam.cpp:3556`) on the smaller class, which
  walks up parents along the recorded paths and adds candidates to the code
  trees reachable from the path tree.

  **This is called before the merge is performed** (`smt_context.cpp:544`,
  inside `context::add_eq`, before `remove_parents_from_cg_table(r1)`), so
  `r1` and `r2` still have their own parent lists and the congruence table
  still reflects the pre-merge state. Faithfulness depends on this.

`mam::match()` (`mam.cpp:3930`) then runs the interpreter over every queued
tree's candidates and clears them; it is called from
`default_qm_plugin::propagate()`, i.e. inside the solver's propagation
fixpoint, and `can_propagate()` is true exactly when `m_mam->has_work()`.
Newly added patterns are matched against all existing enodes of their root
symbol once, via `match_new_patterns()` (`mam.cpp:3772`) using a throwaway
tree.

`pop_scope` (`mam.cpp:3897`) *discards* pending candidates (`m_to_match`) and
pending new patterns — work queued at a level that is being popped is dropped.

### 2.3 Filtering

Three mechanisms, all approximate and all cheap:

* `label_hasher` (`mam.cpp:68`): `func_decl -> 6 bit hash` (`APPROX_SET_CAPACITY
  = 64`, so `hash & 63`).
* Per class root: `lbls` = hashes of symbols of applications *in* the class
  (plus `lbl_hash` of pattern ground terms), `plbls` = hashes of symbols of
  applications having a member of the class as an *argument*.
* `FILTER`/`CFILTER` backtrack when `instr.lbl_set ∩ root.lbls = ∅`;
  `PFILTER` the same against `root.plbls` (`mam.cpp:2463`). `m_is_clbl[f]` /
  `m_is_plbl[f]` record which symbols need to be tracked at all, so classes
  are only annotated for symbols that actually occur in a pattern.

### 2.4 From match to instance

`interpreter` `YIELD` -> `mam::on_match` (`mam.cpp:3978`) ->
`context::add_instance` -> `quantifier_manager::imp::add_instance`
(`smt_quantifier.cpp:288`):

1. `max_generation = max(max_generation, generation(q))`.
2. `context::add_fingerprint(q, q->get_id(), num_bindings, bindings)` — returns
   null if this (q, binding-roots) tuple was already instantiated. **This is
   the duplicate filter.**
3. `qi_queue::insert(f, pat, max_generation, min_top_generation,
   max_top_generation)`.

`qi_queue::instantiate()` (`qi_queue.cpp:150`) walks the new entries:
`cost <= m_eager_cost_threshold` (`qi.eager_threshold`, default 10) -> add now;
otherwise, if `qi.promote_unsat` and the instance body is already false under
the current assignment, add now anyway; otherwise push to `m_delayed_entries`.
The cost is a user-specifiable arithmetic expression over
`weight, generation, min/max_top_generation, instances, size, depth, vars,
pattern_width, total_instances, scope, nested_quantifiers, cs_factor`
(default `(+ weight generation)`), evaluated by `cost_evaluator`.

Adding an instance (`qi_queue.cpp:199`) means: substitute bindings, *rewrite*,
drop if it simplified to true, build `(or (not q) body)` (flattened if body is
an `or`), store it in `m_instances`, and `context::internalize_instance(lemma,
pr, new_generation)`. `new_generation` comes from a second cost expression
`qi.new_gen` (default: `generation + 1` unless overridden).

Backtracking (`qi_queue.cpp:367`): `m_delayed_entries`, `m_instances` and the
`m_instantiated_trail` are shrunk to the scope's watermark, and entries that
were instantiated lazily get `m_instantiated = false` again. `m_new_entries` is
dropped entirely. At final check, `final_check_eh` (`qi_queue.cpp:404`)
instantiates delayed entries whose cost is `<= qi.lazy_threshold` (or, with
`qi.conservative_final_check`, only the cheapest ones) and returns false if it
did anything, which keeps the search going.

## 3. Our architecture

```
  master equality engine ──(eqNotifyNewClass / eqNotifyMerge / eqNotifyDisequal)──┐
                                                                                  v
                                                                        EagerEqNotify
                                                                                  │
   EagerInstEngine (QuantifiersModule)                                            │
     ├── EGraph        mirror of the master e-graph  <───────────────────────────┘
     │                 union-find, parent lists, cg table, label sets, own trail
     ├── Mam           code trees, compiler, interpreter, pc/pp path trees
     ├── InstQueue     fingerprints, cost, eager threshold, delayed entries
     └── InnerSmtSolver
           ├── InnerEGraph   congruence closure with *removal*
           ├── InnerArith    (planned) own arithmetic solver
           └── clause store  instances, added/removed z3-style
                 └── exports conflicts / propagations to cvc5
```

| our component | file | z3 counterpart |
| --- | --- | --- |
| `ApproxSet`, `LabelHasher` | `approx_set.h` | `util/approx_set.h`, `mam.cpp:68` |
| `Trail` | `trail.h` | `util/trail.h` (`trail_stack`) |
| `ENode`, `EGraph` | `egraph.{h,cpp}` | `smt_enode.h` + the e-graph part of `smt_context` |
| instructions, `CodeTree`, `Compiler`, `Interpreter`, `PathTree`, `Mam` | `mam.{h,cpp}` | all of `mam.cpp` |
| `Fingerprints`, `InstQueue` | `inst_queue.{h,cpp}` | `fingerprints.{h,cpp}`, `qi_queue.{h,cpp}` |
| `PatternInference` | `pattern_inference.{h,cpp}` | `ast/pattern/pattern_inference.cpp` |
| `InnerEGraph` | `inner_egraph.{h,cpp}` | — (z3 reuses the main e-graph) |
| `InnerArith` | `inner_arith.{h,cpp}` | — (z3 reuses `theory_arith`) |
| `InnerSmtSolver` | `inner_smt_solver.{h,cpp}` | the instance-holding part of `smt_context` |
| `EagerInstEngine`, `EagerEqNotify` | `eager_inst_engine.{h,cpp}` | `quantifier_manager` + `default_qm_plugin` |

### 3.1 Why we mirror the e-graph instead of reading cvc5's

The MAM needs, per equivalence class: the cyclic list of class members, the
list of *parent* applications of the whole class, two mutable approximate
label sets, and a congruence-root flag per node. cvc5's `EqualityEngine`

* curries `APPLY_UF` into binary internal nodes and does not notify for them,
  so n-ary application structure is not directly available from the callbacks;
* exposes use-lists over the curried representation rather than per-class
  parent lists;
* has no slot to hang per-class annotations on, and no removal;
* notifies merges **after** the merge, and after congruence has already been
  propagated (`equality_engine.cpp:872`, after `class1.merge(class2)`), while
  z3's `add_eq_eh` needs the pre-merge view (see 2.2).

Keeping our own union-find and performing the union *lazily*, when the
notification arrives, recovers exactly z3's pre-merge view: at the moment we
are told `t1` and `t2` were merged, our own structure still has them apart, so
`processPc`/`processPp` see the same thing z3 sees. This is the single most
important reason the mirror exists.

The mirror is also what makes "own congruence closure, with removal" possible
for the `InnerSmtSolver` without touching `EqualityEngine`.

### 3.2 Scope handling

z3 pushes/pops the mam and the queue explicitly from `smt_context`. We do not
get push notifications from cvc5's `Context`, so every public entry point of
`EagerInstEngine` first calls `syncScopes()`, which compares
`context()->getLevel()` with the level our `Trail` is at and pushes/pops the
difference. The level alone misses a pop followed by a push back to the same
level between two calls, so a context-dependent copy of the last synced level
(`d_syncedLevel`) tells how many of our scopes the context still has. Since all of our state is private, the only requirement is that it
be correct when read, and reads only happen through these entry points.

### 3.3 When do we match?

z3 calls its quantifier manager from `context::propagate`, i.e. once per round
of the propagation fixpoint, and that call both runs the matcher and turns the
matches into instances (`quantifier_manager::imp::propagate`). The cvc5
analogue is `Theory::propagate(Effort)`, so `TheoryQuantifiers` declares the
`propagate` property and `EagerInstEngine::propagate` runs `Mam::match()`
followed by `InstQueue::instantiate()` there. That path produces no output.

What the inner solver derives is flushed separately, from
`TheoryQuantifiers::postCheck` before the quantifiers round, where cvc5 expects
output.

We deliberately do **not** make the module request a check at standard effort:
that would force a full quantifiers round (resetting every utility, module and
the model) at every propagation, which changes what the other quantifiers
modules see. An earlier version did, and it changed the answer of
`regress1/quantifiers/issue4433-nqe.smt2`.

`--eager-inst-match-mode=notify` runs `Mam::match()` directly from the e-graph
notifications, which is strictly more eager than z3. It finds the same matches
(a candidate is executed exactly once either way, and a match enabled by a
later merge is found by the merge path at that later point), just earlier and
in a different order.

### 3.4 Pattern inference

Most quantified formulas carry no usable pattern annotation, and which
instances exist at all is decided by the inferred patterns, so matching z3
requires inferring the same ones. `PatternInference` is a port of z3's
`pattern_inference_cfg` with z3's default parameters: `pi.arith=1`
(conservative), `pi.block_loop_patterns`, `pi.decompose_patterns`,
`pi.max_multi_patterns=0`, `pi.avoid_skolems`.

The passes, in z3's order: collect the candidate subterms (applications that
contain a variable of the quantifier, contain no variable bound inside the
body, and are not forbidden), drop the strictly smaller ones
(`filter_looping_patterns` via `smaller_pattern`), drop the ones that contain a
sub-candidate with the same variables (`filter_bigger_patterns`), turn the
candidates that bind every variable into unary patterns, and build at most one
multi-pattern out of the rest. Arithmetic is forbidden in the first pass,
allowed inside patterns in the second, and allowed as the top symbol of a
pattern in the third. `mk_pattern`'s decomposition is included, which is why
z3 and we both infer `(h x)` for `(forall x. p (f (h x)))` and `((+ x 1))` for
`(forall x. p (f (+ x 1)))`.

cvc5's `PatternTermSelector` is not used: it ranks candidates differently and
does not decompose, so it would make the instances differ from z3's for reasons
unrelated to the matcher.

## 4. The e-graph mirror

`EGraph` (file `egraph.{h,cpp}`) is a fresh congruence closure:

* `ENode`: `d_node` (the cvc5 `Node`), `d_args` (our enodes), `d_find`,
  `d_next` (cyclic class list), `d_size`, `d_parents`, `d_lbls`, `d_plbls`,
  `d_lblHash`, `d_cgr`, `d_generation`.
* `addTerm(n)`: called from `eqNotifyNewClass`. Creates enodes bottom-up for
  `n` and any argument we have not seen (cvc5 guarantees arguments are added
  first, but we do not rely on it). Mirrors `relevant_eh`: updates the class
  label sets and registers the node as a candidate with `Mam`.
* `assertEq(t1, t2)`: called from `eqNotifyMerge`. Resolves *our* roots,
  returns immediately if already equal, otherwise calls
  `Mam::addEqNotify(r1, r2)` **first** (z3 order), then performs the union and
  the label-set union, pushing undo entries on the `Trail`, then repairs the
  congruence table and enqueues any congruences it discovers.
* Generations: `generation(n)` is the instantiation depth at which `n` was
  created; terms coming from the input have generation 0, terms created by an
  instance of generation `g` get `g` from the `InstQueue` (z3's
  `context::internalize_instance(lemma, pr, gen)`).

Removal: the trail supports undo of both scope pops and explicit retraction,
because the inner solver retracts instances (section 6). The mirror itself
only uses the scope-pop path.

## 5. Instance queue

`InstQueue` is `qi_queue` with the same entry record and the same two-phase
policy (eager vs delayed by cost against a threshold, delayed replayed at
final check). Differences from z3 that we keep deliberately:

* The cost *function* is fixed to z3's default `(+ weight generation)` rather
  than a parsed expression, with the same variable set available; a parser can
  be added later if we want to reproduce z3 command lines verbatim.
* `Fingerprints` is keyed on `(q, roots of bindings)` exactly as z3; it is
  our only duplicate filter. We do **not** consult cvc5's `InstMatchTrie`:
  the two instantiation paths must not share dedup state, or they would mask
  each other's work.

## 6. The inner SMT solver

The point of the `InnerSmtSolver` is that an eager matcher produces far more
instances than the outer SAT solver should see, and that z3's instance
lifecycle (add at a scope, drop on pop, re-add later at a different cost
threshold) does not map onto cvc5's lemma channel, which is monotone and
global. So instances go into a solver we control.

It is a **propagation-only CDCL(T)**: Boolean unit propagation over the
instance clauses, with `InnerEGraph` as its theory, and no decisions. That is
the shape the instances call for: an instance clause is `(or (not q) body)` and
`q` holds in the outer context, so the clause behaves as `body` does, and most
bodies are units.

* `addInstance(q, bindings, lemma)` stores the clause, interns its atoms, and
  internalizes its terms into `InnerEGraph`. Atoms, clauses and terms are
  retracted together when the scope the instance was added at is popped, as
  z3's `qi_queue::pop_scope` does with its instance store.
* `InnerEGraph` is a congruence closure with an explicit undo log, so a
  retracted instance's terms leave the structure instead of accumulating — this
  is why it is not `EqualityEngine`. It maintains a **proof forest** beside the
  union-find: every asserted or derived equality adds an edge, and the path
  between two terms explains their equality, recursing into the arguments at a
  congruence edge. That is what makes a minimized conflict possible.
* **The outer assignment is read, not pushed.** The atoms the inner solver
  cares about are known, so `check()` asks the outer solver for their value
  (`Valuation::hasSatValue`). Equalities and disequalities between its terms
  come from the e-graph mirror, which the solver listens to: each mirror class
  that contains one of our terms has an *anchor*, one such term. A new term in
  an anchored class, or a mirror merge of two anchored classes, gives an outer
  equality between anchors; an outer disequality between two anchored classes
  gives an outer disequality. Each such fact is entailed by the outer context,
  whatever reason the master equality engine had for it, so each is sound as a
  root of an explanation. A disequality between classes that were not both
  anchored is caught later: when our congruence closure merges classes, the
  outer classes the merged class contains are tested pairwise with
  `areDisequal` (`checkTouchedClasses`).
* **It is incremental.** What a round derives stays until the outer scope it
  was derived at is popped: the state is saved on the first change in each
  scope of the trail and restored when that scope is popped, which also
  retracts the instances added in it. Each round only processes what changed:
  the clauses added since the last round, the pending outer facts, and the
  atoms watching a term whose class was merged (collected from the merge
  notifications of `InnerEGraph`). A round that ends in a conflict is undone,
  so the state is never left inconsistent.
* A predicate application is given a presence in the congruence closure by
  merging it with `true` or `false` when it is assigned, which is how
  congruence over predicates is obtained; `true` and `false` are asserted
  disequal once.
* `InnerArith` will do the same for linear arithmetic. The instances eager
  matching produces are often arithmetic-heavy, and without an arithmetic
  solver the inner solver cannot detect most of the conflicts it is there to
  find. Planned as a fresh simplex with retraction, same reason as above.

### 6.1 What is exported, and why it is sound

A conflict is exported as the clause

```
(or  ¬L_1 ... ¬L_k  (not q_1) ... (not q_m) )
```

where the `L_i` are the outer literals the derivation used and the `q_j` the
quantified formulas whose instances it used. Each instance is entailed by its
`q_j`, so the clause is entailed by the assertions no matter how the inner
solver derived it — the inner solver does not have to be trusted. The
explanation is collected by walking the implication graph back to its roots;
since there are no decisions, that is a reachability traversal rather than
resolution.

Propagations are exported the same way, as `exp => lit`, bounded per round,
and only for atoms the outer solver already has a variable for.

Two things the export must respect, both found by the regressions:

* **Quantifier ownership.** A module that owns a quantified formula may claim
  to be complete for it, which it is not if somebody else instantiates it. Like
  cvc5's lazy E-matching (`InstantiationEngine::shouldProcess`), the module
  skips the quantifiers it does not own. z3 has no equivalent, having one
  instantiation mechanism.
* **Instantiation bookkeeping.** Exporting a clause that mentions `(not q)`
  instantiates `q` in effect, so the used instantiations are recorded with
  cvc5's `Instantiate`; when the clause follows from a single instance it is
  sent through `Instantiate::addInstantiation` instead, which keeps cvc5's
  rewriting, duplicate filtering and proof support in play.

### 6.2 What it does not find

The inner solver reasons about the terms its instances mention plus the outer
facts that hold among them. A conflict that additionally needs an outer term
that no instance mentions is not found: for

```
(forall ((x U)) (! (= (f x) (g x)) :pattern ((f x))))   (= a b)   (not (= (f a) (g b)))
```

the instance gives `f(a) = g(a)`, and the contradiction needs `g(b)`, which the
inner e-graph has no reason to know about. z3 does not have this problem,
because its instances are internalized into the solver that owns `g(b)`.
Importing the outer class members and parents of the terms it knows would close
this, at the cost of duplicating a growing part of the outer e-graph.

## 7. Plug-in points in cvc5 (all of the edits outside this directory)

* `options/quantifiers_options.toml`: `--eager-inst` (off by default),
  `--eager-inst-output=inner|lemma`, `--eager-inst-match-mode=check|notify`,
  `--eager-inst-filters`, `--eager-inst-max-eager-multipatterns=N`,
  `--eager-inst-max-lazy-multipattern-matching=N`.
* `theory/inference_id.{h,cpp}`: `QUANTIFIERS_INST_E_MATCHING_EAGER`.
* `theory/quantifiers/quantifiers_modules.{h,cpp}`: construct
  `EagerInstEngine` when the option is set.
* `theory/quantifiers/master_eq_notify.{h,cpp}`: `MasterNotifyClass` forwards
  new-class/merge/disequal notifications to a list of extra listeners.
* `theory/ee_manager_central.cpp`, `theory/ee_manager_distributed.cpp`:
  register the module's listener — in the central architecture directly in the
  central notify lists (the master notify is only registered for new classes
  there), otherwise through `MasterNotifyClass`.
* `theory/quantifiers_engine.{h,cpp}`: expose the listeners of the modules, and
  `eagerPropagate`/`eagerCheck`.
* `theory/quantifiers/kinds.toml`: the quantifiers theory declares the
  `propagate` property, so that `Theory::propagate` is called for it.
* `theory/quantifiers/theory_quantifiers.{h,cpp}`: `propagate` runs the
  matcher, `postCheck` flushes what the inner solver derived (section 3.3).

## 8. Deliberate deviations from z3

1. Separate e-graph mirror instead of the solver's own e-graph (section 3.1).
   Consequence: we see merges one step later than z3 would, but with the same
   information.
2. Relevancy: z3 drives `relevant_eh` from its relevancy propagation. cvc5 has
   no relevancy by default, so we behave like z3 with `relevancy=0`, which
   feeds *all* internalized enodes to the matcher
   (`default_qm_plugin::propagate`, the `m_new_enode_qhead` loop).
3. Instances go to `InnerSmtSolver`, not to the SAT solver (section 6).
4. Cost function fixed rather than parsed (section 5).
5. The instance queue is drained one round later than z3 drains it: z3 creates
   the instance in the same `propagate` call that found the match, and so do
   we, but what the inner solver derives from it is reported at the next check
   (section 3.3).
6. Counterexample terms: cvc5 marks the inst-constant form of a quantified
   formula, and the terms that sygus instantiation introduces to represent a
   counterexample, with the instantiation-constant attribute. It is
   model-unsound to instantiate with those — `Instantiate` rejects them
   outright — so the mirror drops them, as `TermDb::addTerm` does. Before this
   filter, instances built from them turned `unsat` into `sat` on several
   `cegqi` regressions and produced a model that `--debug-check-models`
   rejected under `--sygus-inst`.
6a. Quantifier ownership: the module only handles the quantified formulas it
   owns (section 6.1).
7. Ground terms occurring in patterns: z3 internalizes them into the solver
   (`mk_enode` in `mam.cpp`), so the solver reasons about them. We only add
   them to the mirror, which means equalities involving a pattern ground term
   that is otherwise unknown to cvc5 are never reported to us. See section 10.
8. Pattern inference omits z3's `pi.pull_quantifiers` pass, so a quantifier
   whose only candidate patterns lie under a nested quantifier gets none, and
   the pattern database (`pi.use_database`, off by default in z3).
9. Preprocessing: patterns are inferred from cvc5's preprocessed body, z3's
   from z3's. Where the two preprocessors disagree, the patterns and hence the
   instances disagree.

## 9. Status and implementation plan

Implemented:

* the notification path from the master equality engine, in both the central
  and the distributed equality engine architectures;
* `EGraph`: classes, parent lists, the congruence table (hence `isCgr` and
  `getENodeEqTo`), the two label sets, generations, and backtracking of all of
  it through `Trail`, with the pre-merge notification (`-t eager-egraph`);
* the label filters and the inverted path index `m_pc`/`m_pp`, and the merge
  path `processPc`/`processPp`/`collectParents` (`-t eager-mam`);
* `Compiler`: multi-pattern to code tree, and insertion into an existing tree
  with prefix sharing, `CHOOSE`/`NOOP` splitting, `find_best_child`, the
  `FILTER`/`CFILTER` compatibility rules, `GET_CGR` and `IS_CGR`
  (`-t eager-mam-compiler`);
* `Interpreter`: the whole instruction set including `CONTINUE` with depth-1
  and depth-2 joints, and the backtracking stack (`-t eager-mam-exec`);
* `matchNewPatterns`, i.e. matching a newly added pattern against the terms
  that already exist, through a throwaway code tree;
* `PatternInference` (section 3.4);
* `InstQueue` with `Fingerprints`, the cost/threshold split and the delayed
  entries; `InnerSmtSolver`'s instance store with retraction, over an
  `InnerEGraph` that is a congruence closure with an explicit undo log;
* the module, the options, the statistics (`-t eager-inst-stats`) and the match
  log used for comparing against z3 (`-t eager-inst-match`).

* `InnerSmtSolver`: atom and clause interning with retraction, Boolean unit
  propagation, the congruence closure as its theory, implication-graph
  explanations, reading the outer assignment and the outer (dis)equalities, and
  the export of conflicts and bounded propagations (`-t eager-inner`);
* `InnerEGraph`: the proof forest and `explain`.

Not implemented yet:

* `InnerArith`, so an arithmetic conflict among instances is not seen;
* decisions in the inner solver, so it is propagation-complete but not
  refutation-complete over its clauses; an instance body that is not a clause
  is taken as an opaque atom rather than being Tseitin-encoded;
* importing outer terms into the inner e-graph (section 6.2);
* z3's `pi.pull_quantifiers` pass and pattern database.

Remaining plan:

1. `InnerArith`: a retractable simplex, without which the inner solver cannot
   see most of the conflicts it exists to find.
2. Decisions and Tseitin encoding in the inner solver, to make it complete over
   its own clauses.
3. Performance: the congruence tables and the code tree map are `std::map` with
   `Node`/vector keys; z3 uses hash tables with small ids. The inner solver
   evaluates a clause in full on each visit (no watched literals), reads the
   value of every unassigned atom each round, and `InnerEGraph` scans all of its
   disequalities after each merge. The path trees and the
   throwaway trees of `matchNewPatterns` are never freed.

## 9.1 Comparing against z3

`-t eager-inst-match` logs one line per match, with the bindings canonicalized
to their class representatives, which is what z3 logs for a match
(`log_add_instance`, under `trace=true`). `contrib/compare-eager-ematching.py`
parses z3's `z3.log` and our trace and compares the multisets of bindings; it is
the test harness for "do we produce the instances z3 produces".

On a battery of 15 small benchmarks covering unary, nested, ground-argument,
multi-pattern (2 and 3 terms), shared-top-symbol, `IS_CGR`, congruence,
merge-driven and inferred-pattern cases, run with cvc5's own instantiation
strategies disabled (`--no-e-matching --no-cegqi --no-enum-inst --no-cbqi
--no-mbqi`) and z3's model-based instantiation disabled (`smt.mbqi=false`), 13
produce *identical* match multisets. The two that differ are ones where z3
stopped matching as soon as it had a conflict and we did two more matches, i.e.
our set is a strict superset; the patterns and the matches agree.

On large real benchmarks the comparison is dominated by preprocessing
differences between the two solvers (deviation 9) rather than by the matcher.
## 10. Open questions

* Do we need `eqNotifyPreMerge` in `EqualityEngine` after all? The mirror
  makes it unnecessary, at the cost of duplicating the congruence closure. If
  the mirror turns out to be the bottleneck, a pre-merge callback plus direct
  reads of cvc5's structures is the alternative.
* Which notification covers terms that the master e-graph never sees (e.g.
  terms only known to a theory with its own equality engine in the
  non-central architecture)? z3 has one e-graph; we may under-approximate.
* Generation bookkeeping needs a home: instances created by the inner solver
  do not enter cvc5's term database, so `generation` must be maintained purely
  inside `EGraph`/`InnerEGraph`.
* Interaction with the lazy path: both will instantiate. Do we let them, or
  does `--eager-inst` eventually imply `--no-e-matching`?
* Ground terms of patterns (deviation 7): do we register them with cvc5, e.g.
  by asking the quantifiers theory to pre-register them, or do we accept that
  the mirror knows terms the solver does not?

## 11. Trying it

```
cvc5 --eager-inst -t eager-egraph -t eager-mam -t eager-inst-stats file.smt2
```

Trace tags: `eager-egraph` (terms and merges of the mirror), `eager-mam`
(patterns, candidates, machine execution), `eager-inst-queue` (entries and
instances), `eager-inner` (the inner solver), `eager-inst` (conflicts and
propagations), `eager-inst-debug` (scope changes), `eager-inst-stats`.

# DGamma

DGamma is a constructive Idris 2 mechanization of Yifan Shi, Wei Zhang, and
Tianyi Cui's paper [*A Programming Paradigm for Spatiotemporal
Composability*](https://github.com/cordiverse/paper). The paper develops the
Cordis model of reversible effects, reactive coeffects, component lifecycles,
and dynamic plugin composition. This repository turns those definitions and
their main metatheory into executable, indexed Idris programs and proofs.

The release tree is intentionally axiom-free: every Idris module uses
`%default total`, and `src/` contains no `believe_me`, `assert_total`,
postulate, partial default, or metavariable hole. Proofs are erased where
appropriate, but the evaluator, effect maps, inverse stacks, registries, and
context operations are executable. This matters because several plausible
paper proofs and several early versions of our own statements failed only when
we connected them back to the real evaluator.

The main calculus is proved through Lemma 72. This includes Preservation
(Theorem 59), recovery and temporal composability (Theorem 61, Corollary 62,
and Theorem 64), spatial Ordering (Theorem 63), Progress (Theorem 66), support
well-foundedness and quiescent support (Lemmas 68 and 70), and Deletion (Lemma
72). Confluence (Theorem 73) is not proved: its proof has been scoped, with
checked research interfaces, on branch
[`cp5-thm73-scoping`](https://github.com/Termina1/dgamma/tree/cp5-thm73-scoping).
A few Section 3 universal-property theorems remain honest, uninhabited `Type`s,
and Definition 32 is represented only by finite approximations. The exact
status of every numbered item is in the [theorem index](docs/THEOREM-INDEX.md).

## What we found in the paper

Most of the differences below are formal repairs: places where mathematical
prose leaves an implementation-relevant quantifier, category, or observation
implicit. Two findings are more serious. In those two cases, the operational
rules as written permit a running system to do something that the metatheory
later declares impossible—with direct consequences for dependency safety,
teardown, and hot reload.

### Bugs with real consequences for a running system

#### A scheduler can wire components into a dependency cycle the framework believes impossible

*(Paper Lemma 68; NOTES erratum #3.)*

- **What the paper says.** Section 4.4.5, Lemma 68 says support is well
  founded. Its proof argues that a child is registered by a particular
  activation and therefore is born after that activation's L-Begin.
- **What can actually happen under Table 1.** O-Insert asks only that parent
  `A` is present, child name `S` is fresh, and provisions are disjoint. It does
  not record which iterator step of `A` requested `S`. A scheduler can therefore
  insert `S` while merely pointing at `A`; with only phase/order bookkeeping,
  children from alternating subtrees can be arranged so their support edges
  form a cycle. Every individual transition is legal by the letter of Table 1,
  yet the resulting support graph violates the well-foundedness used by the
  proof. A teardown or hot-reload traversal that assumes this graph is acyclic
  may fail to find a leaf and stop making progress.
- **What a runtime must do.** This is not fixed by rewording Lemma 68. A
  Cordis-like runtime must track the iterator step that requested each child
  registration. [`RegistrationProvenance`, `ParentRegistrationYield`, and
  `RegistrationDiscipline`](src/DGamma/CP3.idr) tie O-Insert to the actual
  nonempty iterator head, a deterministic protocol catalog tag, and strict
  component ranks; every child also has its own later retirement obligation.
  The proof is in
  [`CP4SupportSolution`](src/DGamma/CP4SupportSolution.idr), with executable
  premise regressions in
  [`CP3StatementChecks`](src/DGamma/CP3StatementChecks.idr).

The finite catalog is an explicit host representation. Because O-Insert is a
separate rule and does not consume the source head, it can license more than one
fresh child of the same ranked component. That is an over-approximation of one
paper Definition-47 application, and it is documented rather than hidden; each
admitted child still has a strictly higher rank and an independent retirement
obligation.

#### Reusing a freed name confuses two different components that lived under it

*(Paper Lemmas 56 and 72; NOTES ambiguity 7 and CP4 Finding #8.)*

This is the classic identity bug in a hot-module-reload system: a string or
integer name is not a lifetime identity.

- **Why one raw-name bijection fails.** Section 4.3.5, Lemma 56 applies one
  bijection `χ : N → N`, while the same section permits O-Remove followed by
  reuse of the freed name. Suppose one run has a generated child called `S` and
  another fresh-choice run calls that historical child `T`. Both children are
  removed. The orchestrator then inserts a new external root called `S` in both
  runs. Matching history requires `S ↦ T`; matching the current external input
  requires `S ↦ S`. No single raw-name bijection can express both facts.
- **How deletion harms an innocent replacement.** Lemma 72 writes `R` as the
  names registered during `A`'s closing episode and deletes later actions at
  names in `R`. Let `A` register `S`, retire it, and remove it. Later, legally
  insert an unrelated root under the now-free name `S`. The literal raw-name
  filter remembers only `S ∈ R` and withdraws this innocent reissued component
  as though it still belonged to `A`.
- **Executable counterexample.** The ten-step trace in
  [`CP4DeletionGenerationChecks`](src/DGamma/CP4DeletionGenerationChecks.idr)
  proves that the old filter deletes the later root O-Insert and that the
  repaired filter keeps it. Role-change and cross-parent traces also live in
  [`CP3StatementChecks`](src/DGamma/CP3StatementChecks.idr); the final
  adversarial assessment is
  [`review-cp3-round10.md`](review-cp3-round10.md).
- **Runtime repair.** Identity is `(raw name, birth ordinal)`, not just a raw
  name. [`RegistrationGenerationBijection`](src/DGamma/CP3.idr) renames
  historical births; [`CurrentEndpointRenaming`](src/DGamma/CP3.idr) separately
  renames live names and fixes external roots. Lemma 72's
  [`GenerationActionSubsequence`](src/DGamma/CP3.idr) and the
  `CP4DeletionGeneration*` scanners stamp each birth/action. Premises,
  filtering, outside-control equality, and withdrawal all use the same stamp.

### Claims the paper's own tests cannot check

In these cases two behaviors can differ in something the runtime later exposes,
yet pass all observations supplied by the original statement.

#### Two different yielded undo functions can pass every fixed-undo test

*(Paper Lemma 35; NOTES ambiguity/erratum 2.)*

- **What the paper says.** Section 3.3.2, Lemma 35 says
  indistinguishability is the coarsest relation respected by operations. The
  surrounding observer language tests one fixed inverse at related values.
- **Invisible-to-the-test difference.** Run an operation at indistinguishable
  origins `v` and `v'`. It returns the same visible value but dynamically
  yields undo functions `u` and `u'`. Every test that selects one fixed undo
  and applies that same function on both sides can pass, while `u` and `u'`
  give different results on one common probe. The paper's tests never compare
  the two functions that were actually yielded.
- **Repair and status.** [`FixedInverseStep` and
  `YieldedInverseStep`](src/DGamma/Unified.idr) make those two observations
  distinct; the latter applies the dynamically yielded inverses to a common
  probe. The redesigned universal-property statements remain `TODO(proof)`.
  This is an honest open Section 3 item, not an assumed theorem.

#### Two visibly different errors counted as the same outcome

*(Paper Definition 60, Equations 54–55; NOTES CP4 Finding #13.)*

- **What the paper says.** Section 4.4.2 says to read `Right` around the
  yielded triple and compares only projections 2 and 3. It does not require two
  failing evaluations to raise the same error.
- **Visible counterexample.** Let one iterator raise `ColdError` when ambient
  state is cold and `HotError` when it is hot. The old premise projects both
  runs to “undefined,” so they appear stable. L-Raise then stores the concrete
  error in `Unloading`, and two schedules finish with observably different
  controls. Lemmas 71/72 and Theorem 73 cannot transpose that step.
- **Repair.** [`IteratorStageOutcome` and
  `IteratorOutcomeAgreement`](src/DGamma/Metatheory.idr) distinguish
  unavailable, raised, and yielded outcomes and require exact error agreement.
  [`CP4FailureOutcomeChecks`](src/DGamma/CP4FailureOutcomeChecks.idr) inhabits
  the old premise, refutes its endpoint conclusion, and also constructs a
  genuinely failing trace accepted by the repaired premise.

#### A locally witnessed inverse is not automatically uniform everywhere

*(Paper Theorem 15; NOTES clarification 4.)*

- **What the paper says.** Section 3.1.3, Theorem 15 fixes origin `γ`, obtains
  inverse `g` there, and then gives an “if and only if” characterization over
  all accumulators/probes.
- **Quantifier gap.** An undo token produced at `γ` can be known to restore the
  state reached from `γ`. That local witness says nothing about applying the
  same token to a state produced from another origin. Moving from “works here”
  to “works for every `φ` and probe” needs a uniformity hypothesis.
- **Repair.** [`effectLiftWitnessIff`](src/DGamma/Effects.idr) makes the scope
  explicit: restoration for every accumulator and probe is equivalent to the
  yielded inverse being uniform against the complete forward map. The theorem
  is proved pointwise, without function extensionality.

### Places where prose math and machine-checked math part ways

These are not all runtime bugs. Some are conventional abstractions that are
reasonable on paper or in TypeScript but require a more precise statement in a
total proof assistant.

#### The “infinite context” is understandable notation, not a literal inductive datatype

*(Paper Definition 32, Equation 31; NOTES ambiguity/erratum 1.)*

- **Paper convention.** Section 3.3.1 writes
  `Γ∞ = μΓ. Γ × (Γ → Γ) × Σ`. In ordinary implementation prose, one can imagine
  an object whose callback accepts another object of the same interface.
- **Where the literal reading fails.** For an inductive datatype, `Γ` occurs to
  the left of an arrow: the constructor would consume arbitrary complete
  values of its own type. This negative, non-strictly-positive occurrence is
  rejected by Idris because accepting it naïvely breaks normalization. The
  useful intuition is a ladder of boxes: level `n+1` may contain functions over
  level `n`, but there is no final inductive box containing the entire ladder.
- **Repair.** [`ContextTower` and
  `GammaInfinityApprox`](src/DGamma/Unified.idr) implement those finite levels.
  We do not claim a solution of the unqualified equation; a literal `Γ∞` needs
  guarded recursion or domain theory not supplied by the paper.

#### Partial operations do not form the total monoid used in the earlier section

*(Paper Definition 24 and the Definition-39 development; NOTES clarification
3.)*

- **Paper convention.** Coeffect operations/inverses have preconditions, while
  Section 3.1 presents generated transformations as total endomorphisms.
- **Concrete mismatch.** `setFresh(k, value)` succeeds while `k` is absent and
  fails after `k` exists. Treating that failure as a total state map—or as
  identity—changes which programs execute and invalidates inverse composition.
- **Repair.** [`Coeffects`](src/DGamma/Coeffects.idr) represents partial
  operations with `Maybe`. [`PartialTransformation` and
  `PartialEffTransformation`](src/DGamma/Unified.idr) use Kleisli composition,
  so failure remains failure. The missing prose is the name of the partial-map
  category.

#### “Delete steps acting on A” accidentally includes external orchestration

*(Paper Lemma 72; NOTES erratum #4.)*

- **Literal prose.** Section 4.4.5 says to delete steps acting on closing fiber
  `A`. Definition 53 makes O-Retire/O-Remove actions of `A`, although the proof
  immediately says deleted steps write only the lifecycle field and Theorem 73
  must preserve external inputs.
- **Small trace.** Insert `A`; let it open; have the orchestrator retire `A`;
  let `A` unload. Literal deletion also erases O-Retire, leaving a survivor in
  which `A` was never retired. The final controls cannot agree.
- **Repair.** [`EpisodeGenerationDeletedActor`](src/DGamma/CP3.idr) deletes the
  selected lifecycle actions, while selected O-Retire/O-Remove survive. The
  checked implementation is
  [`deletionTheoremProof`](src/DGamma/CP4DeletionTheorem.idr), independently
  retraced in
  [`review-cp4-lemma72-round1.md`](review-cp4-lemma72-round1.md).

#### Confluence must compare endpoints modulo certified inert leftovers

*(Paper Theorem 73 and Lemma 57; NOTES clarification 8.)*

- **Literal tension.** Theorem 73(2) asks for equivalent final states after
  renaming. Lemma 57 treats an inert vestigial record as observationally equal
  to absence, and Lemma 72 guarantees controls only outside registered set `R`.
- **Small trace.** A closing activation registers `S` and retires it, but no
  O-Remove occurs. One schedule ends with a clean, empty, childless,
  unsupported `S`; a reduced schedule omits `S`. Effects agree and no component
  can observe `S`, but raw registry domains differ.
- **Repair.** [`VestigialEndpointGeneration`, `CurrentEndpointRenaming`, and
  `SystemEquivalentByRenamingModuloVestigial`](src/DGamma/CP3.idr) permit a
  mismatch only with a complete trace-derived Lemma-57 certificate. The
  no-O-Remove 23-step and 27-step schedules are executable in
  [`CP3VestigialChecks`](src/DGamma/CP3VestigialChecks.idr). This is the accepted
  Theorem-73 statement; its proof remains pending.

#### “Total on its provision” has to follow the real interleaved execution

*(Paper Definition 69; NOTES CP4 Finding #4.)*

- **What went wrong in our first encoding.** Definition 69 says an activation
  that finishes installed every declared provision. We initially checked only
  uninterrupted execution of the component program.
- **Concrete trace.** Provider `P` has two steps. P1 writes `world = false`; P2
  installs key `k` only when it sees `false`. Uninterrupted, `P` always installs
  `k`. Insert foreign fiber `T` between P1 and P2 and let it set
  `world = true`: `P` finishes Active with an empty table. Consumer `A` depends
  on `k`; the endpoint is quiet and failure-free, but support/Active equality
  fails.
- **Repair.** [`TraceComponentsTotal`](src/DGamma/CP3.idr) certifies the actual
  actor table at checked boundaries. The runnable trace, rejection of the old
  predicate, and positive repaired case are in
  [`CP4TotalityChecks`](src/DGamma/CP4TotalityChecks.idr). This repair makes the
  finite encoding match the paper's literal phrase “an activation ... that
  finishes.”

#### The progress bound assumes a reachable continuation, not an arbitrary one

*(Paper Theorem 66; NOTES CP4 Findings #5 and #6.)*

- **Implicit paper convention.** Section 4.4.4 bounds each declared program by
  `K` and reasons about states reached by the LTS using one global equality.
- **Counterexample to our old arbitrary-state alias.** Take `K = 0`, an empty
  declared program, and an arbitrary well-formed starting state whose lifecycle
  says `Reloading` with five no-op continuations. All five steps fire, but the
  old conclusion requires `5 ≤ (0 + 4)(0 + 1) = 4`. This is not a valid runtime
  history; it exposes the missing reachability invariant.
- **Repair.** [`progressTheorem`](src/DGamma/CP3.idr) requires
  `continuationsBoundedBy K first` and `AlignedTransitions`. Alignment is an
  Idris encoding obligation: each transition stores the `DecEq` dictionaries
  used by evaluation, so the trace must share the theorem's global equality.
  The proof is under [`CP4Progress*`](src/DGamma/CP4ProgressProof.idr); the
  five-step refutation and repaired positive case are in
  [`CP4ProgressChecks`](src/DGamma/CP4ProgressChecks.idr).

#### Runtime table order is observable; erased proofs are not automatically equal

*(Paper Definitions 48/60 and Equation 53; NOTES CP4 Findings
#7/#9/#10/#11/#12.)*

This was a chain of translation mistakes, not five independent paper errata.

- **Paper-level intent.** Definitions 48 and 60 use the evaluator's actual
  local state/maps, and Equation 53 compares runtime state. The paper does not
  introduce a reordered host table or identity of erased uniqueness proofs.
- **Concrete order bug.** Let a fiber store `[k2, k1]` while its declaration is
  `[k1, k2]`, and let a callback inspect which binding comes first. Our old
  restriction rebuilt declaration order. The LTS saw `[k2, k1]`; its alleged
  Definition-60 map saw `[k1, k2]` and could write a different world value.
- **Normalization/proof trap.** After preserving order, generated inverse
  composition normalized before every undo while the lifecycle accumulator
  normalized only once at unload. Runtime bindings agreed, but normalization
  rebuilt erased `UniqueKeys` proofs. Idris quantity `0` removes a proof at
  runtime; it does not prove all inhabitants of that proposition equal.
  Literal equality of proof-bearing records would smuggle in proof irrelevance
  or function extensionality.
- **Repair.** [`restrictOwnedPreservingOrder`](src/DGamma/Metatheory.idr) keeps
  stored order; `pushLocalUndo` matches generated normalization boundaries;
  [`EffectStateRelated`](src/DGamma/Metatheory.idr) retains exact ordered tables;
  `StepEffect.stepWitness` states recovery on the canonical evaluator domain;
  and `LocalStateRuntimeRelated`/`AccumulatorRelated` compare ambient values and
  ordered bindings rather than erased certificate identity. The relational
  deletion boundary likewise compares executable observations.
- **Executable checks.** [`CP4RestrictionChecks`](src/DGamma/CP4RestrictionChecks.idr)
  contains reverse-order/order-blindness regressions;
  [`CalculusChecks`](src/DGamma/CalculusChecks.idr) checks multi-undo rhythm;
  [`CP4AccumulatorControlChecks`](src/DGamma/CP4AccumulatorControlChecks.idr)
  constructs proof-distinct but runtime-equivalent accumulators; and
  [`CP4RuntimeBindingsChecks`](src/DGamma/CP4RuntimeBindingsChecks.idr) checks
  action transport across the boundary.

#### The Confluence premise already bundles the paper's fresh-name lemma

*(Paper Lemma 56 and Theorem 73; documented finite-host deviation.)*

- **Paper proof.** Theorem 73 starts from runs with the same orchestration and
  derives the fresh-registration tree match using Lemma 56.
- **Our accepted premise.** [`SameOrchestrationModuloGenerated`](src/DGamma/CP3.idr)
  already contains `RegistrationGenerationBijection`,
  `RegistrationCorrespondenceByGeneration`, and `CurrentEndpointRenaming`.
  The structural Lemma-56 match is supplied rather than derived from bare
  same-input traces.
- **Status.** Ten CP3 review rounds attacked this generation-aware premise,
  including cross-parent interleavings, reused names, and vestigial endpoints.
  It remains fixed for Confluence. Deriving the bundle from bare orchestration
  inputs is optional post-Theorem-73 strengthening debt on the scoping branch,
  not silently counted as proved paper strength.

#### A good adversarial process must also reject bad counterexamples

*(NOTES CP4 Finding #14; resolved, not an erratum.)*

- **The false alarm.** We tried to let foreign activation `A` commit dependency
  key `k`, then insert selected `S` as a new provider of `k` during `A`'s
  activation, apparently breaking deletion replay.
- **Why it cannot run.** `A`'s L-Begin already needs Active provider `P` for
  `k`. If `S` existed then, `S → A` is already a forbidden precedence edge. If
  `S` was absent, later O-Insert `S` fails provision disjointness while `P`
  remains. `P` cannot retire/remove while `A`'s committed view relies on it;
  raw-name reuse hits the same guard.
- **Checked resolution.** We retracted the weakening.
  [`committedProviderProvisionPersists`](src/DGamma/CP4DeletionCommittedProviderPersistence.idr)
  proves persistence throughout the installed activation, and
  [`crossingActivationExcludesSelectedProvider`](src/DGamma/CP4DeletionSelectedForeignLifecycleCrossing.idr)
  reconstructs the forbidden edge. The machine model corrected the research
  process rather than merely confirming it.

## What is proved

The table below is the short version. See
[`docs/THEOREM-INDEX.md`](docs/THEOREM-INDEX.md) for definitions, theorem names,
modules, and proof status item by item.

| Result | Status | Main checked inhabitant |
|---|---|---|
| Preservation, Theorem 59 | proved | [`preservationTheoremProof`](src/DGamma/Metatheory.idr) |
| Recovery exactness, Theorem 61 | proved | [`recoveryExactnessTheoremProof`](src/DGamma/CP4RecoveryReplay.idr) |
| Terminal recovery, Corollary 62 | proved | [`terminalRecoveryTheoremProof`](src/DGamma/CP4TerminalRecovery.idr) |
| Ordering, Theorem 63 | proved | [`orderingTheoremProof`](src/DGamma/Ordering.idr) |
| Resolution coherence, Theorem 64 | proved | [`resolutionCoherenceTheoremProof`](src/DGamma/CP4ResolutionCoherence.idr) |
| Progress, Theorem 66 | proved on the documented repaired finite-host statement | [`progressTheoremProof`](src/DGamma/CP4ProgressProof.idr) |
| Support, Lemmas 68 and 70 | proved on the documented provenance/totality specialization | [`CP4SupportSolution`](src/DGamma/CP4SupportSolution.idr), [`CP4Lemma70`](src/DGamma/CP4Lemma70.idr) |
| Deletion, Lemma 72 | proved on exact registration generations | [`deletionTheoremProof`](src/DGamma/CP4DeletionTheorem.idr) |
| Confluence, Theorem 73 | not proved; scoped only | [`cp5-thm73-scoping`](https://github.com/Termina1/dgamma/tree/cp5-thm73-scoping) |

Open Section 3 items are also explicit: Lemma 35's universal properties and
Theorems 40/42 are statement-only, and Definition 32 is a finite
approximation. No result becomes usable merely because its proposition type is
declared.

## How to check us

### Toolchain and build

DGamma is checked with **Idris 2 v0.8.0**.

```sh
git clone https://github.com/Termina1/dgamma.git
cd dgamma
idris2 --version
idris2 --build dgamma.ipkg
```

A successful warm build checks all modules listed in `dgamma.ipkg`. The last
Lemma-72 validation completed 207/207 package modules. Idris may print existing
name-shadowing warnings; warnings are not accepted as proof holes.

### Audit the absence of escape hatches

These commands should produce no output:

```sh
# No explicit trust escape or partial default.
grep -RInE \
  'believe_me|assert_total|^[[:space:]]*postulate([[:space:]]|$)|%default[[:space:]]+partial' \
  src --include='*.idr'

# Every source module opts into totality.
find src -name '*.idr' -type f -exec grep -L '^%default total' {} +

# No Idris metavariable holes in the release source.
grep -RInE '\?[A-Za-z_][A-Za-z0-9_]*' src --include='*.idr'
```

“No escape hatches” means every exported proof term was accepted by Idris's
kernel from total definitions. It does **not** mean every proposition declared
in a file is proved. A theorem can be stated as a `Type` without an inhabitant;
the theorem index calls those items “stated,” and they cannot be used as
proofs.

### Review trail

The project used adversarial checkpoint reviews rather than one final friendly
read-through. Reports are committed so claims can be compared with what the
reviewer actually accepted:

- CP1: [`round 1`](review-cp1-adversarial.md),
  [`round 2`](review-cp1-round2.md), [`round 3`](review-cp1-round3.md)
- CP2: [`round 1`](review-cp2-round1.md),
  [`round 2`](review-cp2-round2.md), [`round 3`](review-cp2-round3.md),
  [`round 4`](review-cp2-round4.md), [`round 5`](review-cp2-round5.md)
- CP3 statement review: [`round 1`](review-cp3-round1.md) through
  [`round 10`](review-cp3-round10.md) (the intermediate files are in the
  repository root)
- Lemma 72 implementation review:
  [`review-cp4-lemma72-round1.md`](review-cp4-lemma72-round1.md)

The process deliberately tried to construct executable countermodels, checked
that premises were non-vacuous, compared public statement drift, and rejected
Finding 14's invalid countermodel. Review reports are evidence about a specific
commit, not a substitute for rerunning the compiler.

### Honest open items

- **Theorem 73 is pending.** The scoping branch estimates 24–50 engineering
  shifts. It contains research-only interfaces with named holes; those files
  are not release proofs and must never be merged to `main` unchanged.
- **Cold-build debt remains.** A one-process build from an empty `build/` can be
  killed by memory use while elaborating the large
  [`CP4SupportSolution`](src/DGamma/CP4SupportSolution.idr). The registered
  remedy is to split it into smaller modules and repeat a clean archive build.
  Warm full builds and isolated targeted checks pass; this is reproducibility
  debt, not a known type error.
- **There is no single all-premise calculus demo.** The repository has small
  executable examples and many non-vacuity/countermodel traces, but not one
  compact end-to-end schedule inhabiting every repaired premise of every major
  theorem simultaneously.
- **Some Section 3 proof debt remains.** Lemma 35's universal properties and
  Theorems 40/42 are precise statement-only interfaces. Definition 32 remains a
  finite approximation for the reason explained above.
- **Paper Lemma 56 is bundled in the accepted Confluence premise.** Deriving
  that bundle from bare same-orchestration traces is optional strengthening
  debt after Theorem 73.

## Project layout

| Path | Purpose |
|---|---|
| [`src/DGamma/Effects.idr`](src/DGamma/Effects.idr) | Twisted composition, tracking, recovery, witnessed effects, independence, and out-of-LIFO undo. |
| [`src/DGamma/Coeffects.idr`](src/DGamma/Coeffects.idr) | Dependent coeffect tables, partial operations, notifications, isolation, and interception. |
| [`src/DGamma/Unified.idr`](src/DGamma/Unified.idr) | Finite context tower, observational equivalence, relational effects, and mediated operations. |
| [`src/DGamma/Calculus.idr`](src/DGamma/Calculus.idr) | Components, fibers, registries, lifecycle states, evaluator, actions, and checked transitions. |
| [`src/DGamma/Metatheory.idr`](src/DGamma/Metatheory.idr) | Indexed traces, episodes, preservation, Definition-60 generators, recovery interfaces, and structural lemmas. |
| [`src/DGamma/Ordering.idr`](src/DGamma/Ordering.idr) | Constructive Theorem-63 spatial ordering proof. |
| `src/DGamma/CP4Recovery*`, `CP4TerminalRecovery`, `CP4ResolutionCoherence` | Theorems 61/62/64 and their effect/control replay infrastructure. |
| `src/DGamma/CP4Progress*` | Repaired finite Progress/Theorem-66 proof and regressions. |
| `src/DGamma/CP4Support*`, `CP4Lemma70` | Registration ranks, support well-foundedness, support solution, and quiescent Active/support equality. |
| `src/DGamma/CP4Deletion*` | Lemma-72 generation scanning, deletion plans, eight-action relational replay, selected episode/post-close folds, withdrawal, and theorem assembly. |
| `src/DGamma/*Checks.idr` | Executable countermodels, non-vacuity witnesses, and semantic regressions. |
| [`docs/THEOREM-INDEX.md`](docs/THEOREM-INDEX.md) | Full paper-definition/theorem correspondence and exact proof status. |
| [`NOTES.md`](NOTES.md) | Detailed design decisions, proof history, errata, validation records, and residual debt. |
| `review-*.md` | Adversarial review reports tied to concrete checkpoints. |
| [`research/` on `cp5-thm73-scoping`](https://github.com/Termina1/dgamma/tree/cp5-thm73-scoping/research) | Non-release, hole-containing candidate interfaces for the future Confluence proof. No `research/` code is part of main. |

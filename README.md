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

This is the most important part of the repository. Mechanization did not simply
translate the prose: it found paper-level errata, ambiguities, and mistakes in
our own initially accepted encodings. The examples below use ordinary names:
`A` and `S` are fibers, `P` is a provider, and `k` is a coeffect key. No Idris
knowledge is needed to follow them.

### Erratum 1: Definition 32 is not an ordinary recursive datatype

- **Literal claim.** Section 3.3.1, Definition 32, Equation 31 defines
  `Γ∞ = μΓ. Γ × (Γ → Γ) × Σ` as a recursive context type.
- **Gap.** Imagine trying to build one finite constructor for `Γ∞`. One field
  must be a function that accepts another complete `Γ∞`. The recursive type
  therefore appears to the left of an arrow. Ordinary inductive datatypes allow
  recursive children, but not a constructor that consumes arbitrary values of
  its own type: that is a negative, non-strictly-positive occurrence. Idris
  rejects it because naïvely accepting it would break normalization.
- **Repair.** [`ContextTower` and
  `GammaInfinityApprox`](src/DGamma/Unified.idr) are explicit, executable finite
  approximations. We do **not** claim that they solve the unqualified domain
  equation. A literal solution needs a guarded or domain-theoretic semantics
  that the paper does not provide.

### Erratum 2: Lemma 35's stated tests cannot observe two yielded inverses

- **Literal claim.** Section 3.3.2, Lemma 35 says indistinguishability is the
  coarsest relation respected by the operations. The surrounding prose tests a
  fixed inverse at related values.
- **Counterexample story.** Suppose an operation run at indistinguishable
  origins `v` and `v'` returns the same visible value but dynamically chooses
  two different undo functions, `u` and `u'`. Every test that takes one fixed
  undo and runs that same undo at both values can pass. Yet applying `u` and
  `u'` to one common probe can produce different answers. The advertised test
  language never compares the two inverses that were actually yielded, so it
  cannot prove the coarsest-relation claim.
- **Repair.** [`FixedInverseStep` and
  `YieldedInverseStep`](src/DGamma/Unified.idr) distinguish these observations:
  the latter evaluates the two dynamically yielded inverses on a common probe.
  The redesigned universal-property statements remain marked `TODO(proof)`;
  this is an honest open Section 3 item, not an assumed theorem.

### Clarification 1: Definitions 24 and 39 need a partial-map category

- **Literal claim.** Section 3.2.1, Definition 24 allows coeffect operations and
  inverses with preconditions, while Section 3.1's generated monoids are
  presented using total endomorphisms.
- **Gap story.** A `setFresh(k, value)` operation succeeds only while `k` is
  absent. Run it once and it succeeds; run it again and it fails. Treating that
  failure as an ordinary total state map—or silently as identity—changes which
  programs execute and invalidates composition of inverses.
- **Repair.** [`Coeffects`](src/DGamma/Coeffects.idr) uses `Maybe` for partial
  operations. [`PartialTransformation` and
  `PartialEffTransformation`](src/DGamma/Unified.idr) compose with Kleisli
  composition, so failure remains failure. The clarification the paper needs
  is simply to name the partial transformation category.

### Clarification 2: Theorem 15's “if and only if” changes quantifier scope

- **Literal claim.** Section 3.1.3, Theorem 15 fixes an origin `γ`, obtains an
  inverse `g` there, and then gives an “iff” characterization involving all
  accumulators/probes.
- **Gap story.** An undo token produced at `γ` may know how to restore exactly
  the state reached from `γ`. That witness alone says nothing about feeding the
  same token a state produced from another origin. Moving from “works here” to
  “works for every `φ` and probe” silently requires a uniformity hypothesis on
  the whole forward map.
- **Repair.** [`effectLiftWitnessIff`](src/DGamma/Effects.idr) states the
  quantifiers explicitly: restoration for every accumulator and probe is
  equivalent to the yielded inverse being uniform against the forward map. The
  resulting theorem is proved pointwise, without function extensionality.

### Erratum 3: Lemma 68 assumes provenance that O-Insert does not enforce

- **Literal claim.** Section 4.4.5, Lemma 68 says support is well founded. Its
  proof argues that a child is registered by a particular activation and hence
  is born after that activation's L-Begin.
- **Counterexample story.** Table 1's O-Insert guard originally asks only that
  parent `A` is present, child name `S` is fresh, and provisions are disjoint.
  It does not say which iterator step of `A` requested `S`. A scheduler can
  therefore insert `S` while merely pointing at `A`; with only a phase/order
  discipline, children from alternating subtrees can be arranged so that the
  support edges form a cycle. Timely retirement does not recover the missing
  fact: the birth still was not tied to a yielded registration event.
- **Repair.** [`RegistrationProvenance`, `ParentRegistrationYield`, and
  `RegistrationDiscipline`](src/DGamma/CP3.idr) tie each child insertion to the
  actual nonempty iterator head, a deterministic protocol catalog tag, and
  strict component ranks; every child also has its own later retirement
  obligation. The support proof is in
  [`CP4SupportSolution`](src/DGamma/CP4SupportSolution.idr), with executable
  premise regressions in
  [`CP3StatementChecks`](src/DGamma/CP3StatementChecks.idr). The finite catalog
  is an explicit host representation: because O-Insert is separate and does
  not consume the source head, it can license more than one fresh child of the
  same ranked component. That over-approximation is documented rather than
  hidden.

### Erratum 4: Lemma 72 cannot delete every step “acting on n”

- **Literal claim.** Section 4.4.5, Lemma 72 says to delete the steps acting on
  the closing fiber `n`. Under Definition 53 that includes orchestration such
  as O-Retire, although the proof immediately says the deleted steps write only
  the lifecycle field and Theorem 73 must preserve external inputs.
- **Counterexample story.** Let the orchestrator insert `A`; `A` opens an
  episode; the orchestrator retires `A`; then `A` finishes unloading. If we
  literally delete every action owned by `A`, we also delete O-Retire. The
  survivor now says `A` was never retired, so its final control state cannot
  agree with the original outside the intended deletion.
- **Repair.** [`EpisodeGenerationDeletedActor`](src/DGamma/CP3.idr) deletes the
  selected fiber's lifecycle actions, not its orchestration. Selected
  O-Retire/O-Remove survive. The checked implementation is
  [`deletionTheoremProof`](src/DGamma/CP4DeletionTheorem.idr); the independent
  review retraced this distinction in
  [`review-cp4-lemma72-round1.md`](review-cp4-lemma72-round1.md).

### Lemma 56 must rename births, not raw names

- **Literal claim.** Section 4.3.5, Lemma 56 applies one bijection `χ : N → N`
  to names. The same section also permits O-Remove followed by reuse of the
  freed name.
- **Counterexample story.** In one run, `A` registers a child called `S`; in
  another run fresh choice calls that historical child `T`. Both children are
  later removed. The orchestrator then inserts a new root called `S` in both
  runs. The historical match needs `S ↦ T`, while the current external root
  must remain `S ↦ S`. No single raw-name bijection can do both.
- **Repair.** [`RegistrationGenerationBijection`](src/DGamma/CP3.idr) renames
  `(raw name, birth ordinal)` for historical registration trees.
  [`CurrentEndpointRenaming`](src/DGamma/CP3.idr) separately renames live
  endpoint names and fixes external roots. Checked role-change and cross-parent
  traces live in
  [`CP3StatementChecks`](src/DGamma/CP3StatementChecks.idr), and the final
  adversarial assessment is
  [`review-cp3-round10.md`](review-cp3-round10.md).

### Lemma 72's registered set also has to be generation-indexed

- **Literal claim.** Lemma 72 writes `R` as a set of names registered during the
  selected episode and deletes all later steps acting on a name in `R`.
- **Counterexample story.** `A` registers child `S`; `S` is retired and removed;
  later the orchestrator legally inserts an unrelated root, also called `S`.
  A raw-name filter remembers only that `S ∈ R`, so it deletes the later root
  birth as if it belonged to `A`. The resulting endpoint withdraws a component
  that should survive.
- **Repair.** [`GenerationActionSubsequence`](src/DGamma/CP3.idr) and the
  scanner modules under `CP4DeletionGeneration*` stamp every birth and action.
  The ten-step executable counterexample in
  [`CP4DeletionGenerationChecks`](src/DGamma/CP4DeletionGenerationChecks.idr)
  proves the old filter deletes the reissued root and the repaired filter keeps
  it. Premises, filtering, outside-control equality, and withdrawal all use the
  same generation stamp.

### Theorem 73 needs equivalence modulo certified vestigials

- **Literal claim.** Section 4.4.5, Theorem 73(2) says two canonical runs are
  equivalent after Lemma-56 renaming. Lemma 57, however, treats an inert
  vestigial entry as observationally equal to absence, and Lemma 72 guarantees
  control equality only outside `R`.
- **Counterexample story.** A closing activation registers `S` and retires it,
  but no O-Remove occurs. One legal schedule finishes with a clean, empty,
  childless, unsupported `S` record; another canonical reduction omits `S`.
  Effects agree, and no component can observe `S`, but literal registry-domain
  equality is false.
- **Repair.** [`VestigialEndpointGeneration`,
  `CurrentEndpointRenaming`, and
  `SystemEquivalentByRenamingModuloVestigial`](src/DGamma/CP3.idr) permit a
  mismatch only when the present side has the complete trace-derived Lemma-57
  certificate. The no-O-Remove 23-step and 27-step executable schedules are in
  [`CP3VestigialChecks`](src/DGamma/CP3VestigialChecks.idr). This is the accepted
  statement for Theorem 73, whose proof is still pending.

### Definition 69 must quantify actual interleaved activations

- **Literal claim.** Section 4.4.5, Definition 69 says any activation that
  finishes has installed every declared provision. Our first encoding checked
  only uninterrupted execution of the component program.
- **Counterexample story.** Provider `P` has two steps. Step P1 writes
  `world = false`; P2 installs key `k` only when it sees `false`. Uninterrupted,
  `P` always installs `k`. Insert foreign fiber `T` between P1 and P2 and let it
  set `world = true`: `P` now finishes Active with an empty table. Consumer `A`
  declares dependency `k`, so the endpoint is quiet and failure-free yet the
  advertised support/Active equality fails.
- **Repair.** [`TraceComponentsTotal`](src/DGamma/CP3.idr) certifies the actual
  actor table at checked trace boundaries. The complete runnable trace,
  rejection of the old predicate, and positive repaired version are in
  [`CP4TotalityChecks`](src/DGamma/CP4TotalityChecks.idr). This was a flaw in our
  first specialization; the repaired statement matches the paper's literal
  “an activation ... that finishes.”

### Theorem 66 needs reachable continuation bounds and aligned equality

- **Literal claim.** Section 4.4.4, Theorem 66 assumes each declared program has
  length at most `K` and derives the numerical lifecycle bound. Its prose works
  with states reached by the LTS and one global notion of equality.
- **Counterexample story.** Take `K = 0` and a component whose declared program
  is empty, but start the theorem from an arbitrary well-formed state whose
  lifecycle says `Reloading` with five no-op continuation steps. All five steps
  fire. The old conclusion requires `5 ≤ (0 + 4)(0 + 1) = 4`. This is not a
  paper runtime history; it exposes that our finite arbitrary-state theorem
  forgot the paper's reachability invariant.
- **Repair.** [`progressTheorem`](src/DGamma/CP3.idr) adds
  `continuationsBoundedBy K first` and `AlignedTransitions`. The latter is an
  Idris encoding obligation: each transition stores the `DecEq` dictionaries
  used by evaluation, so the trace must use the same global equality as the
  theorem. Preservation of the continuation bound and the full proof are under
  [`CP4Progress*`](src/DGamma/CP4ProgressProof.idr). The five-step executable
  refutation and repaired positive case are in
  [`CP4ProgressChecks`](src/DGamma/CP4ProgressChecks.idr).

### Ordered tables and erased proofs: the observable-truth chain

This chain comprises CP4 Findings 7, 9, 10, 11, and 12. It is mainly a warning
about translating the paper into a proof assistant, not five independent paper
errata.

- **Literal claim.** Definitions 48 and 60 use the evaluator's actual local
  state and maps; Equation 53 compares runtime state. The paper has no separate
  notion of a reordered host table or identity of erased uniqueness proofs.
- **Concrete story.** Let a fiber's stored table be `[k2, k1]`, while its
  declaration lists `[k1, k2]`. A legal callback checks which binding comes
  first. Our old restriction rebuilt the table in declaration order, so the LTS
  callback saw `[k2, k1]` while its alleged Definition-60 map saw `[k1, k2]` and
  could write a different world value. Fixing the order exposed a second issue:
  the generated inverse chain normalized before every undo, while the lifecycle
  accumulator normalized only once at unload. The runtime values were equal,
  but each normalization rebuilt erased `UniqueKeys` proofs.
- **Why erasure is not proof irrelevance.** Quantity `0` means the proof is not
  present at runtime. It does not give Idris a theorem that any two proofs are
  equal. Two `OwnedTable` records with identical runtime bindings and different
  derivations are observationally the same but not automatically equal terms.
  Demanding literal record equality would smuggle in proof irrelevance or
  function extensionality.
- **Repair.** [`restrictOwnedPreservingOrder`](src/DGamma/Metatheory.idr) keeps
  stored order. `pushLocalUndo` normalizes at the same boundaries as generated
  inverse composition. [`EffectStateRelated`](src/DGamma/Metatheory.idr) retains
  exact ordered tables rather than lookup-only equality. `StepEffect.stepWitness`
  states exact recovery on the canonical evaluator domain, and
  `LocalStateRuntimeRelated`/`AccumulatorRelated` compare ambient values and
  ordered bindings instead of erased certificate identity. The relational
  deletion boundary likewise compares executable observations, not proof terms.
- **Executable checks.** [`CP4RestrictionChecks`](src/DGamma/CP4RestrictionChecks.idr)
  contains the reverse-order and order-blindness regressions;
  [`CalculusChecks`](src/DGamma/CalculusChecks.idr) checks the multi-undo
  normalization rhythm; [`CP4AccumulatorControlChecks`](src/DGamma/CP4AccumulatorControlChecks.idr)
  constructs two proof-distinct but runtime-equivalent accumulators; and
  [`CP4RuntimeBindingsChecks`](src/DGamma/CP4RuntimeBindingsChecks.idr) checks
  action transport across that boundary.

### Definition 60 forgot observable failure agreement

- **Literal claim.** Section 4.4.2, Definition 60, Equations 54–55 say to read
  `Right` around the yielded triple and compare only projections 2 and 3. They
  do not require two failing evaluations to raise the same error.
- **Counterexample story.** One iterator raises `ColdError` when the ambient
  world is cold and `HotError` when it is hot. Under the old premise both runs
  project to “undefined,” so they appear stable. But L-Raise stores the error
  in `Unloading`; two schedules therefore finish with visibly different control
  outcomes. Lemmas 71/72 and Theorem 73 cannot transpose that step.
- **Repair.** [`IteratorStageOutcome` and
  `IteratorOutcomeAgreement`](src/DGamma/Metatheory.idr) distinguish unavailable,
  raised, and yielded outcomes and require exact agreement of errors. The
  old premise is inhabited and then constructively refuted at the endpoints in
  [`CP4FailureOutcomeChecks`](src/DGamma/CP4FailureOutcomeChecks.idr); the same
  file includes a genuinely failing trace accepted by the repaired premise.

### Finding 14: a plausible counterexample that was itself wrong

Adversarial review should reject bad proofs, but it should also reject bad
counterexamples.

- **Initial concern.** A foreign activation `A` opens before selected fiber `S`
  and closes during `S`'s episode. We tried to make `A` commit key `k`, then
  insert `S` as a new provider of `k`, apparently invalidating the deletion
  replay.
- **Why the story cannot execute.** `A`'s L-Begin already requires an Active
  provider `P` for `k`. If `S` existed then, `S → A` is already a forbidden
  precedence edge. If `S` did not exist, O-Insert `S` later fails the
  provision-disjointness guard while `P` remains. `P` cannot retire/remove
  while `A`'s committed view relies on it. Reusing a raw name does not evade the
  same insertion guard.
- **Checked resolution.** We retracted the proposed weakening.
  [`committedProviderProvisionPersists`](src/DGamma/CP4DeletionCommittedProviderPersistence.idr)
  proves that the committed provider remains the relevant provider throughout
  the installed activation, and
  [`crossingActivationExcludesSelectedProvider`](src/DGamma/CP4DeletionSelectedForeignLifecycleCrossing.idr)
  reconstructs the forbidden edge. This is a useful example of the machine
  model correcting the research process rather than merely confirming it.

### The accepted Theorem 73 premise bundles paper Lemma 56

- **Paper proof.** Theorem 73 starts from two runs with the same orchestration
  inputs and derives the fresh-registration tree match by invoking Lemma 56.
- **Finite-host deviation.** Our accepted
  [`SameOrchestrationModuloGenerated`](src/DGamma/CP3.idr) premise already
  contains `RegistrationGenerationBijection`,
  `RegistrationCorrespondenceByGeneration`, and `CurrentEndpointRenaming`.
  In other words, the structural Lemma-56 match is supplied rather than derived
  from bare same-input traces.
- **Status.** Ten CP3 adversarial rounds tested this generation-aware premise,
  including cross-parent interleavings, reused raw names, and vestigial
  endpoints. We will keep it fixed for the Confluence proof. Deriving the bundle
  from bare orchestration inputs is registered as optional post-Theorem-73
  strengthening debt on the scoping branch, not silently counted as proved
  paper strength.

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

# Mechanization notes

## Design decisions

### Runtime data and erased specifications

- Forward maps, inverses, accumulators, coeffect values and tables are runtime
  data.
- Algebraic laws and recovery witnesses are quantity `0` fields/arguments.
- `Undo after before`, `Applied before`, `CoeffectApplied before`,
  `Loaded current initial`, `EffectStack current initial`, and
  `RelEffectStack current initial` expose the
  state indices needed for a later linear API without prematurely forcing every
  runtime handle to quantity `1`.
- Idris does not assume function extensionality. Every equality of functions in
  the paper is therefore represented by `Pointwise` equality. This avoids an
  axiom and is the computationally relevant form of the statement.
- **Erasure is not proof irrelevance.** Although `CoeffectContext.uniqueBindings`
  is quantity `0`, two contexts built from the same runtime bindings with
  differently derived `UniqueKeys` witnesses are not automatically equal in
  Idris. Metatheory must therefore frame and compare executable observations
  (`lookupFiber`, invariant folds, resolved values), never obtain a state or
  context equality solely by assuming erased uniqueness proofs coincide.

### Partial coeffect operations

The paper writes partial arrows and says a violated precondition raises an error
and produces no transition. `get`, `setFresh`, `liftOperation`, all yielded
inverses, isolation/interception inverses, and `runMediated` therefore use
`Maybe`; no partial Idris function is used. A successful `setFresh` returns an
indexed `CoeffectApplied before`, and
`deleteInserted` proves that its inverse recovers the same runtime dependent
map. The erased uniqueness witness is representation proof and deliberately not
part of that equality. `LiftedUndo` keeps a full dependency-table certificate
on the executable runtime path. `IsoSetResult` and `InterSetResult` keep indexed
partial table tokens, while `isoUndoValid`/`interUndoValid` certify only their
respective dependency/provider-table projections; the smart constructors
preserve realm/default and ambient fields operationally, but the token types do
not claim full-context equality. The inverse deletes by key,
so unrelated later registrations are retained; isolated undo additionally
fails if the logical key has changed realm. `failurePropagates` checks that a failed
mediated stage remains `Nothing`, rather than becoming identity.

### The recursive context

Paper Definition 32 is the negative recursive equation
`Gamma = Gamma × (Gamma -> Gamma) × Sigma`. A literal inductive declaration is
not strictly positive and Idris correctly rejects it. `ContextTower n` and
`GammaInfinityApprox` are explicitly named finite approximations. No claim that
they preserve every finite observation is made, because the paper supplies no
observation semantics for this fixed point. They are executable and total, but
are not Definition 32 itself and do not prove that the unqualified domain
equation has a set-theoretic least fixed point.

### Observational equivalence

A coeffect table relation compares every dependent lookup using the equivalence
for that key. Its reflexive, symmetric and transitive laws are proved via the
indexed `MaybeRelated` family. `RelEffStar` carries both halves of Definition 37:
the effect result is stable on related inputs, and every yielded inverse both
respects the relation and recovers its application state up to that relation.
`relDiamond` and `relPushStack` prove the relational composition/soundness core
of Lemma 38.

## Paper ambiguities / possible errata

1. **Definition 32 is non-strictly-positive.** The recursive variable occurs to
   the left of an arrow. Calling `mu Gamma. Gamma × (Gamma -> Gamma) × Sigma` a
   routine recursive type requires a domain-theoretic solution or a guarded
   encoding not supplied by the paper.
2. **Lemma 35 needs a stronger observer language than the prose states.** A
   fixed inverse generator alone cannot prove that two *different* inverses
   yielded at indistinguishable origins are pointwise related; the round-2
   reviewer supplied a checked countermodel. Tests now contain both
   `FixedInverseStep` (one concrete inverse applied to two related current
   states) and `YieldedInverseStep` (inverses dynamically yielded at the two
   compared origins, applied to one common probe). The result statement keeps
   map-relatedness and each map's respect as separate obligations, matching
   Definition 36. This is a semantic repair/clarification of the paper, not
   merely a missing induction.
3. **Definition 24 and Theorem 40 mix partial and monoidal maps.** Operations
   and their inverses are partial, while Section 3.1 originally presents total
   endomorphisms. The revised mechanization uses Kleisli composition for
   `Maybe` in `PartialTransformation`/`PartialEffTransformation`; failures are
   never totalized. This is a faithful explicit interpretation, but the paper
   should have named the partial transformation category.
4. **Theorem 15's “iff” has a quantifier-scope subtlety.** At a fixed origin,
   the yielded inverse is only initially witnessed there. `effectLiftWitnessIff`
   now states and proves that accumulator restoration for all `phi` and probes
   is equivalent to that yielded inverse being uniform against the whole
   forward map. This resolves the mechanization issue but the paper could state
   the scope more explicitly.

## Escape-hatch and hole audit

There are no uses of `believe_me`, `assert_total`, `postulate`, unsafe FFI, or
`%default partial`. Every Idris module has `%default total`.

The following are statement-only `Type`s. They export no value and therefore
cannot silently introduce a proof:

- `OperationsRespectIndistinguishability` and
  `CoarsestRespectedEquivalence` — Lemma 35.
- `distinctKeysIndependent` — Theorem 40.
- `MediatedIndependenceTheorem` — Theorem 42.
- `preservationTheorem` — raw-rule Theorem 59.
- `recoveryExactnessTheorem` — Theorem 61.
- `terminalRecoveryTheorem` — Corollary 62.
- `orderingTheorem` — the finite closed-trace form of Theorem 63.
- `resolutionStructureTheorem` and `resolutionCoherenceTheorem` — the global
  structural/full forms of Theorem 64.

Each is marked `TODO(proof)` at its declaration. These are honest uninhabited
statements, not holes accepted by the compiler.

## Checkpoint 1 — Section 3 (approved)

### Scope completed

- Read the full extracted paper (`paper/cordis-paper.txt`, 3882 lines).
- Installed Idris 2 0.8.0 through Homebrew and created `dgamma.ipkg`.
- Mechanized the runtime content of every numbered Section 3 definition except
  the literal Definition 32 fixed point, for which the explicitly partial
  `GammaInfinityApprox` is provided and catalogued as a deviation.
- Proved the monoid/tracking/recovery results, witnessed effect composition,
  every field of effect preservation, projection, lifted state recovery,
  the exact Theorem 15 formula/iff, every intermediate LIFO boundary from
  Theorem 16, both clauses of Lemma 18, both equations at every intermediate of
  Theorem 20, arbitrary-permutation recovery (Corollary 21),
  intrinsically unique finite dependent-table set recovery, notification facts,
  table-equivalence laws, and the relational effect-composition/accumulator
  soundness core of Lemma 38.
- Stated the three remaining operation-observational theorems precisely as
  types rather than using axioms. See the audit above.

### Adversarial review

The orchestrating supervisor independently reviewed the repository and then
required a second hardening pass. This worker has no `subagent` tool exposed in
its tool namespace and is also governed by a child-agent instruction forbidding
further delegation, so the requested fresh reviewer process could not be
launched. Adversarial self-review plus the supervisor's independent review found
and fixed:

1. Initially fieldwise Theorem 13 covered only the current-state projection;
   accumulator and lifted-inverse fields were added.
2. The initial Corollary 21 encoding merely represented an undo list and was
   vacuous as a theorem. It was replaced by `Permutation` plus the exact
   `anyPermutationRecovery` proposition over inverses collected at application
   states.
3. The initial Lemma 18(2) statement did not express submonoid inclusion. It was
   replaced by `JointTransformation` and a dependent pair giving a pointwise
   embedding target.
4. Operation independence initially mentioned outcomes only. It was replaced
   with partial generated transformation monoids, commutation up to the suite
   equivalence, and inverse/outcome stability only under foreign generated
   transformations.
5. The supervisor rejected statement-only general independence. Lemma 18(2)
   is now proved by an explicit `JointTransformation` embedding. Theorem 20 is
   proved by `withdrawAcross` induction, including stability of every later
   yielded inverse. Corollary 21 is proved by deriving pairwise commutation of
   the concrete yielded inverses, showing adjacent swaps preserve evaluation,
   and relating every permutation to the independently proved LIFO recovery.
6. A fresh-context adversarial reviewer (run by the supervisor; full report in
   `review-cp1-adversarial.md`) found the following additional issues, all of
   which were addressed:
   - Theorem 20 exposed only the final withdrawal equality. The new
     `theorem20EveryIntermediateProof` quantifies by every prefix split and
     returns both forward factorization and withdrawal; the inverse-stability
     list remains separately proved.
   - Definitions 22/25 admitted duplicate list keys. `CoeffectContext` and
     `CoeffectSpec` now carry erased `UniqueKeys` witnesses.
   - Definition 24 lacked equivalence/partial-inverse laws and a lift witness.
     These are now in `OperationResultsRelated`, `CoeffectOperation`,
     `CoeffectInterface`, and `liftedInverseWitness`.
   - Definitions 27–31 omitted operational recovery, isolated/intercepted set,
     the realm injection, and `InterSpec`; all were added.
   - Lemma 35 and Theorems 40/42 had false weakened statement shapes. Lemma 35
     now includes aligned definedness, outcomes, successors and inverse respect;
     Theorem 40 is restricted by construction to dependent-table lifts; Theorem
     42 now carries the required shared-key commutativity hypothesis and
     operation-occurrence evidence.
   - Executable `runMediated` no longer totalizes failure to identity. It returns
     a partial effect and propagates `Nothing`; an executable regression theorem
     checks this.
   - README's Theorem 10(2) overclaim was fixed by actually proving the
     unconditional `embedTwisted` homomorphism.
   - Theorem 15's exact formula/iff and Theorem 16's intermediate clauses were
     added. Lemma 38 and Definition 32 are now explicitly marked partial rather
     than overclaimed.
7. The independent round-2 review (`review-cp1-round2.md`) found a checked
   countermodel to the first Lemma 35 redesign plus runtime-token/lifecycle
   gaps. The fixes were architectural rather than cosmetic:
   - Definition 34 gained two inverse observations: fixed-origin inverses test
     individual relation respect, while dynamically yielded inverses test
     pointwise relatedness. Lemma 35 now asks for these separately, eliminating
     the supplied countermodel's hidden probe.
   - `LiftedOperationResult` now contains an indexed `LiftedUndo` with its
     application-state recovery certificate, and `keyedApply` returns that
     result intact. `keyedPartialEff` is the explicitly proof-erased mathematical
     projection used only to state generated-monoid independence; runtime callers
     and `runMediated` consume the witness-carrying result first.
   - Realm overrides now reuse intrinsically unique `CoeffectContext`, and base,
     isolated, and intercepted sets all return indexed witnessed *partial*
     tokens. `isoUndoValid`/`interUndoValid` prove their application-state
     recovery; isolated undo fails after a realm change instead of deleting the
     wrong binding.
   - `reverseActual` runs the actual `effect`-returned lifted inverses and carries
     their live accumulator. `actualLifoEveryIntermediateProof` proves current
     state and `recover` invariant at each prefix/suffix boundary. The older
     reconstructed base-map theorem remains useful but is no longer cited as
     the lifted-accumulator result.
   - `Section3Example` now includes two components, provisions/requirements,
     independent effects, load/load/unload/unload, coeffect activation and
     withdrawal, and direct applications of base and lifted recovery theorems.
   - `keyCommutative` now quantifies every operation pair in the whole key
     interface (including self-pairs); Theorem 42 assumes it for every key used
     by both programs, literally matching the paper.
8. The supervisor's independent round-3 review
   (`review-cp1-round3.md`) reconstructed the hidden-probe model and verified it
   is now distinguished, checked a nontrivial distinct-value model to ensure the
   stronger observer is non-vacuous, and checked concrete equality of captured
   lifted undo execution with `reverseActual`. It reported no BLOCKER/MAJOR and
   accepted CP1. Its sole MINOR was that isolation/interception validity types
   expose table-projection recovery rather than full-context equality. README
   and this note now state that narrower claim; no stronger theorem is implied.
9. All source files were scanned for hidden escape hatches and missing
   `%default total`; none were found.

### Validation

`idris2 --build dgamma.ipkg` succeeds with Idris 2 0.8.0 without warnings.

### Deviations / residual work

Checkpoint 1 is buildable. Lemma 35, Theorem 40 and Theorem 42 remain correctly
stated and explicitly unproved; no proof is claimed for them. Definition 32 is
an explicit finite approximation, and Lemma 38 has a proved relational core but
not a transport theorem covering every Section 3.1 declaration.

## Checkpoint 2 — Section 4 calculus through Theorem 64 (round-1 redesign)

The independent round-1 report (`review-cp2-round1.md`) rejected the first
candidate for vacuous/false theorem types and one confirmed rule bug. Every
BLOCKER/MAJOR was addressed architecturally rather than hidden by a postulate.

### Dynamic confined runtime

- A fiber now owns a dynamic `OwnedTable`; its erased `ownedSound` certificate
  confines every runtime key to the component's declared provisions. Components
  no longer carry immutable final values.
- `StepEffect` receives `DepValues` for exactly its declared dependency list and
  a `LocalState` containing only ambient world plus its own table. It can
  therefore consume the committed resolution and install computed provision
  values, but cannot inspect control fields or mutate another fiber. Its yielded
  inverse restores the exact local application state.
- `resolveCommittedValues` reads through the committed provider identities even
  while a provider is Unloading, whereas `providerOf`/`activeCoeffects` expose
  providers only in Active. This is the visibility interval used by Theorem 63.
- The iterator remains a finite list. Nested registration inside a step remains
  absent; `Registration` is still the explicit O-Insert/O-Retire host pair.
  Those two restrictions remain documented rather than overclaimed.

### LTS and invariant hardening

- The empty-list terminal branch now checks target equality. A stale empty
  iterator emits L-Divert, never L-Finish.
- `registryWellFormed` strengthens Definition 58's view clauses: each committed
  `(key, provider)` must name an installed fiber whose dynamic table still
  contains that key. This removes the round-1 provider-visibility countermodel.
- `applyAction` remains the raw ten-rule evaluator. `checkedApplyAction` is the
  executable proof-trace gate: it admits the same endpoint only when the target
  satisfies `registryWellFormed`. `Transition` is indexed by that checked
  equation and `fire` packages executable results. `preservationTheorem` is
  proved by eliminating the checked equation via `checkedActionTargetValid`.
  This is a deliberate proof-LTS safety monitor; proving that the monitor never
  rejects a raw rule from a valid source remains a stronger future lemma.
- `EpisodePrefix` must contain a checked L-Begin boundary immediately before its
  installed trace. `ClosedEpisode` additionally contains its checked L-Unload
  boundary. Arbitrary Active/Unloading suffixes no longer inhabit the episode
  types used by Theorems 61/62/64.

### Non-vacuous temporal statements

- The rejected `AllComponentsIndependent` was deleted. `TraceIndependent`
  quantifies only transformations that actually occur in the supplied trace at
  distinct actor names, with partial commutation and definedness stability.
  `emptyTraceIndependent` constructs it for every world, including Bool, so it
  cannot imply that the world is subsingleton.
- `partialWorldMap` returns `Nothing` when an off-origin successful iteration
  would fail. `ForeignReplay` requires a `Just` equation at every foreign step;
  failure is never totalized to identity.
- Theorem 61 is now anchored at L-Begin and takes a trace-specific
  `PrefixRecoveryIndependent`. Corollary 62 takes a maximal `ClosedEpisode`.
  Both remain statement-only pending the temporal induction.

### Spatial/resolution statements and proved structural lemmas

- `beginSatisfactionTheorem` proves Equation 58 directly from the checked
  L-Begin equation.
- `unloadGuardTheorem` proves that every checked L-Unload has `relied = False`.
- `advanceStructureTheorem` proves for every successful raw LAdvance that its
  tag is exactly Iter/Finish/Divert/Raise and that Iter/Finish expose target
  equality with the committed view (Equation 59). It catches the empty-program
  branch as well as nonempty iterations.
- `orderingTheorem` no longer accepts an arbitrary provider episode. From an
  initially empty finite checked trace, a closed consumer episode, resolution
  at its opening, and provider inactivity at the final state, it selects the
  containing closed provider episode. Its result requires strict prefix
  equations in the same global trace, consumer committed-provider constancy,
  and dynamic provider-value constancy. The global induction remains
  statement-only.
- The global `resolutionStructureTheorem` is anchored by `EpisodePrefix`, so the
  round-1 Unloading-suffix counterexample is unrepresentable. The local
  Equation-59/exit fact is proved; the global split and the recovery-combined
  `resolutionCoherenceTheorem` remain statement-only.

### Executable adversarial coverage

`DGamma.CalculusChecks` now uses the checked evaluator and covers all ten rule
tags, both L-Divert alternatives, L-Raise, O-Remove, a stale zero-step consumer,
and an attempted provider L-Unload while relied is true. A dynamic provider
installs ServiceA; the consumer reads it through `DepValues`, changes ambient
state, and installs ServiceB in its own table. Native evaluation reports `True`
for each individual scenario and `allRuleChecks`.

Lemmas 54–57 remain not separately packaged. Their most important boundary and
rule-shape fragments are now represented by checked transitions,
`BeginStep`/`UnloadStep`, `InstalledTrace`, Equation 58, the unload guard, and
`AdvanceStructure`.

### Round-2 countermodels and remediation

The independent round-2 report (`review-cp2-round2.md`) confirmed all five
round-1 blocker repairs, dynamic capability use, complete tag coverage, and a
real seven-step checked trace. It then supplied three new executable attacks.

- The arbitrary accumulator in Theorem 61 was deleted. `actualAccumulatorAt`
  extracts a dependent `AccumulatorHandle` from the selected fiber at the exact
  episode endpoint; `runAccumulator` determines the result. The theorem can no
  longer choose an unrelated function or restored world. Its conclusion also
  contains `SelectedTableRecovered`, pointwise exact recovery of the fiber's
  dynamic owned table.
- Definition 58's provider invariant now admits committed providers only in
  Active or Unloading, never Reloading. This makes table mutation structurally
  disjoint from existing committed consumers while preserving withdrawal-time
  capability reads.
- `OrderingResult.consumerResolution` and `providerValueStable` now range over
  `closedInside`, ending at the last installed state before L-Unload. They no
  longer demand a committed view at the post-close Inactive endpoint.
- `partialWorldMapFor` dispatches on `RuleTag`; L-Raise is exactly identity as in
  Table 1. Only successful Iter/Finish/landing-Divert maps rerun an iterator and
  may be undefined off-origin. `raiseMapIsIdentity` is an executable regression.
- `TerminalTableRecovery` adds the table half of paper's control-forgetting
  relation: the selected table equals its opening table pointwise and every
  foreign table equals its last-installed value across L-Unload. Theorem 64 now
  carries this result too. Pointwise dependent lookup equality is used because
  values have no global `DecEq` and erased uniqueness certificates are not
  runtime state.
- `AdvanceStructure` now includes its endpoint and proves Reloading for Iter,
  Active for Finish, and Unloading for landing Divert/Raise.
  `AbortDivertStructure` separately proves the exact pre/target-changed/post
  shape of the aborting L-Divert action.
- `reliedProviderCannotUnload` is a proved local provider-ordering conclusion:
  an L-Unload cannot coexist with the relied certificate created by an
  installed consumer's committed view.

The report correctly rejected the old `preservationTheorem` name: its proof was
only the target check embedded in `checkedApplyAction`. That lemma is now named
`checkedTransitionTargetValid`. Paper Theorem 59 is stated separately as the raw
implication from a valid source plus an `applyAction` equation to a valid target.
It remains unproved. Likewise the proof locating the unique exit after the
maximal Reloading prefix, and global provider-episode selection, remain open.
No checked-monitor lemma is claimed as those results.

### Round-3 full-effect recovery redesign

The round-3 review (`review-cp2-round3.md`) found that the round-2 conclusions
compared owned tables while `TraceIndependent`, accumulator commutation, and
`ForeignReplay` still projected every map to ambient `world`. Its reachable
actual-handle counterexample was valid: an inverse can be world-identity yet
choose the wrong table off-origin.

The recovery layer now has one state space throughout:

- `EffectState` contains ambient state and a table for every name;
  `projectEffectState` erases only control. Absent and empty tables coincide,
  matching vestigial-entry equivalence.
- `EffectStateRelated` compares ambient state exactly and every heterogeneous
  lookup pointwise, avoiding function extensionality and value `DecEq`.
- `partialEffectMap` executes Table-1 effect maps on that full state.
  `restrictOwned` reconstructs the acting fiber's provision-confined input
  table, `resolveEffectValues` reads provider tables from the moved state, and
  successful steps update both ambient and own table. L-Unload applies the
  captured accumulator to both fields. L-Raise remains full-state identity.
- `TraceIndependent`, `PrefixRecoveryIndependent`, definedness stability, and
  `ForeignReplay` accept only `PartialEffectMap`; their APIs contain no
  world-projection map. `accumulatorEffectMap` uses the same type.
- Theorem 61 and Corollary 62 conclude one full-effect replay relation. The
  disconnected `SelectedTableRecovered`/`TerminalTableRecovery` appendages were
  removed. Premises therefore structurally observe exactly what conclusions
  claim.

Reusable dependent-map frame lemmas `lookupReplaceOther`,
`lookupDeleteOther`, and `lookupInsertOther` were added to `DGamma.Coeffects`.
Definition 58 now uses explicit `parentsInvariant`, `chainsInvariant`, and
`viewsInvariant` recursors rather than opaque library folds, and
`parentChainFuelMonotone`/`chainsFuelMonotone` prove that insertion's extra fuel
preserves every existing acyclicity check. These are shared infrastructure for
raw Preservation, lifecycle frames, and later trace deletion/permutation proofs.

The supervisor's final CP2 bar additionally requires inhabited raw Preservation
and the whole-episode first-exit split. Those proofs are not yet complete in
this commit; global provider selection is explicitly deferred to CP3 with the
reviewer's required machinery: indexed trace splitting/search, boundary
extraction under name reuse, restricted Lemma-54 lifecycle/view frames, and a
forward relied-guard argument.

## Status

**Fully proved:** all previously approved Section 3 results; same-action raw
evaluator determinism; checked-to-raw projection and checked target admission;
Equation 58; L-Unload's local relied guard and relied-provider exclusion;
per-LAdvance Equation 59 with exact Iter/Finish/Divert/Raise endpoint phase; and
the aborting L-Divert structural shape. All executable rule checks, including
L-Raise identity and dynamic resolution consumption, pass.

**Partial/deviation:** Definition 32 finite approximations; Lemma 38 transport;
finite iterators; host-level rather than nested registration; trace-specific
rather than generated-monoid independence; exact full-effect equality; and the
checked proof-LTS. Full observational transport remains future work. Lemmas
54–57 are not individually complete.

**Merely stated:** Lemma 35, Theorems 40/42, raw Theorem 59, actual-handle/table
Theorem 61 and Corollary 62, corrected global `orderingTheorem`, global
`resolutionStructureTheorem`, and recovery-combined Theorem 64. These are the
only `TODO(proof)` declarations and remain escape-hatch-free types.

**Next:** finish and independently audit raw Theorem 59 and the whole-episode
first-exit split. Round 4 must rerun the table-sensitive actual-handle attack on
full-effect commutation/replay. Global provider selection remains deliberate
CP3 proof debt rather than part of the final CP2 approval bar.

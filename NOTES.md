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

## R174 freshness reclassification (owner ruling, 2026-09-06)

All historical raw-name reuse discussions below are scoped to the local-rule
calculus, not to the implementation's UID discipline. Def 47 O-Insert checks
LOCAL absence; Lemma 71's sorting argument uses GLOBAL freshness, and §5.1
states "a uid is drawn fresh and never reused". Global freshness is a **missing
hypothesis of Theorem 73**, satisfied by the implementation by construction.
R137/R172 and Finding-8 reuse countermodels are necessity evidence, **not paper
or implementation bugs**. DGamma implements `UniqueRawNameInsertions` in R173,
including rejection of the reuse fixture and actual reduction transport.
The CP3 raw premise is a **missing hypothesis at the frozen surface;
satisfiability under uniqueness remains to be re-verified**. This does not
validate or authorize calling the frozen deletion theorem or a scoped-to-raw
cast. Unrelated provenance, yield, and applicability findings are not dismissed
by this name-freshness reclassification.

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
5. **Confirmed Erratum #3 — Lemma 68 assumes yielded nested-registration
   provenance that O-Insert does not enforce.** The proof says a subtree fiber
   is “registered by an activation of `m` or of one of `m`'s descendants, hence
   at a step after the L-Begin of `m`”. Table-1 O-Insert requires only a present
   parent, current freshness, and provision disjointness; it does not identify
   a parent iterator step or yielded inverse. Checked inactive-parent,
   remove/reissue, and retired-parent/open-child traces expose that mismatch.

   Round 3's report was incremental. Its early cross-subtree counterexample
   applies to the submitted **phase/order-only** `RegistrationDiscipline`: merely
   seeing `Reloading` plus a timely O-Retire does not identify what the program
   yielded and admits an alternating mixed support cycle. The later VERIFIED
   disposition concerns the stricter intended formulation. This revision makes
   that distinction a type distinction. `RegistrationProvenance` ties every
   child insertion to the actual nonempty head `StepEffect`, its fixed suffix,
   an optional `registrationYieldTag`, a shared deterministic
   `RegistrationProtocol` catalog, and an admitted component rank whose yielded
   and precedence edges strictly increase. `RegistrationDiscipline` adds the
   inverse O-Retire-before-recovery obligation needed by Lemma 70 and Confluence;
   Lemma 68 itself requires only `RegistrationProvenance`.

   For this local-rule support theorem the former no-rebirth condition was
   removed: the preservation discussion (lines 1855–1858) allows reissue under
   LOCAL freshness. This does not waive Theorem 73's missing GLOBAL-freshness
   hypothesis, implemented for the research confluence telescope in R173.
   Located occurrence evidence distinguishes births in the broader local model. The finite catalog tag/rank is an explicit
   host representation delta necessitated by the absence of a recursive
   component yield channel in `runStepEffect`; it is not claimed to be a paper
   rule. It is also an **over-approximation** of one Definition-47 application:
   because the separate O-Insert rule does not consume the iterator head, one
   live tagged source occurrence may license several fresh child names. This is
   more permissive than the paper's one-fresh-name application. It does not
   invalidate Lemmas 68/70: every admitted child still has a strictly higher
   component rank and its own retirement obligation, so duplicating a target
   rank cannot create a support cycle.
6. **Erratum #4 / proof-intent ambiguity in Lemma 72.** The prose says to delete
   “steps that act on n”, which literally includes O-Retire under Definition 53,
   but the proof immediately claims those steps write only `theta_n` and
   Theorem 73 must preserve external orchestration. A checked retirement episode
   shows literal deletion falsifies the control conclusion. `EpisodeDeletedActor`
   therefore follows the proof intent: it deletes only selected lifecycle steps;
   selected O-Retire/O-Remove survive, while every R-owned action remains
   deletable.

7. **Lemma 56 under local-rule reuse: necessity of the global-freshness hypothesis.**
   Lemma 56 states equivariance for one bijection on raw names, while the
   Preservation discussion explicitly permits O-Remove followed by reuse of
   the freed raw name. Those clauses do not compose across two complete traces
   when one raw name denotes a historical generated child and later a shared
   live root: the historical child may need to map to a different fresh raw
   name, while the current root is an externally fixed input. The mechanization
   therefore uses `RegistrationGenerationBijection` on `(raw name, birth
   ordinal)` for historical/generated registration trees, and a separate
   `CurrentEndpointRenaming` for the current registries with live roots fixed.
   This is a generation-wise interpretation for the broader local-rule model,
   not a paper or implementation bug; confluence additionally assumes R173's
   global uniqueness, matching the implementation's never-reused UIDs.
8. **Likely clarification needed for Theorem 73's final equivalence.** Lemma 57
   makes a vestigial entry observationally equal (`approximately equal`) to its absence, and
   Lemma 72 promises control equivalence only outside the registered-name set
   `R`. A closing episode may therefore leave a schedule-dependent vestigial
   registry entry without any O-Remove. Read literally, Theorem 73(2)'s claim
   of final control equivalence on the complete raw registry domain is false in
   that ordinary case. `SystemEquivalentByRenamingModuloVestigial` follows the
   proof's outside-`R` boundary: effects remain exact, every non-vestigial
   control entry corresponds exactly under renaming, and an unmatched entry is
   admitted only with an exact discarded-generation Lemma-57 certificate.
9. **CP4 Finding #4 — the CP3 Definition-69 encoding was too weak under
   interleaving.** Rounds 1–10 accepted `ComponentTotalOnProvision` as a
   property of uninterrupted `ProgramFinishes`: one `LocalState` flowed
   directly from each iterator step to the next. The actual LTS permits a
   foreign fiber to mutate ambient `world` between those iterations.

   `DGamma.CP4TotalityChecks` commits the missed countermodel. Root provider P
   declares `ServiceA`. P1 always sets `world=False`; P2 installs `ServiceA`
   exactly when it observes `False`. Every uninterrupted P execution therefore
   installs the key, and `providerUninterruptedTotal` inhabits the old CP3
   predicate. A foreign root T runs between P1 and P2 and sets `world=True`.
   P then finishes Active with an empty table. A clean root consumer C that
   depends on `ServiceA` stays Inactive. The checked endpoint is quiet and
   failure-free, but C is supported from P's declaration and is not Active.
   `oldTotalityInterleavingDivergence` evaluates `True`, while
   `counterexampleTraceTotalityRejected` proves the repaired evidence producer
   rejects this exact schedule.

   This is also the precise connection to Definition 60 that the paper's prose
   mentions: installed-key schedule-independence follows from effect
   independence; P and T are deliberately non-independent. Since Lemma 70 does
   not assume Definition-60 independence, Definition 69 itself must quantify
   any actual activation that finishes, including interleaved activations, as
   the paper literally says. CP3's uninterrupted proxy moved that obligation
   outside the LTS and was unfaithful.

   With supervisor approval, CP4 repairs `TraceComponentsTotal` to certify the
   actual acting fiber's table at each checked actor boundary, a preserved
   strengthening of checking L-Finish alone. `buildCertifiedActionTrace`
   executes schedules while constructing this erased certificate.
   `repairedTotalityInterleavingCheck` evaluates `True` for the same schedule
   after replacing P2 by an always-installing step, and
   `repairedTraceTotalityWitness` constructs its trace-indexed proof value.
   `reachedActiveFibersProvideAll` derives endpoint Active-table totality by
   local-update framing. `ProgramFinishes` and
   `UninterruptedComponentTotalOnProvision` remain only as named rejected
   diagnostics so the regression continues to typecheck.

   **Review status:** this is an approved CP4 statement repair, not an immutable
   proof-only change. Definition 69, Lemma 70, and downstream Lemma 72/Theorem
   73 premises that mention `TraceComponentsTotal` lose their prior accepted
   status until the end-of-CP4 adversarial round re-reviews the repaired shapes.
10. **CP4 Finding #5 — the CP3 Theorem-66 alias omits initial continuation
    validity.** The numeric premise bounds only
    `length (componentProgram component)`. Its `first` state is otherwise
    arbitrary: `registryWellFormed` validates committed views but does not say
    that a `Reloading remaining ...` continuation is a suffix of, or even no
    longer than, that declared program.

    `DGamma.CP4ProgressChecks` pins the countermodel. One root fiber carries a
    component with an empty declared program (`K = 0`) but starts in
    `Reloading` with five well-typed no-op steps. The registry is well formed,
    precedence is vacuously acyclic, the declared program bound is true, all
    five checked transitions are lifecycle rules, and the target remains
    `Just []`, hence `V(0) = 0`. The conclusion nevertheless demands
    `S(0) = 5 <= (0 + 4) * (0 + 1) = 4`.
    `progressAliasCounterexample` maps any inhabitant of the current public
    alias to `Void`; the executable companion evaluates `True`.

    The paper's global convention starts states from valid operational
    histories, so this is an encoding omission rather than a paper
    counterexample. With supervisor approval, the alias now adds the minimal
    explicit `continuationsBoundedBy K first = True` premise: every current
    `Reloading` continuation has length at most `K`, while declared programs
    remain separately bounded.

    `DGamma.CP4ProgressBound.transitionPreservesContinuationsBoundedBy` proves
    the repaired premise is preserved by **all ten evaluator rules**, using
    proof metadata on local updates: insertion starts non-Reloading; retirement
    preserves a continuation; exits stop it; L-Iter shortens it; and L-Begin
    restarts exactly at the declared program, discharged by
    `programsBoundedBy`. `repairedContinuationPremisePositive` gives a checked
    nontrivial Reloading endpoint with four remaining steps at `K=4`, while
    `progressAliasCounterexample` / `progressCounterContinuationRejected`
    prove the old K=0 countermodel is blocked exactly at the new premise. The
    old theorem shape remains named only as the rejected diagnostic
    `UnboundedProgressTheorem`, refuted by
    `unboundedProgressAliasCounterexample`.

    This repair is the same genus as Lemma 68's explicit reached-state premise:
    both expose a paper-global reachability invariant that an arbitrary-state
    finite specialization otherwise loses. Record that parallel in the future
    authors letter. **The repaired Theorem-66 shape requires end-of-CP4
    adversarial re-review alongside Definition 69/Lemma 70.**
11. **CP4 Finding #6 — Theorem 66 omitted the global equality alignment used
    by every sibling trace metatheorem.** `Transition` stores the `DecEq name`
    and `DecEq key` witnesses used by its checked evaluator step, while the old
    Progress alias fixed another pair only for initial invariants, target-turn
    counting, and the conclusion. Without `AlignedTransitions`, preservation
    and the quantitative per-rule proof would have to establish coherence of
    the complete evaluator across arbitrary equality implementations—an
    artifact of the Idris encoding, not a claim in the paper.

    With supervisor approval, `progressTheorem` now carries
    `AlignedTransitions name key world error value nameEq keyEq trace`
    immediately after `LifecycleOnly trace`. This matches the established CP2/
    CP3 encoding used by `orderingTheorem`, `deletionTheorem`,
    `confluenceTheorem`, `alignedTraceWellFormedEnd`, and the trace-level
    installation/resolution results. The paper has one global equality, so the
    premise restores that semantics rather than weakening Theorem 66.
    `DGamma.CP4ProgressChecks.progressCounterAligned` is a checked nonempty
    five-step witness that the new premise is constructive and non-vacuous.
    Finding #6 joins Findings #4 and #5 on the mandatory end-of-CP4 adversarial
    re-review list.
12. **CP4 Finding #7 — Definition-60 restriction reordered actual owned
    tables.** The LTS runs L-Advance and L-Unload functions on the fiber's
    stored `OwnedTable`. The old `restrictOwned` reconstructed a moved effect
    table by iterating the component's provision declaration, so a valid table
    stored in another order was silently canonicalized. Because `StepEffect`
    and accumulators are executable and may inspect binding order, an
    `ActualForwardGenerator` could disagree with its checked LTS transition at
    the actual source. Ten CP3 review rounds missed this because no earlier
    proof connected generated partial maps back to real evaluator endpoints;
    the Step-4 per-rule frames are the first such consumer.

    With supervisor approval, Definition-60/yielded/recovery maps now use
    `restrictOwnedPreservingOrder`, which filters the input table in its current
    order while reconstructing `ownedSound`. Legacy `restrictOwned` remains
    only for the negative regression. Because Idris quantity-0 erasure is not
    proof irrelevance (the CP2 lesson), equality of reconstructed `OwnedTable`
    certificates cannot be assumed. The LTS therefore normalizes L-Advance and
    L-Unload inputs with the same order-preserving constructor used by the
    generated maps. Raw Preservation (all dispatch branches), CP3/Ordering,
    the complete Progress assembly, and every landed CP4 effect frame were
    rechecked after this normalization; the reverse-order runner remains `True`.
    Binding order and values are identical to the stored table;
    only erased certificate identity changes, so observable evaluator/plugin
    semantics is unchanged. `reverseOrderRestrictionRegression`
    pins all three outcomes: actual L-Advance sees reverse order and sets the
    world true, the legacy map sets it false, and the corrected map again sets
    it true. The executable runner prints `True`.

    This deliberately corrects the semantic extension of unchanged premises
    such as `TraceIndependent` and `PrefixRecoveryIndependent`: old concrete
    witnesses for the wrong canonicalizing maps may cease to inhabit them and
    must be revalidated/replaced. `singletonTraceIndependent` plus the concrete
    nonempty effectful `correctedTraceIndependentWitness` and
    `correctedPrefixIndependentWitness` prove the corrected premises remain
    non-vacuous. Statement shapes and their paper-intended meaning—commutation
    of the evaluator's actual maps—do not drift.

    Finding #7 joins Findings #4–#6 on the mandatory end-of-CP4 adversarial
    re-review list. The reviewer must attack both evaluator-faithfulness of the
    order-preserving maps and non-vacuity of corrected independence premises.
    The timed-out `CP3StatementChecks`, `CP3VestigialChecks`, and
    `CalculusChecks` runs are part of the registered clean-validation debt and
    must pass before that review.
13. **CP4 Finding #8 — raw-filter reuse necessity countermodel (not a bug).**
    The accepted CP3 statement used `RegisteredActor (List name)` before and
    after the selected episode. After the selected child generation was
    O-Removed, a legal later O-Insert could reuse its raw name; the raw filter
    then deleted that unrelated root birth too. At a quiet endpoint where the
    reissued root is non-retired with unavailable dependencies,
    `RegisteredNamesWithdrawn` was impossible. This is the same raw-name-reuse
    genus as CP3 rounds 6–7, now surfacing in Lemma 72: necessity evidence
    for Theorem 73's missing global-freshness hypothesis, not a paper or
    implementation bug. The frozen raw premise must be re-verified under
    uniqueness before claiming its satisfiability.

    With supervisor approval, the repair reuses `RegistrationGeneration`.
    `actionGenerationAt` assigns O-Insert its `(raw name, birth ordinal)` and
    every later action the generation current immediately before the step.
    `GenerationActionSubsequence` scans the original trace even across deleted
    actions, so O-Remove closes exactly one generation and a later O-Insert is
    retained. `scanGenerations` now constructs the indexed
    `GenerationTraceScan` certificate for every finite checked trace, exposing
    exact start/end ordinals and live-generation environments for the three
    Lemma-72 segments. `RegisteredGenerationsDuring`, `NoRegisteredEpisode`,
    `ControlEquivalentOutsideGenerations`, and generation-aware
    `RegisteredNamesWithdrawn` now use the same stamp throughout premises,
    filtering, controls, and endpoint withdrawal. Raw canonical endpoint names
    retain the explicitly renamed `RawNamesWithdrawn` relation where a raw
    endpoint omission is intentionally being described.

    `CP4DeletionGenerationChecks` pins the ten-step checked countermodel:
    selected L-Begin; child O-Insert/ORetire; selected finish/retire/leave/
    unload; child O-Remove; then a quiet non-retired root reissue at the same raw
    name. Its runtime check prints `True`. The old one-action raw
    `ActionSubsequence` is proved to delete the reissue, while the repaired
    generation filter is proved to keep that exact checked transition.

    Finding #8 joins Findings #4–#7 on the mandatory end-of-CP4 adversarial
    re-review list. The reviewer must attack scanner ordinal alignment,
    O-Remove/reissue boundaries, current-generation endpoint exemptions, and
    the existing no-O-Remove vestigial cases under the repaired alias.
14. **CP4 Finding #9 — the lifecycle accumulator and Definition-60 yielded
    maps normalized at different rhythms.** After Finding #7, every yielded
    inverse map applies `restrictOwnedPreservingOrder` before its undo. A
    generated-monoid composition therefore normalizes before *every* captured
    inverse, while the evaluator's old lifecycle accumulator
    `accumulator . undo` normalized only once, at the eventual L-Unload. Their
    runtime binding lists remained equal, but each normalization reconstructs
    quantity-0 `UniqueKeys`/`ownedSound` certificates. Quantity-0 erasure is not
    constructive proof irrelevance: identifying the two `OwnedTable` records
    would require equality of erased negative-function proofs and hence the
    forbidden function-extensionality step. This blocked the accumulator-to-
    generated-transformation invariant required by obligation 3.

    With supervisor approval, successful L-Advance now uses
    `pushLocalUndo provision accumulator undo`, definitionally
    `accumulator . normalizeLocal provision . undo`. Commit `babebb6` first
    proved the key runtime fact: normalizing an already confined table preserves
    its complete binding list and order. `normalizeLocalWorld` and
    `normalizeLocalBindings` expose both observable invariants. Thus the repair
    changes only when erased confinement certificates are rebuilt; ambient data,
    table keys/values/order, and plugin-visible evaluator behavior are unchanged.
    The disproportionate alternative—adding a public respect/quotient law to
    every `StepEffect`—was rejected.

    `interUndoNormalizationRuntimeIdentity` executes two existing effectful
    provider steps and compares the pre-repair `undo1 . undo2` accumulator with
    the repaired inter-undo-normalizing accumulator on the same L-Unload-
    normalized state. It compares both runtime world bits and the complete
    ordered binding lists and evaluates to `True`. Mandatory revalidation passed
    for the Section-3/CP2 LIFO module, Metatheory recovery/exit infrastructure,
    raw Preservation's L-Advance/L-Unload branches, the complete Progress proof,
    all changed deletion effect/control frames, corrected nonempty independence
    witnesses, `CalculusChecks`, and `CP3VestigialChecks`. The first vestigial
    check attempt exited 137 at the known support-solution resource boundary;
    rebuilding `CP4SupportSolution` alone and then rerunning the two heavy check
    modules succeeded. The combined runtime tuple for the new regression plus
    the 23/18, 27/18, and live-provider vestigial checks was
    `(True, (True, (True, True)))`.

    Finding #9 joins Findings #4–#8 on the mandatory end-of-CP4 adversarial
    re-review list. The reviewer must attack observable equivalence of both
    normalization repairs together, especially multi-effect accumulator order
    and Definition-60 correspondence.
15. **CP4 Finding #10 — lookup equality forgot a host-observable table order.**
    The first foreign-effect induction for Theorem 61 exposed a missing
    congruence used explicitly in the paper's proof: each generated map must
    carry effect-equal states to effect-equal states. `EffectStateRelated` had
    compared ambient state exactly but tables only by per-key lookup. Two unique
    dependent tables with the same bindings in different orders were therefore
    related, even though Finding #7 established that `StepEffect` is executable
    and may inspect that order. A later foreign map could distinguish related
    states, so pairwise `PartialCommute` alone could not transport the recovery
    induction hypothesis.

    With supervisor approval, `EffectStateRelated.tablesExact` now requires
    pointwise **whole `CoeffectContext` equality** for each actor name. This
    keeps the name-to-table function extensionality-free while retaining the
    complete binding list/order and its erased uniqueness certificate. It is
    the consistent completion of the Finding-#7 -> Finding-#9 design chain:
    Definition-60 preserves evaluator order, the lifecycle accumulator matches
    its normalization rhythm, and the equality used to compose those maps no
    longer forgets an observation available to the host. The rejected
    alternative was a new `PartialMapRespects` premise on `TraceIndependent`;
    that would strengthen every metatheorem premise while leaving the defective
    alleged exact relation in place.

    `legacyOrderBlindnessWitness` constructs two full effect states related by
    the old lookup-only relation. `strengthenedRelationRejectsOrderMismatch`
    proves the same pair cannot inhabit the repaired relation, and
    `effectRelationOrderRegression` executes an order-sensitive witnessed
    `StepEffect` on both tables and evaluates to `True`. All exact-effect frame
    proofs were strengthened from per-key lookups to whole-table equalities.
    A warm package build rebuilt/passed all 93 modules, including
    `CP3StatementChecks`, `CP3VestigialChecks`, `CalculusChecks`, the recovery
    modules, independence witnesses, and every deletion frame. The executable
    validation tuple for the new regression, Finding-9 inter-undo regression,
    Finding-7 restriction regression, the complete vestigial aggregate, and
    the complete calculus aggregate was
    `(True, (True, (True, (True, True))))`.

    `SystemEquivalentByRenamingModuloVestigial.exactRenamedTables` is a
    separate renamed-table lookup family rather than an `EffectStateRelated`
    consumer, so its proposition did not shift in this repair. Nevertheless
    the 23/18 and 27/18 correspondence witnesses and live-provider rejection
    were recompiled and executed successfully. Its separate order sensitivity
    remains on the end-of-CP4 endpoint-equivalence review list; no unapproved
    alias change was folded into Finding #10.

    **Replay-boundary addendum.** The first `NoEpisodeReplayBoundary` scaffold
    incorrectly asked for term-level `SystemState` equality with an
    `InactiveLeafDeletionPlan` target. Commuting a retained action past those
    deletions preserves the exact ambient state and ordered runtime binding
    list, but the two construction orders can synthesize different erased
    `UniqueKeys` proof terms. With supervisor approval, the boundary now states
    exactly ambient/binding equality and carries survivor well-formedness;
    `transportApplyActionAcrossRuntimeSnapshot` proves all eight evaluator
    cases preserve tags and runtime snapshots and reconstructs a real raw step.
    `CP4RuntimeBindingsChecks` pins two separately defined singleton uniqueness
    certificates and checks both observation equality and successful O-Retire
    transport. This is the same Finding-#10 representation principle, not a new
    theorem-alias repair: ordered bindings are observable, uniqueness proofs
    are not.

    Finding #10 joins Findings #4–#9 on the mandatory end-of-CP4 adversarial
    re-review list. The reviewer must attack Findings #7, #9, and #10 as one
    ordered-table design chain, as well as the still-separate renamed endpoint
    table relation.

16. **CP4 Finding #11 — recovery is exact on the canonical evaluator domain,
    not on every proof-distinct `LocalState`.** Finding #9 made every yielded
    inverse map normalize its local input before invoking the callback. The old
    `StepEffect.stepWitness` only proved `undo after = before`, which says
    nothing about `undo (normalizeLocal provision after)`. The first attempted
    unconditional replacement,
    `run ... before = Right (after, undo) -> undo (normalizeLocal provision
    after) = before`, is uninhabitable for the public callback interface: the
    identity step may be called directly with a provision-confined table whose
    erased `UniqueKeys`/soundness witnesses are propositionally noncanonical.
    It would then require `normalizeLocal provision before = before`, although
    normalization deliberately rebuilds those certificates. Runtime bindings
    are identical, but Idris intensional equality correctly distinguishes the
    proof-bearing records.

    With supervisor approval, the old law was replaced rather than retained:
    `stepWitness` now requires
    `normalizeLocal provision before = before` and concludes
    `undo (normalizeLocal provision after) = before`. This is the exact domain
    used by the evaluator and Definition 60. The companion keystones
    `restrictOwnedPreservingOrderIdempotent`, `normalizeLocalIdempotent`, and
    `restrictedLocalCanonical` prove that one ordered restriction produces a
    canonical fixed point. `advanceSourceStepRecovery` discharges the premise
    for L-Advance's owned-table source;
    `DGamma.Metatheory.yieldedInverseStepRecovery` does so for the arbitrary
    full-effect-state restriction used by Definition 60; and
    `pushLocalUndoRecoversStep` proves that a successful pushed undo supplies
    the older accumulator with the canonical recovered source. Thus induction
    over the composed accumulator chain cannot pass a proof-noncanonical local
    state to a later undo.

    Every concrete `StepEffect` author was rechecked under the conditional law:
    the four calculus examples, both CP3 registration examples, the
    generation-reissue registration step, the order-sensitive restriction
    regression, and all four Definition-69 totality regressions. The
    order-sensitive checks additionally specialize the fixed-point,
    L-Advance, yielded-map, and pushed-accumulator lemmas so the three required
    application sites remain typechecked. One forced `CP3StatementChecks`
    rebuild was killed at the known `CP4SupportSolution` resource boundary
    (exit 137); an immediate no-concurrent-Chez retry rebuilt the support
    solution and then `CP3StatementChecks` successfully. This is a warm targeted
    pass and does not discharge the registered cold-archive validation debt.

    Finding #11 joins Findings #4–#10 on the mandatory end-of-CP4 adversarial
    re-review list. Review must attempt a proof-relevant noncanonical table at
    every direct `runStepEffect` entry point and a multi-undo chain whose
    intermediate worlds and ordered bindings differ.

17. **CP4 Finding #12 — Equation-53 accumulator controls compared erased proof
    terms rather than runtime states.** The retained-foreign L-Advance replay
    exposed the last inconsistent layer in the Finding-#10/#11 representation
    boundary. A replayed iterator runs at the recovered effect origin and stores
    the inverse yielded there. `TraceIndependent.iteratorYieldsStable` correctly
    relates that inverse to the original one by exact ambient state and complete
    ordered table bindings. The old `AccumulatorRelated`, however, demanded
    literal equality of the two proof-bearing `LocalState` outputs at every
    input, including erased `OwnedTable` uniqueness/confinement certificates.
    That stronger obligation neither follows from Definition 60 nor denotes an
    observation available to the executable host.

    With supervisor approval, `LocalStateRuntimeRelated` now records exact
    ambient and ordered-binding equality, and `AccumulatorRelated` is its
    pointwise lifting. All lifecycle/control, renaming, endpoint, and vestigial
    relations continue to carry complete runtime information while no longer
    requesting proof irrelevance. This is the paper-faithful reading of
    Equation 53: ordinary state equivalence has no erased-certificate identity.
    Strengthening `TraceIndependent` to proof-bearing equality was rejected as
    both unfaithful and unusable by real components.

    **Canonical-domain implementation addendum.** `pushLocalUndo` now composes
    as `older . normalize . undo . normalize`: every yielded inverse receives a
    canonical input by construction, while the already-present post-undo
    normalization gives the older accumulator one exact canonical argument.
    L-Unload already normalizes the initial input and every older undo already
    sat behind a normalization, so evaluator/plugin behavior on the reachable
    domain is unchanged. `pushLocalUndoRuntimeRelated` is the named composition
    keystone: runtime-related yielded inverses normalize to one exact local
    argument before invoking the older related accumulators. The existing
    two-step `interUndoNormalizationRuntimeIdentity` regression compares the
    pre-normalization chain to the wrapper chain and still evaluates `True`.
    `pushLocalUndoRecoversStep`, accumulator factorization, and selected effect
    recovery were mechanically adapted with the Finding-11 fixed-point law.

    `DGamma.CP4AccumulatorControlChecks` pins the distinction with two
    separately constructed singleton uniqueness certificates. The rejected
    `OldExactAccumulatorRelated` diagnostic exposes the former proof-bearing
    state-equality obligation; the repaired relation constructs both a direct
    accumulator witness and a non-vacuous `FiberControlRelated` witness, while
    the runtime binding check evaluates `True`. A full warm 131/131 package
    rebuild re-established every direct consumer, explicitly including
    `CalculusChecks`, `CP3StatementChecks`, `CP3VestigialChecks`, Theorems
    61/62/64, all renamed-control/vestigial pairs, and the selected/deletion
    proof chain. The combined Finding-12/multi-step runtime tuple is
    `(True, True)`.

    Finding #12 joins Findings #4–#11 on the mandatory end-of-CP4 adversarial
    re-review list. Findings #7/#9/#10/#11/#12 are one observable-truth review
    unit: evaluator order, normalization rhythm, exact effect tables,
    canonical recovery, and accumulator control observations must be attacked
    together.

    **Relational replay addendum.** The selected-episode quotient confirms the
    same representation boundary one level higher: Theorem 61 returns exact
    ambient/ordered-table agreement and extensional accumulator control, not
    equality of proof-bearing `Fiber` values. Consequently the recovered
    survivor cannot constructively seed `NoEpisodeReplayBoundary`'s exact raw
    registry-binding snapshot without function extensionality and proof
    irrelevance. With supervisor approval, public Lemma 72 remains unchanged
    while `RelationalNoEpisodeReplayBoundary` becomes the primary
    selected-to-suffix interface: complete current-R plan plus
    `EffectStateRelated` and an ordered control-binding relation (projecting to
    `ControlEquivalent`) against the plan target. Ordering is retained because
    provider selection is executable and scans the registry list. The old exact
    boundary embeds as its runtime-snapshot specialization. A parallel
    relational suffix fold will be used rather than mechanically replacing the
    already-proved exact fold; this avoids destabilizing the 0eeef3d lifecycle
    case split, and the exact fold remains a useful regression specialization.
18. **CP4 Finding #13 / candidate paper Erratum #4 — Definition 60 omitted
    failure-outcome agreement.** The retained-foreign L-Advance proof reached
    L-Raise and exposed that the old `IteratorYieldAgreement` projected every
    `Left error` to `Nothing`. It therefore certified two evaluations of the
    same iterator that failed with different errors, even though L-Raise stores
    that error in `Unloading` and Equation 53 compares outcomes exactly. The
    paper makes the same omission literally: after Equation 54 it says
    Definition 60 is read with **“Right around the triple”**, and Equation 55
    compares only `pr2,3`. That is insufficient for Lemma 71, Lemma 72, and
    Theorem 73 once a transposed evaluation fails.

    With supervisor approval, `IteratorStageOutcome` now distinguishes an
    unavailable capability, `IteratorRaised error`, and a successful
    `IteratorYielded` triple. `IteratorOutcomeAgreement` keeps the successful
    continuation/inverse-map clauses unchanged and adds exact error agreement;
    `TraceIndependent.iteratorYieldsStable` now carries that repaired outcome
    relation. The old success-only `IteratorYieldAgreement` remains available
    as an explicitly rejected diagnostic rather than silently changing its
    meaning.

    `DGamma.CP4FailureOutcomeChecks` pins the defect in both directions. One
    callback returns `ColdError` or `HotError` according to ambient state. Its
    two evaluations inhabit the old premise as `IteratorBothUndefined`, and
    both checked L-Raise endpoints exist, but exact `ControlEquivalent` is
    constructively impossible because their stored outcomes differ. The new
    premise is constructively refuted by `repairedFailurePremiseRejected`.
    Conversely, `agreeingFailureTraceIndependent` is a genuinely failing
    nonempty checked-trace witness under the repaired relation; the existing
    never-failing singleton witnesses and all recovery consumers remain the
    mandatory revalidation set.

    **Erratum #4 for the future authors letter.** Definition 60 must require
    equal observable failures when corresponding iterator evaluations both
    raise (and must reject raise/yield or raise/undefined disagreement). The
    phrase “reading Right around the triple” makes the witness vacuous exactly
    where L-Raise writes a schedule-visible control outcome. Without this
    clause Theorem 73 is false: independent schedules may finish with distinct
    error controls. This is the same proof/definition mismatch genus as Lemma
    68's rank argument—the proof uses an invariant that the stated premise does
    not enforce.

    Finding #13 joins Findings #4–#12 on the mandatory end-of-CP4 adversarial
    re-review list. Failure/value transport and successful yielded-inverse
    transport must be attacked together at retained L-Advance boundaries.
19. **CP4 Finding #14 — resolved by committed-provider persistence (not an
    erratum).** During the selected-episode fold, a crossing foreign activation
    can open before the selected L-Begin and close before the selected L-Unload.
    The first attempted countermodel let actor A commit dependency key `k`, then
    inserted/activated selected S so that S became a live candidate for `k`
    during A's activation. That sketch is not executable. A's successful
    L-Begin already requires an active provider P for `k`. If S existed at A's
    opening and its component declared `k`, `PrecedenceEdge S A` holds even when
    S itself was Inactive/table-empty, so `NoDependentClosingEpisode` rejects
    the trace. If S was absent, later O-Insert S fails the
    `provisionsDisjointFrom` guard while P remains. P cannot be withdrawn while
    A's committed view relies on it, and raw-name removal/reissue hits the same
    insertion guard. The initially proposed weakening was therefore retracted;
    no false countermodel module was added.

    The checked resolution is the named reusable theorem
    `committedProviderProvisionPersists`: a provider observed in the committed
    view at a later point of one installed activation was already committed at
    every earlier point. `crossingActivationExcludesSelectedProvider` transports
    a hypothetical selected candidate back to A's L-Begin boundary, reconstructs
    the forbidden precedence edge, and eliminates it with the unchanged public
    premise. `selectedEpisodeLifecycleAnchorProvider` combines that closing
    branch with the selected-L-Unload reliance branch. The complete selected
    dispatcher and structural fold now compose from public Lemma-72 premises via
    `selectedClosedEpisodeFoldFromPremises`.

## Escape-hatch and hole audit

There are no uses of `believe_me`, `assert_total`, `postulate`, unsafe FFI, or
`%default partial`. Every Idris module has `%default total`.

The following are statement-only `Type`s. They export no value and therefore
cannot silently introduce a proof:

- `OperationsRespectIndistinguishability` and
  `CoarsestRespectedEquivalence` — Lemma 35.
- `distinctKeysIndependent` — Theorem 40.
- `MediatedIndependenceTheorem` — Theorem 42.
- `deletionTheorem` — Lemma 72.
- `confluenceTheorem` — the finite explicit-registration form of Theorem 73,
  with parent-activation structural matching, exact historical external-root
  coupling, non-vestigial current-generation renaming, and final control
  equivalence modulo exact trace-derived Lemma-57 vestigials.

Each open theorem is marked `TODO(proof)` at its declaration. These are honest
uninhabited statements, not holes accepted by the compiler. `orderingTheorem`
is no longer on this list: `DGamma.Ordering.orderingTheoremProof` inhabits it.
`progressTheorem` is likewise inhabited by
`DGamma.CP4ProgressProof.progressTheoremProof`.

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

## Checkpoint 2

### Section 4 calculus through Theorem 64

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
  equation and `fire` packages executable results. Separately,
  `preservationTheoremProof` proves raw Theorem 59 directly from source
  well-formedness and an `applyAction` equation for every rule branch; it does
  not use checked target admission.
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
  At the CP2 checkpoint both remained statement-only pending the temporal
  induction; CP4 now proves both.

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
  and dynamic provider-value constancy. `orderingTheoremProof` now proves the
  complete statement by factoring snapshot/value induction from strict
  last-opening/first-closing episode extraction.
- The global `resolutionStructureTheorem` is anchored by `EpisodePrefix`, so the
  round-1 Unloading-suffix counterexample is unrepresentable. The local
  Equation-59 facts and the whole-episode first-exit split are proved by
  `resolutionStructureTheoremProof`. `resolutionCoherenceFromTerminalRecovery`
  proves all remaining dependent packaging from Corollary 62. CP4 has now
  proved terminal recovery, leaving only the direct exported proof binding.

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

The report correctly rejected the old `preservationTheorem` name: at that
review point its proof was only the target check embedded in
`checkedApplyAction`. That lemma is now named `checkedTransitionTargetValid`.
The later proof-bar pass proves raw Theorem 59 directly and locates the selected
fiber's first exit after the maximal Reloading prefix. Checkpoint 3 subsequently
proves global provider-episode selection in `DGamma.Ordering`; no checked-monitor
lemma is substituted for that result.

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
- `TraceIndependent`, `PrefixRecoveryIndependent`, and `ForeignReplay` accept
  only `PartialEffectMap`; their APIs contain no world-projection map.
  `accumulatorEffectMap` uses the same type. The round-4 section below records
  the subsequently discovered and repaired per-yield omission.
- Theorem 61 and Corollary 62 conclude one full-effect replay relation. The
  disconnected `SelectedTableRecovered`/`TerminalTableRecovery` appendages were
  removed. Premises therefore structurally observe exactly what conclusions
  claim.

### Round-4 yielded-inverse generated-monoid repair

Round 4 (`review-cp2-round4.md`) accepted both CP2 bar proofs but found a new
recovery blocker. The prior `TraceIndependent` quantified actual Table-1
forward maps, while `PrefixRecoveryIndependent` compared foreign maps only with
the final composite accumulator. Two equal noncommuting yielded inverses can
cancel in that composite, so its commutation does not imply commutation of each
factor. The reviewer's four-state executable probe reached exactly this case:
the composite accumulator was identity, but removing the selected actor yielded
`Q3` while foreign replay yielded `Q1`. The old Theorem-61/Corollary-62 premises
were therefore false, not merely conservative.

The repair restores a finite full-effect-state form of paper Equations 54–55:

- `ReachableSuffix` is the continuation closure for the finite-list iterator;
  `IteratorStage` anchors every nonempty reachable suffix at an actual
  L-Advance occurrence.
- `iteratorStageEffect` exposes the exact forward result, individual yielded
  inverse, and explicit fixed continuation at every full `EffectState` origin.
- `TraceEffectGenerator` includes actual Table-1 forwards, every reachable
  continuation forward, and every per-origin yielded inverse.
  `TraceEffectTransformation` closes these generators under identity and
  composition, giving the partial transformation monoid `M(i)`.
- `TraceIndependent.generatedMonoidsCommute` quantifies every transformation of
  distinct actors; `iteratorYieldsStable` separately requires inverse and
  continuation agreement when a foreign generated transformation moves the
  origin. `yieldedInverseCommutes` directly projects the per-factor obligation,
  so cancellation in the final accumulator cannot hide a bad inverse.
- `PrefixRecoveryIndependent` is now the same generated-monoid family premise,
  not a final-accumulator commutation certificate. The actual accumulator
  remains fixed by `actualAccumulatorAt`; the deferred Theorem-61 induction
  must derive its factorization from the yielded generators.
- This is intentionally the finite calculus's continuation closure: each
  continuation is a static list suffix. Data-dependent/coinductive iterator
  continuations and nested registration remain documented representation
  restrictions rather than silently omitted Equation-55 fields.

`yieldedInverseGeneratorRuntimeCheck` executes one stage and its separately
exposed full-state inverse, checking restoration of ambient state and the actor
owned table. Round 5 reran the composite-accumulator, individual-factor,
later-suffix, and origin-shift attacks; all were rejected, and CP2 was approved.

Two conservative deltas remain explicit after that approval. First,
`ActualForwardGenerator` includes every actual action, so off-origin O-Insert
and O-Remove table-clearing maps are generators even though the literal paper
assigns orchestration maps identity. This can reject a paper-independent trace
but cannot admit an invalid one. Second, the reviewer constructed separate
positive witnesses for a nonempty two-actor control trace and a one-actor
effectful trace; the repository still lacks a single fully effectful two-actor
interleaving independence witness. This is useful future regression coverage,
not a soundness blocker.

Reusable dependent-map frame lemmas `lookupReplaceOther`,
`lookupDeleteOther`, and `lookupInsertOther` were added to `DGamma.Coeffects`.
Definition 58 now uses explicit `parentsInvariant`, `chainsInvariant`, and
`viewsInvariant` recursors rather than opaque library folds, and
`parentChainFuelMonotone`/`chainsFuelMonotone` prove that insertion's extra fuel
preserves every existing acyclicity check. These are shared infrastructure for
raw Preservation, lifecycle frames, and later trace deletion/permutation proofs.

### CP2 proof-bar completion and audit

- `preservationTheoremProof` dispatches over every raw action and proves all
  Definition-58 clauses without using `checkedApplyAction` or target admission.
- `InstalledTrace` is aligned with the episode's `nameEq`/`keyEq` dictionaries.
  Every successful action is classified as a single-name registry update;
  foreign lookup frames and selected lifecycle lemmas then prove
  `committedProvidersInstalledTrace`.
- `classifyReloadingStep` separates a continuing foreign/ORetire/L-Iter step
  from Finish, aborting/landing Divert, or Raise. Invalid selected actions are
  eliminated from the exact raw equation. `resolutionStructureInstalled`
  inducts over the aligned trace, prepends continuing steps, and carries a
  found exit through the remaining suffix. `resolutionStructureTheoremProof`
  starts this induction from the exact L-Begin snapshot.
- The clean git-archive build succeeds, `allRuleChecks` (including the
  per-yield inverse runtime regression) evaluates to `True`, all modules retain
  `%default total`, and the escape-hatch scan finds no
  `believe_me`, `assert_total`, postulate, unsafe FFI, `%default partial`, or
  metavariable holes.
- **Deferred global-ordering debt:** CP3 now addresses this with indexed global
  trace splitting, name-reuse boundary extraction, Lemma-54 lifecycle/view
  frames, and the forward relied-guard argument. CP2 did not silently replace
  it with local `reliedProviderCannotUnload`.

### CP3 dictionary-alignment encoding premise

`orderingTheorem` now takes `AlignedTransitions nameEq keyEq global`. Idris
retains distinct `DecEq` implementations as distinct values even when erased,
so a transition built with an extensionally equivalent dictionary cannot be
repackaged definitionally as the `BeginStep`/`UnloadStep` required by an episode.
The paper has one ambient equality decision procedure and no corresponding
issue. `AlignedTransitions` makes the proof-LTS convention explicit: every
transition in the searched global trace uses the theorem's dictionaries. It
changes no runtime rule or guard and is the same dictionary-alignment discipline
already used by `InstalledTrace`; omitting it would amount to silently assuming
proof irrelevance. The paper-explicit `consumer /= provider` premise is also now
present in the finite Ordering statement rather than recovered indirectly from
provision disjointness.

## Checkpoint 3 — Ordering, Progress, and Confluence

### Fully proved global Ordering (Theorem 63)

- `orderingTheoremProof` inhabits the exact exported `orderingTheorem`; the
  theorem is no longer statement-only.
- `resolvedConstantInstalledTrace` transports the committed consumer snapshot
  across every installed step without proof irrelevance or function
  extensionality.
- `providerValueConstantTrace` proves provider-value constancy. Foreign actions
  use lookup frames; ORetire and LLeave have factored selected-provider proofs;
  impossible selected LBegin/LAdvance/LDivert/LUnload cases are eliminated from
  stable-provider and installed-boundary evidence.
- `extractContainingProviderEpisode` selects the last provider opening before
  the consumer and the first provider closing after it. Its two
  `StrictTransitions` and prefix equations prove strict containment in the same
  global trace, including name reuse.
- `DGamma.Ordering` isolates final assembly from the large CP3 module. This is
  an elaboration-performance split only; it changes no theorem premise.

### Fully proved Progress (Theorem 66)

`DGamma.CP4ProgressProof.progressTheoremProof` inhabits the approved repaired
finite-trace alias. The proof combines four constructive layers:

1. `CP4ProgressNoDeadlockFinal` scans all lifecycle shapes and follows blocked
   Unloading reliance through finite precedence accessibility.
2. `CP4ProgressStep*` proves strict same-target potential consumption for every
   successful L-Begin, L-Advance outcome, L-Divert, L-Leave, and L-Unload rule.
3. `CP4ProgressNumeric.actorTraceEquation61` performs the amortized induction:
   the initial potential pays the first interval and each `TargetChanged`
   constructor contributes one fresh `K + 4` budget.
4. `CP4ProgressProgramBound` and `CP4ProgressPrecedence` preserve the declared
   program bound and precedence acyclicity along lifecycle-only traces, allowing
   the endpoint no-deadlock theorem to use the initial public premises.

CP4 Findings #5 and #6 remain approved statement repairs pending the mandatory
end-of-CP4 adversarial review. The old continuation shape remains constructively
refuted; no escape hatch was introduced.

### Confluence (Theorem 73): parent-local structural statement and proof debt

The finite explicit-registration specialization remains stated and is being
resubmitted for round-10 review. Rounds 6–8 established generation stamping,
parent-local matching, historical-root coupling, activation-local positions,
and surviving-only tree matching. Round 9 accepted all of those repairs but
found their downstream endpoint projection still exact-domain: a discarded
birth left vestigial rather than O-Removed had to biject again and the theorem
result could not express its absence on the other side. The proposition now
separates seven roles:

1. **One-step episode deletion (Lemma 72).** `KeepAction` remains
   bidirectional, but `DeleteEpisodeLifecycle` additionally requires
   `isLifecycleAction=True`. Thus selected L-Begin/body/L-Leave/L-Unload steps
   are removed while selected O-Retire/O-Remove survive; every R-owned action is
   still removed. Open-R exclusion, relevant-time dependencies, all-trace
   totality, yielded-registration provenance, effects, and outside-R controls
   remain explicit. The checked replay proof is open.
2. **Yielded registration.** `StepEffect.registrationYieldTag` and the shared
   `RegistrationProtocol` catalog connect each child O-Insert to the exact
   nonempty head step and fixed continuation of its live parent. Protocol ranks
   strictly increase along yielded-parent and precedence edges. This is the
   documented explicit-host repair for the paper's Lemma-68 provenance gap.
3. **Surviving parent-activation matching.**
   `RegistrationGenerationBijection` acts on `(raw name, birth ordinal)`, not
   on raw names. `RegistrationActivation` pairs the live parent generation with
   its exact `L-Begin` ordinal. `L-Begin` resets that activation's child
   position to zero; `L-Unload` clears it. A generated birth may enter the
   pending tree only with `SurvivingRegistration`, whose suffix proves
   `NoParentUnload`; it may be skipped only with
   `DeletedClosingRegistration`, which supplies the exact activation plus an
   `ActionOccurs (LUnload parent)` proof. Therefore births from deleted closing
   episodes neither match nor consume positions. `RegistrationEventMatch`
   requires the same component, mapped child and parent generations, matching
   concrete activation witnesses (whose opening ordinals may differ), and equal
   **parent-activation** positions. It preserves one activation's iterator/yield
   order but imposes no
   chronological order between different parents.
4. **Historical external roots.** `SameExternalOrchestration` still compares
   externally supplied root actions in exact raw-name order.
   `ExternalRootBirthCorrespondence` additionally scans every historical root
   O-Insert, including roots removed before the endpoint, and requires its
   generation to map to that exact same matched root birth. Generated subtrees
   cannot be reassigned by permuting removed external-root generations.
5. **Current endpoint names.** `CurrentEndpointRenaming` contains the raw
   `NameBijection`, fixes every live root, and requires each **non-vestigial**
   current generation to agree with the generation bijection. A generation may
   be omitted only with `VestigialEndpointGeneration`: its exact current stamp
   occurs in `indexedDeletedGenerations`, and the endpoint fiber is retired,
   `Inactive Nothing`, empty-table, childless, and unsupported. The executable
   `vestigialEndpointGeneration` checks those runtime fields; a metadata flag
   alone cannot manufacture the witness.
6. **Final endpoint equivalence.**
   `SystemEquivalentByRenamingModuloVestigial` keeps ambient state and every
   effect-table lookup exact under the raw renaming. Its pointwise control sum
   requires `MaybeFiberRelatedBy` whenever either side is non-vestigial; every
   unmatched present entry on either side must carry the complete vestigial
   certificate above. Thus loosening the premise does not leave a false exact-
   domain conclusion. `supportedGenerationNotVestigial` proves directly that a
   live supported fiber cannot enter the exception.
7. **Canonical deletion.** `CanonicalRegistrationCorrespondence` still maps
   located occurrences injectively and keys removals by exact generations.
   `CanonicalEndpointRelation` separates historical
   `endpointWithdrawnGenerations` from current `endpointWithdrawnNames`, and
   `CanonicalInputPlacement` quantifies freshness/order per located birth.

Six concrete statement families now cover the repaired public domain.
`freshChoiceCorrespondenceWitness` retains round 6's pair: left child `(1,2)`
versus right child `(2,2)`, both followed by the same live root `(1,5)`.
`crossParentPermutationCorrespondenceWitness` constructs two checked 12-action
traces with exact external roots 0 then 1 and the same final registration tree;
the left births children `(2,4)` under root 0 then `(3,5)` under root 1, while
the right births `(3,4)` then `(2,5)`. The pending structural matcher maps
`(2,4)->(2,5)` and `(3,5)->(3,4)` at local position zero under their respective
fixed parent activations. `crossParentPermutationTheorem73PremiseChain` applies
the literal public `confluenceTheorem` after taking every remaining semantic
premise. `episodeBoundaryCorrespondenceWitness` is the hardened round-8 case:
the left trace begins parent 1, inserts child 2, retires/removes it early,
diverts and unloads parent 1, replaces provider root 0 with root 3, reopens
parent 1, and inserts surviving child 4. The right delays parent-1 activation
until after the same provider replacement and inserts only child 4. The deleted
left birth carries explicit closing-unload evidence and is discarded; the
surviving births both elaborate at activation-local position zero.
`episodeBoundaryTheorem73PremiseChain` applies this complete
`SameOrchestrationModuloGenerated` witness through the literal public theorem
boundary after taking all remaining semantic premises. This older 24/18 pair
is retained specifically as the activation-reset/early-O-Remove regression; it
is no longer cited as covering paper vestigials.

`DGamma.CP3VestigialChecks` supplies the missing no-O-Remove cases. The 23/18
pair removes only the early child O-Remove. The 27/18 pair additionally begins
and finishes child 2, retires it while Active, closes parent 1 while the child
is still open, and only then leaves/unloads the child. Both endpoints are
checked quiet and successful with identical supported tree `{1,3,4}`; left
name 2 is an unremoved retired/clean/empty/childless/unsupported vestigial.
`vestigial23CorrespondenceWitness` and
`vestigial27CorrespondenceWitness` construct the complete public same-input
packages. Their `*Theorem73PremiseChain` declarations take every literal public
premise and project the new vestigial-aware final relation from the theorem
result. `liveProvidingFiberRuntimeCheck` confirms root 3 is the supported
ServiceA provider, while `liveProvidingFiberVestigialRejected` eliminates any
attempted vestigial certificate for it at `vestigialUnsupported`.

Conversely, `CompleteRemovedRootPermutationCandidate` contains a concrete
six-action checked history that inserts/retires/removes root 0 and then root 1,
together with an alleged **full** `SameOrchestrationModuloGenerated` relation,
not merely the root-coupling projection. `historicalExternalRootPermutationRejected`
projects the exact first-root equation from that full candidate and eliminates
its `(0,0) <-> (1,3)` historical permutation. Both endpoints are empty, so this
negative check cannot be discharged accidentally by current-name constraints.

`roleChangingFullCanonicalScheduleStatementCheck` still specializes every
`CanonicalSchedule` constructor field to the nine-action role-changing trace
and forces historical withdrawals to `[(1,2)]` with no current raw omission. It
is an honest full-package assembly check, not a construction of the still-open
canonical sorting proof. `roleChangingCanonicalRuntimeCheck` separately
executes the six-action roots-first replay and confirms quiet, successful,
supported active-root endpoint shapes. The round-6 1-vs-2 witness and this
self-canonical package both still typecheck under the parent-local redesign.

The trace-free `CanonicalEndpointRelation` deliberately cannot validate an
arbitrary historical list. `canonicalEndpointHistoricalOnly` is therefore only
a metadata constructor. Historical entries are meaningful only inside
`CanonicalSchedule`, where `canonicalRegistrationTree` proves that each listed
stamp is an actual original child birth removed from the canonical trace.

The older exact-name/zero-current-raw-withdrawal helpers remain proved strong
special cases. Constructive checked deletion, canonical sorting, and general
endpoint assembly remain open. The round-7/8 repairs and round-9 vestigial
endpoint repair now have positive/negative typed regressions, but acceptance is
not claimed before the independent round-10 review.

### Recovery and Theorem 64

At the CP3 checkpoint Theorem 61 and Corollary 62 remained stated because the
actual accumulator still needed a temporal generated-monoid induction. CP4 now
implements that induction and proves both. `resolutionCoherenceFromTerminalRecovery`
shows that Corollary 62 immediately completes the recovery branch of Theorem 64;
`DGamma.CP4ResolutionCoherence.resolutionCoherenceTheoremProof` now performs that
direct assembly, so resolution structure and final packaging are closed.

### CP3 adversarial rounds 1–3: statement redesign in progress

Round 1 accepted global Ordering. Rounds 2–3 exposed false/trivial proposition
shapes in support, deletion, and fresh-name Confluence. The following are
candidate round-5 statements, not accepted proofs:

- The old Lemma-70 alias accepted an arbitrary snapshot and was false on a
  quiet Active mixed cycle (parent edge one way, precedence edge the other).
  `SupportEdge`/`SupportPath` now represent the full Equation-62 relation;
  `ReachedFromEmpty` records an aligned checked trace from an empty well-formed
  registry, but round 2 proved that reachability alone is insufficient.
  `RegistrationProvenance` now exposes the exact tagged parent step/catalog and
  rank needed by Lemma 68. `RegistrationDiscipline` adds only the retirement
  provenance needed by Lemma 70. Post-remove reissue is retained in the local-rule model only; R173 confluence
  additionally assumes global uniqueness, matching never-reused runtime UIDs.
- Round 3 retained `fiberTotalOnProvision` only as an executable current-Active
  diagnostic and replaced it with `ProgramFinishes` /
  `ComponentTotalOnProvision`. CP4 Finding #4 above supersedes that conclusion:
  uninterrupted complete executions do not cover foreign interleaving.
  `ProgramFinishes` and the renamed
  `UninterruptedComponentTotalOnProvision` are now countermodel diagnostics;
  repaired Definition 69 is `TraceComponentsTotal`.
- The old canonical package ordered precedence only and compared lifecycle
  summaries. `LinearizesSupport` now requires `UniqueKeys` and linearizes
  `SupportPath`; `LocatedOpenEpisodeBlock` enforces actor-only contiguity,
  openness, and no earlier/later episode; coverage excludes unsupported
  lifecycle history; and `CanonicalInputPlacement` records located root/child
  birth freshness and ordering. `FiberControlRelated` retains the exact immutable
  component (dependencies, provisions, program), parent, retirement, remaining
  iterator, committed view, outcome, and a pointwise accumulator relation.
- The round-1 `DeletionResult` redesign admitted identity; round 3 then showed
  its selected predicate over-deleted O-Retire. `KeepAction` now requires
  non-deletability and selected deletion is lifecycle-only. Open-R and
  relevant-time totality/dependency guards remain explicit.
- `DGamma.CP3StatementChecks` now applies and projects Lemma 68 rather than
  returning its alias, and separately projects lifecycle-only deletion, yielded
  source/program-membership/rank provenance with a concrete positive inhabitant,
  canonical discipline/located-generation correspondence, block/order
  fields, all deletion segments, effect recovery, Lemma-56 renaming, outside
  controls, and withdrawals. These candidate types remain honestly unproved.

### CP3 adversarial round 4: over-strengthening repairs

Round 4 verified lifecycle-only retirement replay and full endpoint renaming, but
proved the first rank law made every child yield empty: it quantified arbitrary
tagged same-typed steps. `yieldedRankIncreases` now takes
`Elem step (componentProgram parent)`, exactly matching
`ParentRegistrationYield.sourceBelongsToProgram`. `positiveParentRegistrationYield`
in `DGamma.CP3StatementChecks` constructs a concrete nonempty tagged parent,
child, catalog, ranks, and source membership, preventing another vacuity
regression.

The same review identified three downstream shapes. `ActorLifecycleOnly` now
admits a yielded child O-Insert within its parent's canonical block;
`LocatedGeneratedRegistration` and ordinal inverse/injectivity fields replace
raw `ActionOccurs` existence for registration correspondence; live endpoint
roots, rather than every historical raw root name, are fixed by Lemma 56.
Finally, `WithdrawnNameResult` includes the paper-permitted already-removed
absent/absent endpoint case. The recovery-boundary comment now states correctly
that the accumulator executes at L-Unload, not at L-Leave/L-Divert/L-Raise.

These are candidate proposition-shape repairs. Constructive Lemma 72/Theorem 73
proofs and a full positive nested canonical schedule remain open.

### CP3 adversarial rounds 5–9: role changes, generations, and vestigials

Round 5 found that raw-name canonical withdrawal made the checked
child-1-to-live-root-1 trace internally inconsistent. Generation-stamped
canonical accounting repaired that self-canonical case. Round 6 accepted the
repair but found a distinct cross-trace restriction: the global raw
`NameBijection` still forced historical child 1 to remain 1 because the later
live external root 1 had to be fixed, excluding an equivalent trace that chose
fresh child 2. The generation/current-name split and the complete 1-vs-2 public
premise chain repaired that defect without regressing self-canonicalization.

Round 7 then showed that the first generation scanner was not actually a tree
bijection: it consumed the globally first remaining child on both sides. The
reviewer's checked 12-action pair reversed two independent parents' child-birth
interleaving and reached the concrete forced mismatch `(3,4)` versus `(2,5)`.
The same review found the weaker dual: a removed external root was coupled to
its exact raw input only while current, allowing historical root generations
and their subtrees to be swapped.

The round-7 replacement used pending generated events and mapped parent-local
positions, removing cross-parent chronological order, while
`ExternalRootBirthCorrespondence` fixed every historical external O-Insert.
Round 8 then supplied a checked delay/divert/delete/reopen counterexample to the
remaining lifetime-local position. Path A now compares only surviving
activation trees: `L-Begin` creates a new activation stamp and resets position;
a matched birth proves no later parent unload, while every discarded generated
birth proves the closing unload explicitly. The 24-action left/18-action right
hardened pair builds the complete `SameOrchestrationModuloGenerated` package
and crosses the exact public Theorem-73 premise chain. The historical-root
negative now assumes the complete full relation over a checked two-removed-root
history before deriving contradiction. The earlier 1-vs-2 fresh-choice pair,
12-action cross-parent pair, nine-action self-canonical statement package,
positive parent yield, empty-parent rejection, strict-rank cycle rejection, and
identity-deletion barrier remain typechecked.

Round 9 verified the 24/18 activation repair but exposed its early O-Remove as
masking the paper-normal endpoint: discarded birth 2 remained in the current
generation environment when only retired, and exact raw-domain control
comparison could not relate it to absence. The repair is coupled. The scanner
records every discarded generation. `CurrentEndpointRenaming` either matches a
current generation or supplies a fully checked trace-derived vestigial witness;
`ConfluenceResult.finalEndpointsEquivalent` now uses the same exception and is
exact on all effects/non-vestigial controls. The checked 23/18 and activated-
child 27/18 pairs both cross the public premise and result boundaries, while a
supported/providing fiber is rejected.

The old singleton-membership role-change guard remains removed.
`roleChangingFullCanonicalScheduleStatementCheck` assembles every field of a
`CanonicalSchedule` specialized to the concrete nine-action trace, with exact
historical/no-raw-withdrawal equations. Because constructive sorting remains
open, the field proofs remain arguments; this is a full-package statement
regression, not a claimed schedule inhabitant. Likewise
`canonicalEndpointHistoricalOnly` remains unchecked metadata unless coupled to
`canonicalRegistrationTree`.

## CP4 constructive proof debt

The interrupted CP4 worktree was inspected before any edit. It contained a
proof-oriented refactor of `supportPass` into explicit `supportPassEntries`, an
explicit `allList` with the same Boolean conjunction semantics as the prior
library `all`, and a new untracked `DGamma.CP4SupportSolution` module. Nothing
was discarded. The recovered work compiled under Idris 2 0.8.0 and was finished
as Lemma 68.

The accepted `supportWellFoundedTheorem` type is unchanged. The executable
Definition-67 implementation was only definitionally refactored so recursive
proofs can expose one scan step at a time; `supportClause`, `supportCandidate`,
`supportPass`, `supportFuel`, `supportSet`, and `isSupported` retain their prior
runtime behavior. This is not a CP4 statement deviation.

`supportWellFoundedTheoremProof` now constructs both fields of
`SupportWellFoundedResult` without an escape hatch:

1. `DGamma.CP4Support` recovers a protocol rank for every current registration
   from the aligned reached trace. Both an immediate parent edge and a
   provision-precedence edge strictly increase that rank, so every nonempty
   combined support path strictly increases it and cannot cycle.
2. `supportFuelLengthStable` proves that at most the registry length worth of
   successful additions reaches a fixed point. `supportSetIsSolution` proves
   the computed bounded closure satisfies Equation 62.
3. `computedSupportIncludedInSolution` proves leastness by scan/fuel induction.
   The converse `candidateIncludedInComputedSupport` uses accessibility of each
   finite protocol rank: a candidate-supported fiber's parent and providers
   have smaller ranks and are already in the computed closure, making the fiber
   eligible for the stable pass.
4. `supportSolutionUniqueFromRanks` combines both Boolean inclusions pointwise,
   completing Definition-67 support-solution uniqueness.

Every public theorem/proof export in the new module is quantity `0`; auxiliary
fixed-point machinery is private and is consumed only while elaborating those
erased exports. The runtime support computation remains executable. No
statement micro-adjustment, partial definition, postulate, or proof escape was
introduced.

### Lemma 70: support equals Active at quiescence

`DGamma.CP4Lemma70.supportAtQuiescenceTheoremProof` now inhabits the repaired,
otherwise immutable Lemma-70 alias without an escape hatch:

1. `reachedActiveFibersProvideAll` folds repaired Definition-69 certificates
   over the aligned checked trace, so every endpoint Active fiber has every
   declared provision installed in its actual table.
2. `DGamma.CP4ParentSafety` carries each child insertion's
   `ChildRetirementProvenance` forward. A non-retired current child retains a
   parent in `Reloading` or `Active`; a parent recovery step is excluded until
   that child is retired. Quiescence rules out `Reloading`, hence the parent is
   Active. The internal `RetirementUpdate` view added to local replacement
   frames records whether retirement is preserved or explicitly applied; it
   strengthens proof metadata only and does not change evaluator behavior.
3. `DGamma.CP4SupportActive` proves both fixed-point directions. An Active
   fiber's quiet target supplies Active providers, trace totality turns their
   declared provisions into actual provider resolution, and parent safety
   supplies the parent clause. Conversely, a true support clause supplies a
   target; quiescence plus failure-freedom rules out every lifecycle except
   `Active`.
4. The resulting Active predicate is a `SupportSolution`. Lemma 68's unique
   support-solution field then gives the required pointwise
   `isSupported = supportedActiveAt` equality.

The elaboration was deliberately split across three small proof modules after
an initial monolithic assembly exhibited catastrophic elaborator growth. All
proof exports are quantity `0`, `%default total` remains universal, and the
runtime evaluator/support computation is unchanged. The approved Definition-69
statement repair still requires the mandated end-of-CP4 adversarial re-review.

### Theorem 66: unloading-chain no-deadlock

`DGamma.CP4ProgressNoDeadlockFinal.progressNoDeadlockAt` now proves the complete
no-deadlock clause. `CP4ProgressFinite` turns finite acyclic precedence into
accessibility. `CP4ProgressReliance` reflects a true `relied` guard into an
actual consumer and precedence edge; it records the consumer's committed
lifecycle shape at construction. `CP4ProgressUnloadingDescent` then recurses on
that accessibility proof: Reloading advances, Active leaves because its
Unloading provider makes the committed target stale, another Unloading
consumer descends, and an unrelied provider unloads. The registry scanner covers
all lifecycle forms and returns either exact quiescence evidence or a move.

Idris 0.8 exhibited a reproducible elaboration cliff when a 20-plus dependent-
argument mismatch lemma was applied across a module boundary: the application
exceeded ten minutes or was killed, while its direct proof checked in under two
seconds. The final architecture uses one rule case per small module and packages
the Active provider/consumer fields into pre-saturated records in the defining
module. Every landed module checks in roughly 0.7–2.3 seconds. All failed WIP was
SHA256-archived outside the repository before cleanup; no worktree content was
silently discarded.

`DGamma.CP4ProgressPotential` defines the executable same-target lifecycle
potential from Theorem 66(A) and proves its uniform `K + 4` upper bound from
`continuationsBoundedBy`. `CP4ProgressStep*` proves every per-rule decrease,
`CP4ProgressNumeric` proves the amortized Equation-61 trace bound, and
`CP4ProgressProof` assembles the full public theorem.

### Lemma 72 Step-4 frame library

`ActualEffectFrame` states actual-generator soundness relationally with
`EffectStateRelated`; exact `EffectState` equality would require forbidden
function extensionality because effect tables are functions. Complete checked
frames are proved for all ten Table-1 tags. The L-Advance dispatcher covers
empty/effectful L-Finish, L-Iter, L-Raise, and both explicit/landing L-Divert;
L-Unload includes the accumulator's ambient/table recovery. The shared core
proves pointwise insertion, deletion, table-preserving replacement, runtime
replacement, and actual capability resolution frames.

This exposed a real prerequisite omitted by the prior structural work:
`ActualForwardGenerator` packages a checked transition, but Definition-60
commutation alone did not prove that its partial map reaches the concrete LTS
target even up to `EffectStateRelated`.
`actualTransitionEffectFrame` now closes that prerequisite exhaustively.
The control-side suffix frame is now constructive. `providerOfInactiveDelete`,
`resolveViewInactiveDelete`, `resolveCommittedValuesInactiveDelete`, and
`reliedInactiveDelete` show that removing an Inactive leaf cannot change a
surviving fiber's target, valid committed capability, or L-Unload reliance
check. Per-rule modules exhaust L-Begin, every L-Advance landing, L-Divert,
L-Leave, and L-Unload. `checkedLifecycleAfterInactiveDelete` rebuilds a checked
transition using raw Preservation; `checkedLifecycleAfterInactivePlan` iterates
this through an indexed multi-leaf plan whose tail source is definitionally the
prior deletion target. The nonempty `nonemptyInactivePlanControlWitness` crosses
the aggregate with a concrete checked L-Finish.

This closes the Lemma-57/suffix control-applicability theorem, not all of Lemma
72. `GenerationEnvironmentBounded` now proves that every scanner-live birth is
strictly earlier than the next ordinal, and
`deletionBeforeFromRegisteredDuring` combines that invariant with the selected
segment's exact birth stamps. Consequently no R generation can own an action
before the selected episode, and `DeletionResult.beforeDeletion` is
constructively the original prefix retained verbatim.

`decGenerationOwnedActor` and `decEpisodeGenerationDeletedActor` decide the
repaired predicates themselves, not a parallel Boolean approximation.
`filterGenerationActions` then scans the original generation environment even
across erased actions and constructs the surviving checked trace together with
its `GenerationActionSubsequence`. Its `Maybe` failure remains intentional and
honest: it occurs exactly when a non-deletable action cannot be replayed at the
smaller state. Thus action-subsequence construction is complete modulo the
control-applicability invariant that Step 4(b) is deriving; no applicability is
smuggled into the filter.

`splitLocatedNoRegisteredSegments` now performs the public alias's exact
three-way trace split while threading the original scanner ordinal/environment.
It constructs the episode and suffix `GenerationTraceScan` values and restricts
global `NoRegisteredEpisode` to both pieces. `traceComponentsTotalLocatedSplit`
does the same for repaired Definition 69. This removes another previously
implicit appeal to hereditary premises; no extra theorem assumption was added.

`DeletionTraceSkeleton` integrates the verbatim prefix, exact segment scans,
and both dependent generation filters. `assembleDeletionResult` proves the
public result constructor from that skeleton and an erased
`DeletionEndpointEvidence` containing exactly `effectsPreserved`,
`controlsPreservedOutside`, and `registeredWithdrawn`. Final dependent-record
assembly is therefore closed; endpoint debt cannot hide inside existential
bookkeeping.

`buildCurrentRegisteredDeletionPlan` now performs the exact generation-aware
plan construction executable at any boundary: it scans the live generation
environment, ignores non-R generations (including later raw-name reissues),
checks each current R fiber is an Inactive leaf, and constructs both
`InactiveLeafDeletionPlan` and every pointwise actor-outside projection. The
remaining proof obligation is sharply its success from
`RegistrationDiscipline`, `RegisteredGenerationsDuring`, and generation-indexed
`NoRegisteredEpisode`, rather than construction of the dependent plan itself.
`reachedCurrentRegisteredInactive` now proves the Inactive half directly by
forward induction over aligned checked transitions and the generation-indexed
no-episode evidence. It handles insertion, retirement, removal, raw-name reuse,
and rules out every lifecycle action that would require a non-Inactive source.
`CurrentRegisteredChildless` names the structural half, and
`reachedCurrentRegisteredChildless` now proves it by forward induction over the
aligned checked trace. At a fresh birth, well-formed parent closure proves that
an absent raw name cannot already have children; at a later O-Insert, disciplined
`ParentRegistrationYield` provenance would require the current exact R parent
to be Reloading, contradicting the proved Inactive invariant. O-Remove/reissue
is handled by the generation environment rather than a global raw-name ban.
The theorem is stronger than the selected-episode use site: once
`NoRegisteredEpisode` identifies the exact generation list, it does not need to
inspect `RegisteredGenerationsDuring` again. `inactiveAndChildlessGiveLeaves`
combines both halves, and `reachedDisciplinedBoundaryGivesDeletionPlan` derives
the complete exact-generation plan directly from public discipline,
well-formedness, alignment, scan, and no-episode premises.
`CurrentRegisteredInactiveLeaves` is the combined internal boundary invariant;
`currentRegisteredLeavesGivePlan` proves it yields the checked multi-leaf plan,
and `hasChildDeleteFalse` proves iterated leaf deletion cannot create a child.
`generationTraceScanPreservesUnique` proves live raw names remain unique from
`[]`, and `currentGenerationOutsideImpliesActorOutsidePlan` consequently bridges
the public generation-aware outside relation to the builder's pointwise
actor-outside input. `checkedLifecycleAfterCurrentRegisteredPlan` composes that
bridge, the executable plan, and the exhaustive lifecycle control theorem into
one checked replay result. No raw-name global exclusion was reintroduced.

The current-R boundary construction is now complete. The remaining construction
must prove both selected-episode/suffix filters succeed and derive the three
endpoint invariants.
Whether `NoDependentClosingEpisode` suffices for that episode-local bridge remains under active review; no public statement change
has been made.

Obligation 2 now has its complete per-action plan frame. The earlier
`checkedLifecycleAfterInactivePlan` covers all five lifecycle action forms;
`DGamma.CP4DeletionControlOrchestration` adds raw and checked O-Insert,
O-Retire, and O-Remove replay through an arbitrary `InactiveLeafDeletionPlan`.
O-Insert is the important nontrivial case: registry deletion relaxes provision
uniqueness, but a child insertion also reads its parent. The new
`OrchestrationOutsideDeletionPlan` therefore records both owner exclusion and
`InsertionParentOutside` for every erased leaf. This prevents an unsound generic
“orchestration only gets easier” argument.

`DGamma.CP4DeletionRetainedAction` now derives the plan certificates at every
original retained boundary. A successful O-Insert is fresh, hence outside each
present leaf. For child O-Insert, `ParentRegistrationYield` proves its parent is
Reloading, which is incompatible with every Inactive plan leaf. For O-Retire,
O-Remove, and all lifecycle forms, the complement of
`GenerationOwnedActor` plus scanner uniqueness gives the exact current-R
outside certificate. `checkedRetainedOrchestrationAfterCurrentPlan` and
`checkedRetainedLifecycleAfterCurrentPlan` close the checked one-step theorem
for all eight action constructors.

`DGamma.CP4RecoveryAccumulator` closes the first algebraic half of obligation
3. `AccumulatorFactorization` relates the concrete lifecycle accumulator to one
trailing actor normalization after the generated composition of its individual
yielded inverses. `identityAccumulatorFactorization` proves the L-Begin base;
`pushAccumulatorFactorization` proves the inductive L-Advance step using the
Finding-9 `pushLocalUndo` rhythm. The proof is relational because complete effect
states contain a function-valued name-to-table projection: exact function
equality would require forbidden extensionality. `effectOverwriteSameActor`
proves directly that the trailing normalization absorbs the intermediate
selected-table/ambient write. The remaining obligation-3 work is the temporal
trace induction: build the concrete transformation at each selected advance,
commute it across foreign actual generators using `TraceIndependent`, and join
that selected-episode equality to the surviving suffix.
`DGamma.CP4RecoveryTrace.AccumulatorModel` now ties that algebraic object to the
actual installed fiber and exact `AccumulatorHandle`. `beginAccumulatorModel`
proves the L-Begin base directly from the checked evaluator: it extracts the
fresh Reloading lifecycle, identity accumulator, runtime table, and identity
transformation without assuming proof irrelevance.
`foreignStepPreservesAccumulatorModel` proves the complete control-side foreign
step: the exhaustive local-update theorem keeps the selected fiber object,
accumulator, installed-shape evidence, and factorization unchanged. The
remaining temporal step is the selected-action dispatcher plus the effect-side
commutation/replay invariant. `selectedRetirePreservesAccumulatorModel` now
closes the selected O-Retire branch: it reconstructs the exact checked target,
transports all three installed lifecycle shapes through the retirement-only
fiber update, and retains the accumulator transformation/factorization.
`DGamma.CP4RecoveryAdvance.actualIteratorStageYields` now connects a concrete
successful checked L-Advance to the exact Definition-60 `IteratorStage` at the
projected source, including the evaluator's resolved capability, resulting
ambient/table state, yielded inverse, and continuation. The derived
`successfulAdvancePushesAccumulatorFactorization` extends the old generated
transformation by that exact inverse occurrence and applies the Finding-9 push
factorization. This closes the only selected temporal branch that changes the
accumulator; control-only selected branches and foreign replay commutation
remain.

`DGamma.CP4DeletionFilterSuccess` closes the filter's generic `Maybe` layer
without replacing it by a parallel relation. `GenerationReplayReady` records
one exact `fireNamed` success for every retained head and no transition for a
deleted head. A structural induction constructs the same
`GenerationFilterResult` and proves an equation that the executable
`filterGenerationActions` call returned `Just`; selected-episode and suffix
specializations use the committed decidable deletion predicates directly. The
`DGamma.CP4DeletionSkeletonSuccess.deletionReplayReadyGivesTraceSkeleton`
then runs both exact filter-success specializations and constructs the complete
`DeletionTraceSkeleton` without a `Maybe`; its suffix readiness callback is
indexed by the selected filter's actual result and exact episode generation
scan. `DGamma.CP4DeletionReadiness` now proves the two requested structural
readiness inductions. `retainedReplayGivesGenerationReadiness` performs the
ordinal/environment/deletion decision recursion once; its selected-episode and
suffix specializations use the exact committed deletion predicates. The input
`GenerationRetainedReplay` is a record-saturated local interface: at each kept
original head it receives the exact complement-of-deletion proof and supplies
the exact `fireNamed` result at the current survivor; the induction itself
threads that endpoint into the tail. Carrying the complement is necessary for
the current-R plan's actor-exclusion proof—deleted heads deliberately have no
survivor transition.

This pins the remaining obligation-2 dependency precisely. The existing
`checkedRetained*AfterCurrentPlan` lemmas fire from
`MkSystemState originalAmbient (planTarget plan)`, whereas the dependent filter
carries its independently computed survivor. A new replay-boundary invariant
must identify or relate those sources through every step. In the suffix this is
the no-selected-episode deletion/commutation frame; in the selected segment it
also quotients the selected fiber lifecycle and uses generated-effect
transposition. Theorem 61 supplies the selected endpoint effect replay but not
this intermediate checked applicability. This is the still-partial Lemma-71
control/replay content, not an extra public premise and not permanently
residualized: it is also required by Theorem-73 sorting. No theorem alias or
runtime evaluator changed, and no escape hatch was introduced.

The first dedicated replay-boundary stage is now constructive.
`DGamma.CP4RuntimeBindings.transportApplyActionAcrossRuntimeSnapshot` is the
exhaustive eight-action keystone that transports evaluator success across exact
ambient/ordered-binding equality while deliberately ignoring proof-only
`UniqueKeys` terms; `CP4RuntimeBindingsChecks` pins the proof-distinct singleton
regression. `DGamma.CP4DeletionPlanRuntime.transportInactivePlanAcrossBindings`
proves the companion dependent induction: every Inactive/childless leaf plan
and actor-outside certificate reindexes across the same runtime binding list,
and its target retains exact ordered bindings, again without equating
uniqueness certificates.
`DGamma.CP4DeletionPlanComplete.currentRegisteredLeavesGiveCompletePlan` adds
its necessary converse: every current exact R generation appears in the plan;
`reachedDisciplinedBoundaryGivesCompleteDeletionPlan` constructs that saturated
plan from the public reached-trace premises. The older plan result stays
unchanged for existing consumers.
`DGamma.CP4DeletionCommuteCore` now proves the local ordered-binding algebra
needed by the next boundary step: deletion commutes with a distinct fresh head
insertion, a distinct replacement, and a second distinct deletion. The matching
registry lemmas deliberately project only `bindings`; no `UniqueKeys` proof
identity is requested. `DGamma.CP4DeletionPlanCommute` lifts each update through
an indexed `InactiveLeafDeletionPlan`. A retained O-Insert carries both owner and
parent exclusion, a retained replacement carries the evaluator's static-parent
fact, and a retained deletion cannot create children. At every recursive tail,
the two update orders are joined with `transportInactivePlanAcrossBindings`
rather than proof irrelevance. `removeExactActorFromInactivePlan` handles the
complementary deleted O-Remove case by deleting the actor's exact plan occurrence
and preserving the old target's complete ordered binding list. Arbitrary
actor-outside certificates are transported by all four folds. The boundary pass
also exposed that checked O-Retire is deliberately/idempotently permissive: it
has no `retired = False` guard, so an exact R leaf may legally be retired again.
`retireExactActorInInactivePlan` is the corresponding fifth internal fold; it
updates that Inactive leaf in place and proves that deleting the replacement
has the old target's exact ordered bindings. The preserving folds now return
`InactivePlanPreservingUpdateCommute`, which additionally proves exact plan-actor
list equality. Exact removal returns `InactivePlanRemovingUpdateCommute`, proving
the dropped actor is outside and every distinct old leaf remains; these are the
erased facts needed to preserve boundary completeness. This closes work order
1's local action/plan commutation layer; packaging these folds into the next
`NoEpisodeReplayBoundary` remains work order 2.

`DGamma.CP4DeletionNoEpisodeReplay` keeps the action index that the older
`TransitionResult` wrappers erased. `lifecycleRawAfterInactivePlan` and
`orchestrationRawAfterInactivePlan` fold the existing one-leaf frames through a
complete plan; `inactivePlanPreservesWellFormed` and raw Preservation turn the
result into the exact checked `fireNamed` package. `retainedSuffixHeadAfterCurrentPlan`
dispatches all eight actions, deriving lifecycle actor exclusion from the
complement of generation ownership and child-O-Insert parent exclusion from
registration discipline. `NoEpisodeReplayBoundary` then identifies an actual survivor with the plan
at the exact host-observable runtime snapshot and carries checked validity. The
boundary scaffold now owns `CompleteCurrentRegisteredPlanResult` directly, so a
deleted exact-generation head can recover plan membership without an unrelated
side invariant; `InactivePlanBindingsTransport` also preserves the plan actor
list while continuing to avoid equality of uniqueness proofs.
`DGamma.CP4DeletionBoundaryPlan` now performs the finite environment half of
boundary preservation: retained insert/replace/remove and exact deleted remove
all produce a new complete current-R plan, using explicit `Elem` transports for
`putCurrentGeneration`/`deleteCurrentGeneration` and the strong commutation
actor facts. No registry or proof-term equality is introduced.
`DGamma.CP4DeletionBoundaryDeleted.deletedSuffixHeadPreservesNoEpisodeBoundary`
closes the deleted-head half exhaustively. A registered O-Insert contradicts the
strict birth-before-boundary invariant; L-Begin contradicts the no-episode head;
L-Advance/Divert/Leave/Unload cannot fire from the exact Inactive plan leaf;
idempotent O-Retire updates that leaf, and O-Remove drops it. Both surviving
cases retain the exact old survivor snapshot and checked well-formedness.
The retained orchestration half is now exhaustive.
`retainedInsertPreservesNoEpisodeBoundary`,
`retainedRetirePreservesNoEpisodeBoundary`, and
`retainedRemovePreservesNoEpisodeBoundary` obtain exact plan/outside frames,
commute insert/replace/delete updates, transport checked evaluator results to the
proof-distinct survivor registry, and package the next complete boundary. Insert
threads its fresh non-R birth through `putCurrentGeneration`; remove threads
`deleteCurrentGeneration` and proves plan deletion cannot create a child.
`retainedOrchestrationPreservesNoEpisodeBoundary` dispatches the three cases.
Snapshot proofs project exact world/ordered-binding equality only.
`retainedSuffixHeadAtBoundary` uses the keystone transport to instantiate the
suffix retained-head interface without proof irrelevance. Deleted heads and all
retained heads now preserve the boundary. The new lifecycle layer proves exact
one-leaf result/control commutation separately for L-Begin, every L-Advance
outcome, L-Divert, L-Leave, and accumulator-driven L-Unload.
`lifecycleActionThroughInactivePlan` folds those comparisons through the whole
current-R deletion plan, transporting dependent tails by ordered-binding
equality and preserving complete plan actors. The shared boundary assembler
then replays the plan-side evaluator result on the proof-distinct survivor via
runtime snapshots. No state/proof-term equality is used.
`DGamma.CP4DeletionSuffixFold.noEpisodeSuffixReplayFold` closes the structural
whole-trace suffix induction: deleted heads leave the survivor fixed, retained
heads replay their exact checked action, and one simultaneous result carries the
generation scan, `GenerationReplayReady`, and final complete boundary.
`DGamma.CP4DeletionSelectedEffectCore` now establishes the first committed
selected-episode quotient stage. `SelectedEffectReplayBoundary` ties the actual
installed state to its concrete Theorem-61 accumulator model and requires the
survivor projection to equal the recovered ambient state and every ordered actor
table. `beginSelectedEffectReplayBoundary` derives the base from checked L-Begin
without equating registry proof terms, and
`selectedStepPreservesEffectReplayBoundary` consumes the proved selected
retirement/advance/divert/leave accumulator step to preserve the relation when
that selected lifecycle action is skipped.
`DGamma.CP4DeletionSelectedEffectForeign` closes the effect-only foreign
transposition at each intermediate boundary. It applies
`foreignAccumulatorStep`, transports the corrected Definition-60 map through
`partialEffectMapRespects`, proves the map is defined on the survivor's exact
ambient/ordered-table projection, and relates its output to target recovery.
`foreignEffectStepGivesNextBoundary` is the explicit join point for the pending
control proof: once an actual replay target is shown to project to that output,
the next accumulator boundary is immediate.
`DGamma.CP4DeletionSelectedBoundary` now packages the intermediate quotient
state with its complete current-R plan, accumulator effect boundary, exact
pointwise controls outside the selected fiber and current R generations, and
both source well-formedness facts. `beginSelectedEpisodeReplayBoundary` proves
this combined relation immediately after deleting L-Begin.
`skippedSelectedStepPreservesEpisodeBoundary` proves the generic structural
step: a skipped selected replacement leaves every foreign control lookup exact;
the rule-specific selected accumulator proof and plan transport are its only
inputs. Generation uniqueness remains supplied by the simultaneous scanner at
the rule-specific fold rather than duplicated inside this boundary record.
`DGamma.CP4DeletionGenerationStamped` adds the complementary scanner invariant
needed there: every environment key equals its generation's raw name.
Insertion, removal, all six unchanged-environment action forms, and whole-trace
preservation from `[]` are proved constructively. This lets the public
`selectedOutsideRegistered` premise exclude the selected fiber from an exact
current-R plan without assuming a raw-name global freshness discipline.
`DGamma.CP4DeletionSelectedOwn` now closes the full skipped-selected installed
step. It proves the checked update must be a parent-preserving replacement
(insert/delete contradict the source/target accumulator models), commutes that
replacement through the complete current-R plan, applies the selected recovery
step, and leaves the survivor fixed. The selected boundary has been honestly
strengthened to the ordered selected-exempt control skeleton that this step and
the pending foreign replay actually require: it compares the complete-plan
target to the survivor with exact binding names/order, full
`FiberControlRelated` evidence off the selected actor, and static
component/parent/retirement equality at the selected actor. Consequently exact
R absence and provider scan order are one field of the boundary rather than a
side certificate that could drift. Pointwise outside-control agreement is now
a proved projection. Selected replacement commutation transports the skeleton
without equating uniqueness certificates. `SelectedStableAccumulatorStep`
adds the missing retirement frame; the L-Advance builder and L-Divert/L-Leave
concrete models prove it per branch, and the exhaustive dispatcher eliminates
insert/retire/remove/begin/unload. Thus
`deletedSelectedInstalledHeadPreservesEpisodeBoundary` remains fully proved
under the stronger invariant. This is the approved ordered-table design-chain
addendum; public Lemma 72 is unchanged. The next obligation is the retained
foreign checked-control transport over this skeleton.
`DGamma.CP4DeletionSelectedForeignControlCore` now discharges the structural
Boolean part of that obligation: exact binding order preserves lookup/parent
presence; related component declarations preserve O-Insert provision guards;
related parents preserve O-Remove child guards; and full foreign control
relations preserve retired/Inactive observations and O-Retire edits. These are
ordered-binding theorems, not lookup-extensional shortcuts. `DGamma.CP4DeletionSelectedForeignOrchestration` now consumes those frames for
all three orchestration forms. O-Insert reconstructs the proof-relevant
`setFresh` result while comparing only runtime binding lists; O-Retire updates
both fully related foreign cells; O-Remove transports retired/Inactive/no-child
guards and deletes both ordered cells. Every branch constructs a checked
survivor transition, preserves the ordered skeleton, and uses
`actualTransitionEffectFrame` to prove its projection realizes the previously
transposed `foreignSurvivorOutput`, yielding the next selected effect boundary.
The remaining part of obligation 1 is lifecycle-specific: derive from the public
no-dependent-closing premise that the selected activation cannot change a
retained foreign target, then rebuild L-Begin/L-Advance/L-Divert/L-Leave/L-Unload.
The selected boundary now also retains the constructively true clean-Inactive
survivor cell explicitly. This approved internal strengthening rules out a
spurious selected provider or relying consumer and is preserved by every
foreign evaluator action; public Lemma 72 is unchanged.
`DGamma.CP4DeletionSelectedForeignLifecycleCore` now establishes the first
checked-control layer without pretending the trace argument is already solved.
Its ordered source relation combines full foreign controls, exact foreign table
bindings, and explicit selected-cell provider/reliance exclusions; its saturated
`ForeignLifecycleGuardFrame` is the exact consumer boundary for the pending
no-dependent-closing derivation. Rule-level control constructors cover L-Begin,
empty L-Finish, L-Raise, L-Divert, L-Leave, and L-Unload's Inactive reset.
Successful L-Advance uses `pushLocalUndoRuntimeRelated`.
`DGamma.CP4DeletionSelectedForeignLifecycleFrame` now performs the first honest
saturation step. `selectedProviderExcludedByNoDependent` reflects an observed
owned-table key through `ownedSound`, transports both immutable component
identities to a located consumer opening, constructs the exact
`PrecedenceEdge`, and eliminates it with the public
`NoDependentClosingEpisode`. The ordered fold then preserves every foreign
runtime table and relied-head observation, uses the explicit clean-Inactive
survivor selected cell for the sole exceptional head, and proves false reliance
transfers to the survivor. `foreignLifecycleGuardFrameFromNoDependent` assembles
the complete frame and owner control relation without equating registries or
erased certificates. Its `ForeignLifecyclePrecedenceAnchor` is deliberately a
trace-derived intermediate, not a new public Lemma-72 premise: deriving that
anchor for each retained occurrence (including the non-closing/open-at-end
case from quiescence and Lemma 70) remains before concrete checked-action
reconstruction. The supervisor approved exporting the previously private
`providerCandidate` used in the already-public source-cell constructor; this is
a visibility-only repair with no semantic change.
`DGamma.CP4DeletionSelectedForeignLifecycleGuards` closes the executable target
scan implied by that frame. `foreignLifecycleProviderInSame` preserves the
first active provider at every declared dependency across the complete ordered
registry (selected false/false, foreign candidates exact), and
`foreignLifecycleResolveViewSame` lifts it to the dependent `View` returned by
`resolveView`. The proof retains provider order and whole table bindings; it
does not weaken target equality to unordered membership. The visibility-only
exports of `providerCandidateExplicit` and `foreignProviderCandidateSame` expose
facts already present in the public source relation and do not change their
types or semantics. `DGamma.CP4DeletionSelectedForeignLifecycleReplayCore`
adds the common proof-indexed result for each pending concrete lifecycle branch
and proves that saturation projects back to the ordered selected-exempt
skeleton; this keeps raw/checked applicability and next-boundary controls in one
non-drifting package. `DGamma.CP4DeletionSelectedForeignLifecycleBegin` is the
first concrete consumer: successful plan-side L-Begin is reflected to an exact
unretired clean-Inactive shape, `foreignLifecycleResolveViewSame` transports its
whole dependent `View`, and the survivor executes a real raw and checked
L-Begin. Both sides install the same declared continuation and identity
accumulator, `beginLifecycleControlRelated` supplies the new control relation,
and ordered replacement plus raw Preservation produce the next replay package.
No ambient equality is assumed.

`DGamma.CP4DeletionSelectedForeignLifecycleDivert` is the second concrete
consumer. It inverts the exact plan-side L-Divert without fiber/proof equality,
uses the saturated ordered provider scan to preserve the stale-target Boolean,
transports the owner's remaining program, committed view, and extensional
accumulator relation to Unloading, executes a real survivor L-Divert, proves its
checked target by Preservation, and replaces both foreign control cells in the
ordered skeleton. Ambient states remain unrelated, as required by the already
transposed effect layer.

`DGamma.CP4DeletionSelectedForeignLifecycleLeave` reconstructs retained
L-Leave from the corresponding related Active controls. Exact ordered target
resolution preserves the false target-match guard, both owners enter related
clean Unloading controls, and raw Preservation reconstructs the checked
survivor step and next ordered skeleton without comparing ambient states.

`DGamma.CP4DeletionSelectedForeignLifecycleUnload` reconstructs retained
L-Unload. The saturated frame transfers the exact false reliance guard; the
survivor executes its own related accumulator on its actual normalized local
input; both owners reset to the common Inactive outcome; and Preservation
supplies the checked target. The proof deliberately does not equate accumulator
outputs across different ambient/table inputs—those observations belong to the
already-transposed effect boundary, while `FiberControlRelated` observes the
post-unload control outcome.

`DGamma.CP4DeletionSelectedForeignLifecycleAdvanceOutcome` and
`DGamma.CP4DeletionSelectedForeignLifecycleAdvance` close the rule-level
retained L-Advance reconstruction. The outcome layer factors the selected
accumulator boundary through its generated Definition-60 transformation,
transports repaired Equation-55 agreement through exact runtime observations,
and projects yielded full-state inverse equivalence back to
`LocalStateRuntimeRelated`. The concrete layer reconstructs empty L-Finish and
L-Divert, exact-error L-Raise, effectful L-Finish/L-Iter/landing-L-Divert, and
uses `pushLocalUndoRuntimeRelated` for every successful accumulator update.
Every constructor executes a real survivor raw step, proves its checked target
by Preservation, and updates the ordered selected-exempt controls.
`DGamma.CP4DeletionSelectedForeignLifecycleAdvanceDispatchCore` defines the
concrete evaluator outcome used at this join, and
`replayForeignAdvanceControlsFromOutcome` eliminates repaired Equation-55
agreement across every empty/failure/success branch. The exhaustive
`replayForeignLifecycleControlsFromProviderEvidence` dispatcher then saturates
either occurrence-local provider-frame reason and invokes the matching
L-Begin/L-Advance/L-Divert/L-Leave/L-Unload reconstruction. This is an internal
consumer of already-derived trace evidence, not an added public premise.

The precedence anchor now has both cases required by the paper rather than
pretending every retained lifecycle occurrence belongs to a closing foreign
episode. `DGamma.CP4DeletionSelectedForeignLifecycleAnchorEndpoint` derives
endpoint precedence acyclicity from the existing protocol-rank discipline and
then applies the proved Lemma 70 using exactly Lemma 72's public reached/quiet/
failure-free/totality premises. No support or acyclicity premise was added to
the public theorem. `DGamma.CP4DeletionSelectedForeignLifecycleAnchorOpen`
proves the open-at-quiescence exclusion: an Active supported owner obtains a
supported declared provider for each dependency; pairwise provision uniqueness
identifies any provider overlapping the selected declaration with the selected
name; Lemma 70 would then make the selected endpoint fiber Active, contradicting
its Inactive closing endpoint. The closed constructor retains the exact
consumer-opening edge used by `NoDependentClosingEpisode`, and the saturated
frame dispatches over both constructors.

`DGamma.CP4DeletionSelectedForeignLifecycleAnchorTrace` supplies the remaining
trace mechanics without proof equality: `OccursIn` is converted to an exact
`LocatedActionOccurrence`; installed evidence is split at that occurrence;
components are proved stable across every checked step with the evaluator's
`RegistryLocalUpdate` certificate and then across an arbitrary installed trace;
and `closedForeignLifecycleAnchorFromInstalledPrefix` constructs the closed
anchor from the located episode plus its opening-to-occurrence prefixes. The
open smart constructor rebuilds Lemma 70 internally from the public premises.
`DGamma.CP4DeletionSelectedForeignLifecycleAnchorClassify` now closes the first
half of that action-specific join. `LocatedTransitionOccurrence` retains the
exact transition dictionaries/equation; each retained lifecycle occurrence is
anchored after L-Begin and before L-Advance/L-Divert/L-Leave/L-Unload. The
forward `InstalledContinuation` classifier stops at the first L-Unload instead
of branching on the raw final installed bit. Consequently a later close/reopen
or O-Remove/O-Insert reuse is classified as a closing current activation, and
`closingOccurrenceGivesLocatedEpisode` reconstructs its exact global
`LocatedClosedEpisode` without a final-uninstalled premise.

The critical remaining-open alternative is no longer represented by an
endpoint-Inactive guess. `SelectedUnloadRelianceAnchor` is constructed from an
installed segment through the selected episode's own closing source and records
both the foreign owner's stable component and the exact selected L-Unload
`relied=False` head observation. This certificate is generation-safe because it
mentions the selected closing state, not a possibly reactivated or reused raw
endpoint. The provider-frame join is now constructive.
`DGamma.CP4DeletionSelectedForeignLifecycleAnchorReliance*` extracts the
foreign owner's intrinsically total committed view, uses current well-formedness
and pairwise provision uniqueness to identify any selected provider candidate
with that committed provider, carries the name through the complete installed
segment, and contradicts the exact selected L-Unload head observation. No final
raw selected cell is inspected. `ForeignLifecycleProviderFrameEvidence` then
joins this branch with both existing precedence constructors—the closed
Definition-65 edge and the Lemma-70 open endpoint—and
`foreignLifecycleGuardFrameFromEvidence` saturates the same ordered source
relation for either reason. The seven small reliance modules are an
elaboration-performance split only; no theorem premise or evaluator behavior
changed. Four previously private helper facts were made public solely so this
separate proof module can consume their unchanged types.
`DGamma.CP4DeletionRelationalBoundary` now defines the approved primary suffix
interface. It compares the actual survivor with the complete current-R plan
target using `EffectStateRelated` plus an ordered `FiberControlRelated`
skeleton (which projects to full `ControlEquivalent`), and
`exactBoundaryGivesRelational` proves the previous snapshot scaffold is its
special case even across distinct top-level uniqueness certificates. The
remaining selected stage must construct foreign retained checked transitions,
handle deleted R heads, close the L-Unload endpoint, and feed the parallel
relational suffix fold. The effect half of that close is now constructive:
`DGamma.CP4DeletionSelectedCloseEffect.selectedUnloadClosesEffectBoundary`
identifies the intermediate model handle with the exact handle consumed by
checked L-Unload, equates their recovered outputs, and composes the L-Unload
actual-effect frame to obtain original-post-close/survivor
`EffectStateRelated`. Control/reset-to-Inactive and plan packaging remain.
`DGamma.CP4DeletionPlanEffects` isolates the other effect-side join premise:
`EmptyTableInactivePlan` records the no-episode empty table at every exact R
leaf, and `emptyInactivePlanPreservesEffects` proves pointwise that iterated
leaf deletion preserves ambient state and every ordered actor table. The proof
composes the existing one-step O-Remove effect frame and never equates registry
or owned-table uniqueness certificates. That premise is now constructive:
`DGamma.CP4DeletionEmptyTableInvariant` performs a simultaneous checked-trace
induction with the proved Inactive invariant, showing O-Insert starts empty,
O-Retire retains bindings, foreign heads preserve lookup, and every R lifecycle
head is impossible without L-Begin. `DGamma.CP4DeletionPlanEmpty` then uses the
plan's outside projection as a constructive no-extra-leaf argument and derives
`EmptyTableInactivePlan` for every complete current-R plan. The reached theorem
`reachedCompletePlanHasEmptyTables` consumes exactly scanner/alignment/public
no-episode evidence.

The selected-boundary deleted-R orchestration layer is now constructive.
`DGamma.CP4DeletionSelectedDeletedPlan` adds the proof-relevant plan operations
that the exact suffix boundary did not need to expose: a fresh R O-Insert
prepends its canonical empty/Inactive/childless leaf, complete plans transport
across equal ordered runtime bindings, and the preserving/removing folds retain
their observable target equations. `DGamma.CP4DeletionSelectedDeletedCore`
uses the old and new `EmptyTableInactivePlan` witnesses to relate the original
before/after effect projections through their common plan target, transports the
unchanged selected accumulator on that relation, and keeps the survivor fixed.
It also re-derives next-boundary table emptiness from the public current-R
invariant rather than storing a new premise in `SelectedEpisodeReplayBoundary`.
`DGamma.CP4DeletionSelectedDeletedOrchestration` instantiates that core for all
three possible deleted orchestration heads: fresh O-Insert, legal idempotent
O-Retire, and exact O-Remove. Each canonical registry update is transported to
the evaluator's actual proof-distinct target through ambient/ordered-binding
observations; no `UniqueKeys` or registry equality is requested.
`deletedRegisteredOrchestrationHeadPreservesEpisodeBoundary` is the exhaustive
three-rule dispatcher. This changes no public Lemma-72 statement and does not
restructure either replay-boundary record.

`DGamma.CP4DeletionRelationalSuffixFold` now proves the parallel structural
suffix induction without weakening the ordered boundary. An exact scaffold from
the relational boundary reuses every committed current-R plan/head commutation.
Deleted R heads are fully discharged by composing the exact next-plan bridge
with the existing relation to the fixed survivor. Retained heads similarly reuse
the exact plan-side transition, then consume the explicit
`RelationalActionReplayer` interface; their returned effect/control relation is
composed with the exact next-plan bridge. The simultaneous result threads the
generation scan, executable `GenerationReplayReady`, live-name uniqueness, and
the final `RelationalNoEpisodeReplayBoundary`. This is a proved fold, not an
inhabitant of its still-open local operational-congruence input: Definition-60
outcome/effect stability and the ordered lifecycle constructors must now supply
that interface for every retained evaluator tag.

The first concrete relational-action layer is also complete.
`DGamma.CP4DeletionRelationalActionCore` proves exact ordered lookup, absence,
insert/replace/delete, O-Insert guards, child guards, and effect updates.
`DGamma.CP4DeletionRelationalLifecycleSources` combines the orthogonal exact
effect and ordered-control relations into a per-cell runtime relation and proves
provider order, target resolution, target matching, and reliance observations
are identical. `DGamma.CP4DeletionRelationalActionOrchestration` then constructs
real checked survivor O-Insert/O-Retire/O-Remove steps and composes their exact
effect/control outputs, including proof-distinct registry certificates. Several
previously proved private helpers were exported solely for this module split;
all types and implementations are unchanged. The remaining
`RelationalActionReplayer` debt is precisely L-Begin/L-Advance/L-Divert/L-Leave/
L-Unload. Endpoint control/withdrawal and `deletionTheorem` consequently remain
uninhabited. No public Lemma-72 statement or replay-boundary record changed, and
no escape hatch was introduced.

### Corollary 62: terminal recovery

`DGamma.CP4TerminalRecovery.terminalRecoveryTheoremProof` now inhabits the
immutable Corollary-62 alias. `appendLeftOccurrenceEmbedding` runs the proved
Theorem-61 simultaneous induction over the maximal installed body while keeping
the complete closed trace as its generator universe, so the public independence
premise needs no lossy subtrace conversion. `ClosingAccumulatorResult` extracts
the exact runtime handle consumed by checked L-Unload and reuses the exhaustive
actual-effect frame to relate its result to the concrete post-close projection
without function extensionality. The two `actualAccumulatorAt` equations identify
that handle with the temporal model's final handle; `appendOwnReplay` then appends
L-Unload as the selected actor's skipped replay step and composes the terminal
relation. `beginAccumulatorRecovery` is now publicly exported as a proved helper
so the closed-body replay starts at the exact episode opening projection. No
statement, runtime evaluator, or escape hatch changed.

`DGamma.CP4ResolutionCoherence.resolutionCoherenceTheoremProof` immediately
applies the previously proved `resolutionCoherenceFromTerminalRecovery`
packager, closing Theorem 64 on the unchanged public alias. Equation 59,
whole-episode resolution structure, terminal recovery, and dependent result
assembly are therefore all proved.

### Cold-build validation under Idris 2 v0.8.0

A one-process build from an empty `build/` may be killed while elaborating the
pre-existing 1,800-line `DGamma.CP4SupportSolution`: Idris retains the memory
used to compile its large dependencies in the same process. This is an
elaborator-resource issue, not a type error. For a genuinely clean archive,
use process isolation at that boundary:

```sh
idris2 --clean dgamma.ipkg
idris2 --build dgamma.ipkg || true   # populates dependency TTCs; may die there
idris2 --source-dir src --check src/DGamma/CP4SupportSolution.idr
idris2 --build dgamma.ipkg
```

The final command must report every package module. The CP4 Lemma-70 modules
then cold-check quickly. Validators must not copy TTCs from another worktree;
the isolated `--check` above consumes only artifacts produced inside the clean
archive. This recipe was exercised on commit `fe9764d`, followed by the 31/31
runtime aggregate and escape/totality scans.

For the expanded Step-3 tree (46 modules at that validation point), a new clean
archive reached the known
`CP4SupportSolution` boundary and the initial package process exited 137 as
expected. The isolated support-solution rebuild then exceeded the 20-minute
validation command budget, and a one-process warm package invocation likewise
exceeded ten minutes. This is recorded as a validation resource residual, not
silently called a clean pass. Targeted checks of `CP4ProgressProof`, every new
Progress dependency, and the then-current deletion-frame modules succeeded;
the current 60/60 source modules retain `%default total`, and anchored escape-hatch scans
remain empty. A combined runtime-runner compilation also exceeded five minutes,
so no fresh aggregate count is claimed for this milestone.

**Registered CP4 validation debt:** before the end-of-CP4 adversarial review,
split the roughly 1,800-line `CP4SupportSolution` into per-lemma modules while
preserving its public aliases, then repeat the clean archive recipe. Exit 137 is
the macOS OOM killer; cold builds must run without concurrent Chez processes.
Targeted per-module checks, totality, and escape scans are accepted for ongoing
Step-4 work, but do not discharge this final reproducibility debt. The same
clean run must explicitly rebuild `CP3StatementChecks`, `CP3VestigialChecks`,
and `CalculusChecks`, whose post-Finding-7 attempts timed out under shared load.

**Registered optional strengthening debt — paper Lemma 56 derivation:** the
accepted finite-host Theorem-73 premise `SameOrchestrationModuloGenerated`
bundles the generation bijection, `RegistrationCorrespondenceByGeneration`,
and `CurrentEndpointRenaming`; these are assumed rather than derived from bare
same-orchestration inputs. Theorem 73 must use this fixed, generation-aware
premise and is not gated on weakening it. Mechanizing paper Lemma 56 after
Theorem 73 would recover the paper's stronger input surface. Record this
finite-host deviation in the eventual errata/clarifications letter.

For the control-applicability milestone, deleting all eight new TTC/TTM pairs
and checking `CP4DeletionControlChecks` rebuilt the complete new dependency
chain (8 modules) in 2.30 seconds. The whole warm package invocation again
exceeded ten minutes, so it is not recorded as a package pass and does not
change the registered clean-build debt. The repository-wide scan now covers
68/68 `%default total` modules with no escape-hatch match.

For Finding #8, a forced rebuild of `CP3` plus
`CP4DeletionGenerationChecks` passed in 10.97 seconds and the executable
countermodel printed `True`. A lightweight exact copy of the full
`CP3StatementChecks` source (only the already-validated
`acceptedSupportLemma68Proof` import/application removed to avoid the registered
`CP4SupportSolution` elaboration boundary) rebuilt 10/10 modules, including all
repaired deletion projections. The tracked tree now scans 69/69
`%default total` modules with no escape hatch. This targeted validation does not
discharge the registered clean-package debt.

For Finding #9 and the first obligation-3 recovery modules, the mandatory
accumulator-dependent revalidation is recorded in Finding #9 above. After the
four recovery modules landed, the warm package build reports 88/88 total source
modules and the anchored escape-hatch scan remains empty. This is a current
whole-package typecheck, but it does not discharge the separately registered
cold archive / `CP4SupportSolution` split debt.

Finding #10 then strengthened the exact effect relation and all of its direct
consumers. The warm package invocation rebuilt and passed 93/93 modules,
including the three heavy check modules; the new/old order regression and all
Finding-7/9/vestigial/calculus runtime aggregates evaluate to the all-`True`
tuple recorded above. This is full consumer revalidation for the semantic
change, but still does not discharge the registered split/cold-archive debt.

After Finding #11 and constructive Theorem 61, a no-concurrent-Chez warm package
build passed all 99/99 modules. The run explicitly rebuilt
`CP3VestigialChecks`, all deletion/control modules, all Progress modules, and the
new selected/foreign/replay proof chain. `CP3StatementChecks` had separately
passed on the immediate no-concurrent retry documented in Finding #11, and
`CalculusChecks` had passed its targeted rebuild. This is current complete warm
validation; the registered `CP4SupportSolution` split plus cold archive build
remains outstanding.

After the two readiness inductions, Corollary 62, Theorem 64, and the first
no-selected-episode replay-boundary stage landed, a no-concurrent-Chez warm
package invocation passed all 103/103 modules. All 103 source modules retain
`%default total`; the anchored proof-escape scan is empty (the sole broad
`postulate` text match is a documentation sentence saying none is used). This
is a current warm typecheck only and does not discharge the registered
`CP4SupportSolution` split/cold-archive validation debt.

After the runtime-snapshot repair and the first whole-suffix foundations, a
warm package invocation passed all 107/107 modules. All 107 source modules have
`%default total`, and the anchored executable escape-hatch scan is empty.
Targeted forced checks passed `CP4RuntimeBindings`, its proof-distinct regression,
`CP4DeletionPlanRuntime`, `CP4DeletionPlanComplete`, and the adapted
`CP4DeletionNoEpisodeReplay`. This remains warm validation; it does not
supersede the registered split/no-concurrent-Chez cold-archive debt.

After the local action/plan commutation layer, targeted forced checks passed both
new modules and the strengthened exported childlessness frames. A warm package
build passed all 109/109 modules; all 109 retain `%default total`, and the
anchored executable escape-hatch scan is empty. The inherited untracked `paper/`
and `review-cp3-round10.md` inputs were not modified. This is still warm
validation and leaves the registered cold-archive debt unchanged.

After the selected-episode effect quotient, stamp-coherence invariant,
relational suffix boundary, checked-L-Unload effect join, and empty-plan effect
frame landed, a no-concurrent warm package invocation passed all 128/128 source
modules. All 128 retain `%default total`; the anchored escape-hatch scan is
empty. The inherited untracked `paper/` and `review-cp3-round10.md` inputs remain
untouched. This is again warm validation only and does not discharge the
registered `CP4SupportSolution` split/no-concurrent-Chez cold-archive debt.

After Finding #12 and the explicit selected-survivor clean-Inactive boundary
certificate, a full warm package invocation rebuilt and passed all 131/131
modules. This run included the three heavy check modules and every Eq-53
consumer. The proof-distinct accumulator regression and concrete control
witness check independently. After the retained-foreign lifecycle source/control
module was added, the warm package passed all 132/132 modules; all 132 retain
`%default total` and the anchored escape-hatch scan is empty. This remains warm
validation and leaves the registered split/no-concurrent-Chez cold-archive debt
unchanged.

After the action-specific retained-lifecycle temporal classifier and
selected-L-Unload reliance anchor landed, the first warm package attempt was
killed with the known exit-137 resource failure. An immediate retry with no
other Chez/Idris process rebuilt the heavy support and statement-check chain and
passed all 141/141 modules. All 141 retain `%default total`; the anchored
executable escape-hatch scan is empty. This is warm validation only and does not
discharge the mandatory `CP4SupportSolution` split/no-concurrent-Chez cold
archive build.

After concrete retained L-Divert reconstruction, a warm package invocation
passed all 142/142 modules, including the three heavy check modules. All 142
retain `%default total` and the anchored escape-hatch scan remains empty. This
again leaves the split/cold-archive validation debt unchanged.

After the stays-installed provider exclusion and the unified
Lemma-70/reliance frame join, a warm package invocation passed all 150/150
modules. The new modules and their exported join were also checked directly.
After retained L-Leave reconstruction, the warm package passed all 151/151
modules; after retained L-Unload reconstruction it passed all 152/152 modules.
After Finding #13 and retained L-Advance outcome/control reconstruction, the
warm package passed all 155/155 modules, including the repaired independence
countermodel and the three heavy check modules. After the split outcome and
five-rule provider-evidence dispatchers landed, a warm package build passed all
158/158 modules. After the no-episode empty-table induction and its plan bridge,
the warm package passed all 160/160 modules; the anchored executable
escape-hatch scan remained empty. The builds reused existing heavy-check
artifacts, so these remain warm passes
and leave the mandatory split/no-concurrent-Chez cold-archive validation debt
unchanged.

The deleted-R selected-boundary milestone adds three small modules plus one
exhaustive dispatcher. Targeted checks of the plan, core, orchestration, and
dispatch modules passed under Idris 2 v0.8.0. With no concurrent Chez process,
a warm package invocation passed the current 164/164 module list. This does not
discharge the mandatory `CP4SupportSolution` split/no-concurrent-Chez
cold-archive debt.

The relational suffix/action milestone adds four modules total (the structural
fold plus ordered action core, lifecycle-source observations, and concrete
orchestration replay). Targeted checks of all four passed, and the warm package
build passed the current 168/168 module list, including rebuilt selected
lifecycle/dispatch consumers after visibility-only exports. This remains warm
validation and does not discharge the registered cold-build debt.

### Lemma-72 relational replay and close milestone

The retained-action interface is now inhabited for all eight actions. The five
lifecycle cases execute concrete survivor `L-Begin`, every repaired
`L-Advance` outcome, `L-Divert`, `L-Leave`, and accumulator-driven `L-Unload`,
and package both exact effect relations and ordered controls. Global
`TraceIndependent` restricts constructively along occurrence embeddings.

The selected quotient now has checked opening, retained selected O-Retire,
retained foreign orchestration, and full retained foreign lifecycle packages.
The lifecycle join derives foreign tables from located ordered membership,
transports repaired Advance outcomes at projected effect sources, and composes
actual effect frames with the transposed accumulator output. Checked selected
L-Unload now produces `PostCloseSelectedBoundary`, deliberately retaining the
selected-static relation for failed closes. `CP4DeletionEndpoint` proves generic
final effect/control/withdrawal assembly from a relational suffix boundary plus
the remaining trace-derived current-generation retirement invariant. The warm
package build passed all 188 listed modules. No escape hatch was introduced.

### Lemma-72 selected structural fold checkpoint (shift 32)

The selected quotient now has a checked simultaneous structural induction. It
threads the generation scan, uniqueness/stamping, current-R Inactive and empty
invariants, executable filter readiness, the exact selected accumulator/control
boundary, and occurrence identity. A concrete local dispatcher covers deleted
selected lifecycle, deleted-R orchestration, selected O-Retire, retained foreign
orchestration, and all retained foreign lifecycle rules. Registration discipline
is recovered at the exact occurrence in the immutable global trace, avoiding an
invalid attempt to shorten the future-sensitive O-Insert premise.

`selectedClosedEpisodeFold` composes the checked opening boundary, the installed
interior fold, and selected L-Unload into `PostCloseSelectedBoundary`. Shift 33
has now discharged its former internal anchor input from the public premises:
closing crossing activations use committed-provider persistence and open-through-
close activations use the selected L-Unload reliance guard. Exact interior
prefix/decomposition indices ensure the temporal occurrence is not confused with
a duplicate transition. `selectedClosedEpisodeFoldFromPremises` checks the full
dispatcher/fold composition. Shift 34 adds the first checked post-close
discharge layer: `selectedOrderedAbsentGivesOrdered` upgrades the selected
quotient after selected O-Remove, while
`selectedOrderedCleanInactiveGivesOrdered` upgrades a surviving selected cell
when both endpoints are `Inactive Nothing`. Shift 35 now proves the effect half
of every retained post-close action (`postCloseOrchestrationEffects` and
`postCloseLifecycleEffects`) without upgrading selected control prematurely.
It also checks `retainedForeignPostCloseOrchestration`, including exact current-R
plan commutation, all three foreign orchestration constructors, survivor replay,
selected-static control threading, selected Inactive preservation, and all
current-R Inactive/empty-plan invariants. Shift 36 closes the remaining local
prefix cases. `retainedSelectedPostCloseRetire` applies retirement to both
selected-static cells and reuses the common post-close packager.
`retainedForeignPostCloseLifecycle` derives direct provider exclusion from the
plan-side selected Inactive witness, derives L-Advance outcome agreement from a
singleton checked stage plus related effects, replays all lifecycle rules, and
threads the full post-close invariant. Shift 37 completes the structural post-close fold: selected O-Remove upgrades
through absence, selected L-Begin upgrades through its checked clean source,
and an unremoved selected cell upgrades at the no-failure endpoint. Deleted-R,
foreign orchestration, and all foreign lifecycle heads recurse through the same
scanner/readiness invariant.

For endpoint withdrawal, `currentGenerationAtScanStart` is checked: a generation
older than the current ordinal that remains current at a scanned suffix endpoint
was already current at the suffix source. This rules out confusing an
occurrence-local O-Retire with a later raw-name reissue. Shift 34 also checks
`retiredInactiveCurrentPersists`: once that exact generation retires while
Inactive, retirement is monotone while it remains current under
`NoRegisteredEpisode`; the proof explicitly eliminates reissue, removal, and
all impossible Inactive lifecycle heads. `CP4DeletionWithdrawalJoin` now splits
the exact center scanner at every generated birth, locates its promised later
O-Retire, preserves exact-generation retirement through the center and suffix,
and constructs `CurrentRegisteredWithdrawable` without confusing a later raw-
name reissue.

## Status

### R172 research checkpoint (supersedes the historical Shift-37 frontier below)

**Fully proved this shift:** `CP5ConfluenceCanonicalSortSpike.supportOrderingSpike`
at `c99145c`, unchanged signature. Its erased lookup/rank observation capital
passed the designated probe; total executable insertion sort simultaneously
constructs its output, nondecreasing rank certificate, uniqueness and both
membership directions. Authentic protocol path ranks yield `BeforeIn`, then all
four `LinearizesSupport` fields. Concrete nonmonotone/deduplicating and equal-rank
reductions check at `9a70ffd`. No new hole, postulate, totality escape, `with`,
production change, frozen deletion-theorem call or scoped-to-raw cast.

**Partial overall / merely stated:** Theorem 73 remains unproved, with six
research holes (CanonicalSort 1 / CrossTrace 4 / DeletionChain 0 / LocalDiamond 0 /
RenamingComposition 1). Scoped DeletionChain was already closed at R171; this
does not fix the CP3 missing hypothesis at the frozen surface (satisfiability under uniqueness unverified). Exact canonical accounting,
shared original/reduced order, R16 fixture drift, R129 integration and copied
legacy `with` cleanup remain explicit debts, not hidden by the hole count.

**O14 milestone validation (ratified at `b590789`):** one fresh check for every retained declaration/body;
final dependent spikes pass and seeded package retains 207/207 modules. No wider
suite or clean rebuild claimed. Its then-next O17 **probe-first** status is superseded
by the continuation below; O19 body and O21
withdrawal lanes remain barred/parked. Full attempts, boundaries and types are in
`research-tests/O6-R172-NEXT-PHASE-RECON.md` and
`research-tests/O6-R172-GRIND-SHIFT-AUDIT.md`; current debt register is in
`THM73-PLAN.md`. Independent reviewer acceptance remains a separate gate.

### R172 O17 continuation status (supersedes O14-only next-target text)

**Fully proved capital:** N1–N42 (`1e8105e`) carry one exact reached replay
state, derive an actual distinct-root insertion diamond/suffix swap and a
one-position root-occurrence decrease, and transport the same support list
through full no-withdrawal control equivalence. They do not implement the full
block selector or its decreasing measure.

**Checked semantic frontier:** `R172O17OpenParentRootReuseCandidate` (`a069cbc`,
whitespace correction `775bd22`) has all OLD-surface O17 inputs (not the R173 uniqueness premise): full replay
bundle (including generated-monoid independence and iterator-yield stability),
closing-free shape and actual O14 order, proved to be [0]. The eight-step trace
yields/removes child 1 and reissues it as a root while parent 0 remains open.
Its source is not root-first; the immediate child-removal/root-insertion pair
admits no local diamond (`r172ReuseRemoveRootDiamondImpossible`).
**This is not a proved global sorting impossibility or a paper counterexample.**
A same-name birth-order invariant through every finite adjacent derivation and
the resulting global placement contradiction, or an alternative actual sorter,
remain unproved. R172 changed no premise; R173 subsequently implemented the owner-selected
global uniqueness hypothesis and its rejection fixture. This is necessity
evidence for that hypothesis, not a paper or implementation bug.

**Partial / merely stated:** O17 body remains 0/3 and its hole remains. Theorem
73 still has six research holes; all accounting, original/reduced-order,
R16/R129, regression and frozen raw-premise debts remain. N42's full-control
transport does not undo the permanent R143 arbitrary-deletion counterexample.

**Validation / escapes:** 133 new top-level declarations in 135 source commits
this shift; 166 serial compiler invocations, 157 diagnostic-clean passes and
9 charged corrected failures. The C45 external 120-second timeout is included;
its deeply indexed match was replaced with an explicit generic occurrence
eliminator and passed 2/3. The final source-whitespace fix was freshly checked.
Eight continuation gate checks passed; unchanged DeletionChain/LocalDiamond
cached checks rely on their genuine Unit A fresh evidence. Production and
package remain frozen, 207/207 TTC seeds retained, no concurrent compiler, new
hole, postulate, unsafe totality escape, `let`, `with`, residual as-pattern,
frozen deletion call or scoped-to-raw cast. Full audit/diagnostics are in
`research-tests/O6-R172-GRIND-SHIFT-AUDIT.md`.

**Next:** request the O17 semantic-frontier/stop gate. With >90 minutes until
the absolute deadline, request separate target-#3 canonical support matching
probe-first authorization; do not self-start it. A global O17 refutation is
not silently substituted for the original sorting obligation.

### Final R172 status — global prefix stopped; future premise revision selected

**Fully proved additional capital:** every hypothetical unchanged O17 output
places its actually preserved root-1 birth before each accounted child-1 birth
(`r172ReuseConclusionRootBeforeChild`, `74d0290`). The child's actual checked
transition is fresh; an occupying fiber at that source gives Void (G25–G27,
`2f6a494`). Root-classified occurrences transport backward through the actual
external-input relation, and the original concrete removal is internal
(G28–G30, `a938488`).

**Partial / stated:** G31 whole-source external-root-removal exclusion exhausted
3/3 and was fully reverted. Root occupancy persistence to the child source and
final negation remain unproved. `R172ReuseGlobalSortingRefutation` is an exact
erased **Type only**, without an inhabitant. The O17 selector body remained
0/3. Six research holes remain; O14 alone closed this shift.

**Owner-selected next path:** premise revision with the strong global condition
“each raw name is inserted at most once in the whole trace,” not conclusion
revision. The owner relates this to globally fresh Cordis instance names; the
reuse candidate was designated in R172 and certified as its negative fixture
in R173. No runtime/production surface changed. Full refutation remains
secondary bounded necessity evidence, not an erratum claim or a gate.
R174 recon must test whether insertion uniqueness resolves the frozen CP3 raw
premise and whether O19/O21 share the reuse cause; these are not yet proved
repairs. Matching probe-first is pre-authorized for R173 only. Existing debts
remain OPEN/parked; no fourth/renamed G31 attempt followed the stop.

**Final validation / escape catalogue:** 212 serialized checks, 196 clean passes
and 16 charged failures (13 corrected, three G31 stop failures). Restored
candidate/lifetime modules freshly pass; all five spikes and seeded package
pass, 207/207 retained. Original ratified audit sections are byte-preserved.
No new hole, postulate, unsafe totality escape, `let`/`with`, residual as-pattern,
frozen deletion call or scoped-to-raw cast. The G31 coverage failures are fully
catalogued, including the complete 170,224-byte raw diagnostic's hash and a
whitespace-normalized checked-in transcript. No unproved theorem is claimed.

### Historical Shift-37 status (preserved as that revision's record)

**Fully proved:** all previously listed approved Section 3 results; Preservation
(Theorem 59); Theorems 61, 63, and 64; Corollary 62; finite-specialized Lemmas
68 and 70; repaired finite Progress/Theorem 66; and **Lemma 72**.
`DGamma.CP4DeletionTheorem.deletionTheoremProof` inhabits the current repaired
public `deletionTheorem` type. Its proof composes the selected center fold, complete
post-close structural fold, exact retirement/scanner join, executable dependent
filter witnesses, and `CP4DeletionEndpoint` effect/control/withdrawal packaging.

**Partial:** Lemma 71 remains a projection-level mechanization rather than a
standalone paper-shaped theorem. Lemmas 54–57 have many proved rule/frame
analogues but are not individually complete. Theorem 73 remains statement and
regression work only; no constructive sorting/confluence proof was started in
Shift 37.

**Merely stated:** Lemma 35, Theorems 40/42, and `confluenceTheorem`. These are
escape-hatch-free proposition types. `deletionTheorem` is no longer merely
stated: its checked inhabitant is exported downstream.

**Validation:** targeted checks passed for the selected fold, post-close fold,
withdrawal join, endpoint, and theorem roots. Every `src/**/*.idr` module has
`%default total`; scans found no `believe_me`, `assert_total`, postulate,
`%default partial`, partial declaration, or metavariable hole. The warm package
build passed all 207/207 modules. The older documented `TODO(proof)` comments
for Unified Lemmas 35/40/42 and Theorem 73 remain outside Lemma-72 scope.

**Deviations:** Definition 32 finite approximations; finite static-list
continuations; finite tagged/catalogued explicit registration rather than a
recursive nested yield (including the documented one-source-head/many-child-name
over-approximation); trace-anchored full-effect generated monoids; exact full-
effect equality; and explicit `AlignedTransitions` dictionary alignment.

**Next:** stop at the Lemma-72 boundary. The supervisor will run the required
fresh-context adversarial review separately. Do not begin Theorem 73 or split
the registered validation debt in this shift.


### R173 research status (2026-09-06; supersedes the old CP5 next-step note)

Production remains frozen. Strong whole-trace raw insertion uniqueness, its
negative reuse/positive distinct-name fixtures, and transport through actual
deletion/adjacent derivations are proved. O17 and R8/R16 now expose the revised
conditional hypotheses. The actual worklist produces correlated blocks/ranges
and adjacent grouping candidates with fixed-order membership; A/O parent
exclusion and activation output installation are proved. No sorting theorem is
claimed: C58 exhausted 3/3 at its final insertion-owner scalar projection and
was removed, archived and restoration-checked. O17 body remains 0/3; the research
census remains 6 (1/4/0/0/1). No escapes or new holes were added.

The supervisor ratified the committed stop, confirmed internal implementation
cursors/helpers remain private, and moved Unit D to R174. Fresh seeded package
build passed 207/207 at 18:49 UTC; this is not from-scratch validation. Exact
remaining producers, C58 sources, validation/frozen hashes, compiler incident,
895-MiB ordinal TTC performance debt, cached disposable-probe artifacts, and the
retained EOF-whitespace warning are catalogued in
`research-tests/O6-R173-GRIND-SHIFT-AUDIT.md`. Continue only at the approved R174
boundary; no fourth C58 attempt or unconditional Theorem-73 claim is inferred.


## Status — R174 (2026-09-06, supersedes R173 continuation)

**Fully proved in research:** the C58 observed-value cure and actual local
A/Insert sealed result; reached closing-free shape from unchanged O17 source
shape/bundle via actual finite adjacent replay; simultaneous reached worklist
reinspection with uniqueness/ranges/order; positive orientation classification,
actual A/A distinctness, local moved-right ordinal decrease, and the actual
worklist selector's non-Begin provenance. The executable eight-step distinct-
birth provision example, strong uniqueness, sorted-prefix guard rejection,
and genuine nonempty-key registration protocol also typecheck. These do not
supply the example's RegistrationDiscipline or full O17 telescope.

**Partial:** O17. Root placement is owner-paused (literal paper clause versus
current declared-provision guard), not refuted on full premises. Early
applicability, every selected sealed swap, completed-prefix/BlockBefore
preservation, global decreasing measure and registration-accounting remain
open. The local ordinal decrease is NOT that global measure; reinspection is
NOT readiness preservation. O17 body remains 0/3. The actual selected activation
is a continuation rather than Begin; this does not by itself prove it can move
earlier. Unit D classifies downstream walls without implementing them.

**Merely stated/open:** the six inherited holes, 1/4/0/0/1. No new escape hatch,
hole, partial function, postulate, unsafe cast, with-block or local alias is
introduced. Production is unchanged; O19/O21 proof bodies and the frozen CP3
surface are untouched. Global uniqueness is not silently threaded through
unchanged downstream telescopes. CP3 raw-premise satisfiability is unverified.

**Validation and checking debt:** last fresh CanonicalSort proof check S39-1,
23:37:55–23:38:50 UTC; seeded production package, R8 and conditional R16 pass.
All 39 S units are committed; S3 used 2/3, S26 used 3/3, others 1/3. Q9 exhausted
3/3 at normalization cost, was reverted and baseline-checked, with no fourth
attempt. Five engineering interrupts are honestly NO COMPILER VERDICT. The
~938-MB ordinal TTC debt is not cured by P6's separate opacity success. Only the
two expressly authorized stale R173 probe TTC/TTM files were removed.

**Next:** owner decides root canonical-form versus faithful store-ownership
semantics; meanwhile build early applicability from the actual selected-pair
provenance and prove global measure/accounting before the O17 body. Full
per-unit sources, diagnostics, decisions and remaining obligations are in
`research-tests/O6-R174-GRIND-SHIFT-AUDIT.md`, the permanent compiler ledger and
`research-tests/O6-R174-A8-CAUSE-SHARING-RECON.md`. No unconditional Theorem 73 or
independent reviewer approval is claimed by this milestone.

## Status — R177 (2026-09-07)

**Proved, research only:** all twelve bounded rank micro-units cure the opaque
computed-rank wall and prove actual accepted-worklist decrease for the SAME
provided descending checked pair. B2–B122 authenticate accepted current scanner
entries and parent-activation generations as genuine ORIGINAL located births
with exact stamps. Registry/current lookup domains are connected in both
directions. For an accepted retained generated event, the sealed static-coherence
boundaries construct the actual opposite endpoint fiber, exact component,
dependency and provision specifications, both exact CURRENT parent stamps, and
parent phi/phi^-1 coherence. Original insertion uniqueness is used only after
both births have been authenticated. Single-state computed parent closure and
exact birth identity avoid any need for a withdrawal/NoParentUnload theorem.

**Partial/open:** generated-source retained-event coverage (and root static
coverage), retirement agreement, both O18 cross-endpoint support-truth
implications and the support-order body. All six inherited research body holes
remain. O17 still needs pair location/discovery and orientation applicability;
root placement and the O17 body remain owner-paused. O19 and O21 bodies remain
unchanged, with no O21 withdrawal or heterogeneous endpoint composition proof.
No O20 consumption/enumeration equality was used as support truth.

**A9 finding and scope:** frozen CP3 skips non-root ORetire in external
orchestration matching and matches generated births, not their retired flags.
The P1 proof plus P2-4 executable checked pair establish actual quiescent states
with an Active parent on both sides and differing child support. The exact full
accepted correspondence and BOTH IndependentCanonicalSchedule capitals for that
quiet pair are not constructed; do not call it a complete O18 counterexample.
The supervisor's proposed cure is a research-side explicit
GeneratedOrchestrationMatched hypothesis modulo the accepted generation
bijection, threaded like uniqueness, pending owner override. Production and
existing theorem premises remain frozen; no such hypothesis was silently added.

**Proof/engineering exceptions:** no new proof hole, postulate, believe_me,
assert_total, partial function, with block, inferred local view or let alias was
introduced in retained R177 Idris additions. The disposable P2 unit reached 3/3,
was rolled back and stop-audited at b1735d2. The supervisor explicitly authorized
ONE P2-4 mechanical namespace repair, both record projections only. That single
--exec invocation exited 0 and executed the actual proof-carrying producer; it
suppressed the usual Building marker. Its unchanged conservative wrapper JSON
therefore retains fresh:false/passed:false, separately qualified by exact source
substitution and source/TTC timestamp evidence. It is not relabelled as an
ordinary fresh --check PASS. All probe .idr sources were removed, snapshots
preserved, and no build seed was deleted. B99 removed an accidental duplicated
unused B98 argument, rather than preserving that unnecessary premise.

**Next:** resolve source event/root coverage and the A9 owner decision; then
prove both genuine support-truth implications, fill O18 only if valid, immediately
re-census (expected five = 1/3/0/0/1), and gate. Neither that closure nor the
five-hole gate occurred during this shift. Detailed per-invocation compiler,
stop, frozen-hash and final validation evidence is in the R177 research audits.

R177 final validation: fresh CanonicalSort, UniqueCapital/CrossTrace,
R8FullPipeline and generated-static-coherence checks PASS; seeded package build
PASS with 207/207 TTC seeds preserved. Final clean frozen audit/census PASS,
six holes unchanged, production/LocalDiamond/O17/O21 boundaries preserved. The
broad R11 diagnostic suite was not rerun. Complete 156-invocation evidence and
qualified P2-4 result are committed; no extra post-validation coverage unit ran.

## Status — R178 (2026-09-07)

**Fully proved, research only:** explicit authentic ordered generated
retirement/removal matching (A9), its structural negative and nonempty identity
fixtures; complete supported generated retained-event and root coverage; actual
current-birth/static parent/component coherence; both support-relative retirement
transport directions; both support-truth implications by actual support-edge rank
induction; **O18 `canonicalSupportOrdersMatchSpike` closed**. Five holes remain,
CanonicalSort/CrossTrace/LocalDiamond/DeletionChain/RenamingComposition = 1/3/0/0/1.
The R177 TWO-CAPITAL GAP remains: its negative pair is not two complete canonical
capitals, and no unconditional Theorem73 result is claimed.

**Checked replacement specification / partial integration:** A8's
AvailabilityAwareCanonicalInputPlacement uses earliest interval-compatible root
cuts, actual source-state declaration occupancy, exact external-input order,
root-own lifecycle order, and the retained child-generation clause. Its executable
cut test rejects crossing a future same-key reservation in the crossed interval;
retirement/inactivity do not release declarations. The R174 scalar shape proves
cuts0..4 rejected and cut5 accepted after removal1, with the earlier lifecycle
and later root actually observed. It is NOT a full placement-record/earliest-root
packet producer. C9's direct located-root fixture remains parked at2/3 after two
no-verdict cost interruptions; exact failed sources and restoration are audited.

**Owner decisions outstanding:** A8 and A9 are supervisor decisions under
delegation, owner override pending. The strict clauses are in frozen CP3's
CanonicalInputPlacement, owned by frozen CanonicalSchedule. Integration requires
an owner choice: fork/migrate the research canonical tower (24 direct research
type references across7 research/test files, plus dependent projections), or
unfreeze production placement and revisit production statement/proof consumers.
Neither was chosen, and no coercion into the old strict record was added.

**Escapes and debt:** no believe_me, assert_total, postulate, partiality or new
hole. A16's three rejected quiet-normalization attempts were fully reverted and
ratified; a genuinely independent structural A9 exclusion was proved instead.
C9's interrupted declaration was fully reverted and restoration checked. No
O17/O19/O21 withdrawal/body or LocalDiamond change is hidden by this milestone.
Next is owner-directed integration/permutation/convergence work, not a fourth
A16 or third C9 retry. Full ledger, clause map and validation evidence are in the
R178 research audit and evidence directory.

Final R178 validation: seeded production package **207/207** and **30 fresh
positives +10 exact-diagnostic negatives** passed. The optional aggregate legacy
R11 suite is **incomplete**, not failed as a proof: after5 spikes and39 positives,
unchanged R23 ran12m52s without a verdict; the supervisor authorized termination
at09:00:27. Its partial log and explicit cost-stop reconciliation are committed.
No broad-suite success is claimed. The protected-source/five-hole audit passed;
LocalDiamond's125,368,223-byte seed is unchanged. Exact evidence is in the R178
ledger/archive; Markdown diagnostic presentation alone is right-trimmed.

## Status — R179 (2026-09-07)

**Fully proved, research only:** both accepted original endpoint current-birth
identity producers in `CP5O21EndpointIdentitySpike`, strict-later-birth exclusion,
and an erased bilateral producer consuming the unchanged O21 original-capital
and uniqueness telescope. Currentness/authentic original birth comes FIRST,
then uniqueness; no raw-name-only identity inference. A9 is threaded but is not
needed for this stronger one-trace subcase. Positive conditional consumption and
an exact wrong-original-trace rejection were checked.

**Partial:** O19 now has a certified empty-origin four-step provider/dependent-
consumer prefix proving early consumer Begin=Nothing; an independent explicit
observed-state fixture proves checked provider Begin/Iter/Finish and cut/finished
WF. The current AdjacentActorSwapSafety, fifteen-field bundle and real blocks
are NOT inhabited. A3's suffix builder is conditional, not executed evidence;
A13's concrete consumer target projection remains unproved. No revised safety
surface, full counterexample, positive revised-safety fixture or O19 body exists.

**Merely sized/stated:** one disposable type-only O20 probe checked the exact four
fixed-bijection bridge clauses; no bridge producer or O20 body. General Theorem73
and all five inherited body holes remain open (1/3/0/0/1). O17/root/A8 integration
and O21 withdrawal branches stayed outside scope.

**Stops/escapes:** no new hole, postulate, unsafe proof, partiality, with block or
local let in retained additions. A4 stopped1/3 on a rejected observation; A6
was cost-interrupted1/3 without verdict (~52GiB) and ratified. A11 and A13 each
exhausted3/3, fully reverted and freshly restored; A14 blocked0 attempts. The
supervisor separately authorized A12/A13/A14 as distinct prerequisites, not a
reset of A11. Detailed exact transcripts and snapshots are committed in the R179
compiler archive. No production source/package, old theorem signature/body or
LocalDiamond declaration changed.

**Next:** expose the ACTUAL provider Finish fiber/table projections before
transporting `restrictOwnedPreservingOrderBindings` into providerOf/targetFiber;
then checked consumer Begin/Finish, protocol, full bundle and actual 3x2 blocks.
Only a committed full old-safety negative can unlock surface revision. O21's
retired/clean/empty-table/childless/unsupported/discarded/current withdrawal
clauses still need independent proofs; identity is not their replacement.

R179 final validation: four fresh positive target checks, the exact intended
wrong-original-trace rejection, and seeded package build207/207 PASS. All37
invocations are accounted (27 ordinary successes including2 package builds and
the type-only probe, 2 intended-negative successes, 7 rejected proof attempts,
1 interrupted/no-verdict attempt). Existing five spike files/production and
LocalDiamond seed remain exact; no legacy R11 rerun, cold build or cache deletion.

### R179 D/E continuation after the 10:10 gate

The supervisor ratified the first prefix but deferred handoff and explicitly
budgeted D12/E8 additional units. **D fully proves the fourth fixed-bijection
bridge clause on originally supported generated children**: exact left origin,
actual opposite canonical birth at renamed child AND parent, same component,
accepted generation triangle, and right canonical birth-stamp uniqueness.
The companion is `CP5O20SupportedBirthBridgeSpike`; A9 is actually used to derive
opposite support and its own canonical child placement. No opposite birth,
lookup, support or triangle oracle was added. Unsupported-child cases and all
ambient/table/control convergence remain open; no O20 body.

**E fully proves actual rank-descent selection output and alignment**, in
`CP5RankedTraceSelectionSpike`, parameterized by one deterministic action-rank
observation. Exact adjacent checked steps/prefix/suffix/ranks are preserved;
barriers are not moved or crossed. The concrete four-action certified trace
selects the Begin0/Begin1 pair at2/3, ranks1/0; the default branch is excluded.
These total selectors are erased proof producers, not new runtime plugin APIs.
The existing private worklist rank observer/body remains unchanged; orientation
applicability, sealed result integration and adequate progress completeness
remain unproved. Nothing is not evidence of canonicality.

D12/12 passed first attempt. E1–E6 passed first attempt; E7 passed2/3 after a
direct producer import; E8 passed3/3 after explicit observation/result typing
and direct rank-computation imports. All attempts are charged in the ledger.
No new hole, unsafe proof, local let/with, partiality, old spike change, root
placement or withdrawal proof. Prior A11/A13 exhaustion remains unchanged.

Post-D/E validation (10:45UTC): all nine retained Idris files freshly checked,
eight positives plus exact intended negative PASS; seeded package207/207 PASS.
Seventy total invocations accounted:56 ordinary successes (including3 package
calls and C's type-only probe),3 intended negatives,10 rejected diagnostics,
1 no-verdict interruption. Old five spikes/five holes and production stay exact.

## Status — R179 post-F/G checkpoint

F's10 units prove actual canonical supported endpoint lookup/Active/nonretired
and view-domain capital, reify its committed accumulator/view, recover the actual
original counterpart/full one-sided controls/static fields, and compose exact
original→own canonical→actual replay effects plus supported controls. These are
conditional producers/consumers of existing capitals, not concrete whole-schedule
executions. The stronger one-sided facts need neither A9 nor original uniqueness;
D's bilateral supported birth producer genuinely consumes A9. F4 only eliminates
already-provided raw withdrawal evidence; no O21 withdrawal packet is produced.

G's8 units expose exactly two existing observers, integrate E's actual selector
with the SAME fixed-order rank observation, inspect the same pair's orientation,
and EXECUTE its chosen right action at the before-left cut. The positive result
contains a real checked endpoint with exact original action AND tag. A different
tag or failure is rejected. `Nothing` proves neither canonicality nor absence of
some later applicable pair; G7 does not scan further after the first failed
candidate. The existing concrete E fixture now checks exact canonical observation
and actual early Begin1, count4 and `Just (2,0,1,False,True)`; it does not reduce or
claim success of the opaque combined orientation consumer.

G visibility deviation is expressly authorized: only `public export` before
`canonicalWorkActionRank` (needed by concrete proof reduction), and only `export`
before `canonicalWorkInspectOrientation` (opaque result consumer). No old helper
body/signature, protected hole, production module or LocalDiamond surface changed.
No new escape hatch/partiality/local let/with. F had three charged diagnostic
repairs (all PASS2); G all first pass, with monitored56s CanonicalSort checks.

Next: the precise O20 missing lemma is **SupportedCanonicalEpisodeSynchronization**
(frontier name only, not an Idris declaration): paired actual supported-episode
prefixes under `expectedBridgeBijection sameInputs` must produce renamed GLOBAL
effects and resolved-input/committed-view/pointwise undo relations, propagating
through checked Begin/Advance/Finish. Ambient has no name-wise supported-domain
restriction. Unsupported generated children separately remain open. O17 still
needs private reached-worklist plumbing, a completeness/existence argument,
independence and child/parent side conditions, actual diamond and sealed decrease.
Thm73 and all five prior holes remain OPEN; A11/A13 remain exhausted and A14 blocked.

## Status — R180 bounded grind shift

Budgets exhausted: A14/14, B15/15. Production and all five original spike files
are unchanged against the authenticated baselines. Five holes remain, split
CanonicalSort/CrossTrace/DeletionChain/LocalDiamond/Renaming =1/3/0/0/1.

**Fully proved new capital:** A's actual post-provider-Finish lookup Just0;
producer-observed raw consumer Begin and Finish with every observation closed;
exact Begin output WF and its full committed-view-domain conjunct, obtained from
already-proved raw Preservation and R179 source WF, not assumed; checked Begin
as a projection of these prerequisites; a genuine five-edge provider/consumer
lifecycle suffix and final WF. Its start is the already-registered root source,
not yet a checked empty-origin whole trace. R179's earlier certified-prefix
rejection is not silently identified with this separately indexed suffix.

B proves actual-Maybe-head resolution from ordered renamed tables, structural
resolution projection, exact normalized local input equality, deterministic
iterator outcome identity including the returned callback, and pointwise pushed-
undo propagation. These are INTERNAL induction consumers; they do not make
synchronization an O20 input. `SupportedCanonicalEpisodeSynchronization` is now
an Idris record at ONE pair of actual prefix/suffix cuts, with the accepted
bijection fixed by `sameInputs`, GLOBAL ambient and ordered tables, and the
selected supported actor's full renamed Maybe-control. The actual operational-
left/right-canonical ZERO-prefix instance is produced from their common empty
origin. R179 view/domain packets are produced at both actual canonical endpoints
using accepted A9 plus both original uniqueness proofs and matched generations.
No view or accumulator equality between those endpoint packets is asserted.

**Partial/open:** all nonempty paired episode induction (real matched Begin
providers/views, committed/effect resolution connection, actual Advance global
registry preservation, and Finish closure); unsupported-child obligations are
additional, not the sole remainder. A still lacks authenticated empty-origin
whole execution/totality, quiet/noFailure, protocol and full fifteen-field replay
bundle, precise blocks/coverage/order/disjointness/uniqueness and full current
AdjacentActorSwapSafety. Thus no full O19 negative, no revised safety/fixtures,
no O19 body permission request, no O20 body, and no confluence proof.

**Stops/escapes:** no new live hole, postulate, believe_me, assert_total, partiality,
with, local proof lambda or local let. A5's3/3 checked-edge attempt was removed;
one interrupted compiler was explicitly reconciled. Its supervisor-authorized
A6/A8 prerequisites now support checked constructor projection, not a fourth
A5 direct probe. B3's3/3 suspended-case body was removed; separately authorized
B4/B5 observed-head prerequisites and B6 structural projection cross that wall.
Exact failed snapshots remain only in evidence, not live source or accepted TTC.

**Next:** authenticate A's two root insertions and total execution, establish
quiet/noFailure and component protocol, then construct every current safety field
before requesting any revision/body gate. For B, advance the actual paired cuts
through registrations and supported Begin/Advance/Finish using the internal
consumers; only after that isolate the unsupported-child endpoint remainder.
Compiler/source correlation, every attempt and guard are catalogued in
`research-tests/O6-R180-GRIND-SHIFT-AUDIT.md` and its compiler ledger/archive.

## Status — R181 bounded shift (2026-09-07)

**Fully checked retained capital:** actual seven-edge empty-origin provider /
dependency-bearing empty-consumer trace, exact designated alignment, genuine
protocol/discipline, quiet/noFailure/both Active final state, every-boundary
TraceComponentsTotal and exact early consumer Begin rejection at the SAME
pre-provider block source. `InstalledCutObservation`/its executable observer
retain actual Fiber/lifecycle/callback VALUES and erased lookup/lifecycle
identity proofs. Soundness/completeness and all five actual installed-cut
observations are proved. This explicitly avoids A11's guessed accumulator wall.

O20 now has a nonzero matched-registration `SupportedCanonicalEpisodeSynchronization`
successor preserving BOTH actual prefix occurrences, supplied whole executions
and FIXED accepted bijection. Global ambient/all ordered-table updates, selected
control insertion and actual replacement projections are proved. Actual committed
resolution connects to R180; deterministic successful callback observations
produce local-state equality and pointwise pushed undo. B11/B13 observed-table
prerequisites are separately checked; their attempted B12 composition is absent.

**Partial/not proved:** complete old-safety negative (InstalledTrace and located
blocks, ordering/disjointness/coverage/decomposition, raw uniqueness,
component-specific independence and bundle assembly); no research safety revision
or O19 body. The consumer's root insertion clears its table and is NOT universally
identity despite its empty program. O20 still lacks actual canonical matching/
pair selection, complete Begin views and Advance/Finish propagation/induction,
unsupported-child/gap handling and selector/body. O21 withdrawals are ONLY the
precise obligations document plus one removed record-type probe, not branch proofs.
Five inherited holes remain1/3/0/0/1; no new proof escape, postulate or partiality.

**Stop discipline:** A11 3/3 removed; supervisor reopened only five DISTINCT
observed-lifecycle prerequisites after B. B12 3/3 removed; B13 authorized out of
order while it was parked2/3, retained. A16/16 consumed, B13/15 with B14/B15 not
recycled, C one of3 checks. No unauthorized original-spike/production edits.

**Explicit workflow violation:** an unconditional shell command mistakenly
committed failed B11-1 asdfc933e and launched B12-1 with two unaccepted declarations.
Both failed checks count; B12 was removed and dfc933e git-reverted ascdaee57.
B11-2 subsequently PASSed and was correctly committed19a798c. The supervisor was
notified. The evidence checker records the exact bad snapshot and reports
`oneNewDeclarationPerInvocation=false`, not a false clean-protocol certificate.
No failed declaration is retained. This is a required independent-review concern,
not an escape hatch in any theorem or an accepted waiver. Subsequent commit
commands verify the passed JSON under `set -e`.

**Next, separately authorized work:** assemble current safety from the real A16
observations before any revision/body gate. For O20, supervisor's precise B12
wall diagnosis is that separately elaborated anonymous case tables remain
nonconvertible even when printed identically: re-derive the B11 eliminator over
ONE explicit observed TABLE value supplied by B13, not another bridge between
two anonymous cases. Then finish actual matched Begin/Advance/Finish construction.
For O21, authenticate the exact current withdrawn original birth and produce the
full one-sided Lemma57 endpoint packet before branch assembly; never infer
absence from a raw withdrawn name or discard the mapped-current alternative.

All scope/attempts/evidence are in `O6-R181-GRIND-SHIFT-AUDIT.md`, the compiler
ledger/archive, and `O6-R181-O21-WITHDRAWAL-OBLIGATIONS.md` under research-tests.

## Status — R181 D/E authorized continuation (supersedes prefix at92e2daa)

D6/6 completed15:13UTC; E8/8 conditional continuation therefore met its >=60min
remaining guard and completed15:26UTC. All D units PASS1; E4 PASS2 after importing/
qualifying the actual CalculusChecks components rather than Section3Example's
ToyComponent. The passed-bit assertion under set-e stopped that failed combined
command before any premature commit or E5 invocation; no further workflow breach.

**New fully proved capital:** D's one-NAMED-table B13-inside-B11 replacement
cures the suspended case boundary. DISTINCT observed-table owner uniqueness,
actual committed projection, actual successful provider-head correspondence and
structurally recursive ViewRelatedBy for actual successful resolveView outputs
are proved. This is a genuine paired Begin-view prerequisite without a view
oracle, not a fourth B12 attempt or complete O20 producer.

E constructs exact provider/consumer body traces, full InstalledTrace at every
body state via A16, both LocatedOpenEpisodeBlock records with ALL fields on the
same certified count7 trace, exact provider-before-consumer ordering, and full
lifecycle coverage[0,1]. No caller-provided block or guessed callback is used.
There was no public retained R172/R174 block builder to import; the existing
public CP3 constructor was used and the private canonical builder stayed frozen.

**Still partial:** O19 needs 3x2 numeric range disjointness and full decomposition,
raw insertion uniqueness, real component-specific independence and bundle/current
safety. No completed negative/revision/body permission. O20 still needs actual
canonical pair selection, Begin/Advance/Finish successor controls/induction,
unsupported child/gap/selector/body work; matched resolveView alone is not that.
O21 remains obligations only. Forty-one retained new declarations, five inherited
holes unchanged, no new escape/partiality/production or original-spike edit.
Parent owns the independent review, including the earlier reverted dfc933e and
premature B12-1 workflow violation, which remains explicitly not excused.

## Status — R181 F8/8 continuation (supersedes D/E prefix)

**New fully proved:** actual3x2 disjoint ranges and full ActorBlockDecomposition
on the SAME authoritative provider/consumer blocks; strong original count7
UniqueRawNameInsertions for arbitrary located root/child insertions; actual
ReachedFromEmpty and protocol-derived RegistrationProvenance. F1–F4 are in
R181O19BundlePrerequisites; F5–F8 in R181O19UniquenessAndBundle. Splitting the
independent checks avoids repeating the68-second numeric/block-field proof on
every later fixture unit; no original file or interface was changed.

**Conditionally proved, NOT inhabited:** r181ReplayBundleFromIndependence
constructs the exact existing ReplayInvariantBundle and derives all14 other
fields via trace/alignment/discipline/totality/endpoint capital and existing
rank/support producers. The single visible quantity0 TraceIndependent input is
still NOT produced. Its TODO(proof) documents a genuine remaining obligation,
not a postulate, new hole or modified O19 premise. Empty consumer program does
not imply an identity generated monoid: OInsert1 clears its table. R172's empty
key/universally-related-state proof is inapplicable to ToyKey.

**Still partial/stated:** complete old-safety negative, actual component-specific
TraceIndependent, both body NoGeneratedChild proofs and final order-swap/
AdjacentActorSwapSafety assembly. Next is the real independence proof over both
generated monoids AND iterator-outcome stability; then inhabit current safety
and commit the full negative before requesting any revision/body authorization.
O20 has actual successful-view correspondence but no full canonical pair/control
induction/bridge body. O21 withdrawal branches remain obligations only.

F2 needed3 attempts: forced index binder, then nested indexed coverage, then a
checked single-head dispatcher. F3 needed2: the first emitted an undefined direct
source name EVEN WITH exit0; passed=false correctly blocked its commit and the
next declaration. Explicit direct imports repaired it. No new workflow violation,
unsafe proof, partiality or escape.49 retained declarations across six files;
five inherited holes unchanged. Earlier A11/B12 real stops and the reverted
failed B11/premature B12-1 workflow violation remain unexcused and preserved for
parent-owned independent review. No further proof unit started after F8's cap.

## Status — R181 terminal G resource stop (supersedes F prefix)

**Fully proved additional capital:** G1 r181ConsumerLookupAfterBegin obtains the
actual consumer's explicit Reloading[]/id/view payload using lookupReplacedFiber
and the THREE actual checked foreign-provider updates. It does not observe a
nested provider builder with scalar Refl or guess the provider's accumulator.

**Not proved / removed:** G2 r181IteratorStageIsProvider attempted to show every
reachable nonterminal stage in the real count7 trace has actor0. This is the
necessary exclusion of consumer forward/yielded generators, NOT independence
by itself. Nested captured dependent OccursIn splits grew to48,438,144KiB RSS
and566.615s; the supervisor authorized terminating attempt1 as interrupted/no
verdict. SAME statement with thin LHS patterns/forced-field wildcards hit the
unchanged48GiB guard at102.840s/max50,642,656KiB, before the authorized150s limit.
No compiler diagnostic/verdict exists for either; they must not be represented
as type refutations or successful proofs. Per explicit override, STOP at2/3:
whole declaration removed, exact G1 source restored and freshly PASS2.089s.
Third attempt and G3–G6 remain unused, not silently recycled. No extra escape.

**Still partial/stated:** actual TraceIndependent (generated monoid commutation
AND iterator-outcome stability); F8 stays a conditional bundle function, not an
inhabitant. No full negative, no research safety revision/O19 body. NoGeneratedChild
body proofs and final order-swap/safety assembly were explicitly deferred to the
next shift. O20 incomplete beyond actual matched views/registration successor;
O21 withdrawal branches obligations only.50 retained declarations across seven
Idris files; five inherited holes unchanged. The earlier reverted B11/premature
B12-1 workflow violation remains unexcused; parent owns independent review.

**Next:** avoid direct case elimination of a stage indexed by the full closed
trace and callback-bearing concrete source states. Produce a generic per-step
stage-restriction certificate over abstract state indices, then instantiate with
actual runtime observations. Even the thin LHS alternative expanded excessively;
this is an elaboration/resource wall, not a paper or logical counterexample.
After a real independence proof, project F8 and assemble current safety/full
negative BEFORE any subsequent revision/body gate. No further proof work this shift.

### Owner decision16:50UTC — superseding next-step gate, NOT a new proof

**Owner decision, exception to R146 doctrine.** For the NEXT SHIFT,
AdjacentActorSwapSafety revision under R146(iii) (support incomparability /
both-direction applicability) is authorized WITHOUT completing the old-safety
negative. The certified count7 trace, actual swapped-source consumer Begin=None,
both blocks, decomposition, uniqueness and14/15 bundle fields are accepted as
sufficient partial-negative evidence. Owner's stated reason: "failure mechanism
fully certified; missing field unrelated to the mechanism".

This supersedes the preceding requirement to finish independence/full negative
BEFORE research safety revision. TraceIndependent continues in parallel as
capital, NOT a gate. No mathematical inhabitant or complete negative is implied,
no O19 body authorization is inferred, and no source revision/proof work is
performed now. The next shift may implement the authorized safety revision and
continue the abstract-index stage-certificate route independently. This approved
methodology exception does NOT waive the earlier unexcused B11/B12-1 workflow
violation or the parent-owned reviewer gate.

## R182 — O19 owner-authorized surface correction

The owner accepted the certified R181 failure mechanism despite the unrelated
missing TraceIndependent field. Research `AdjacentActorSwapSafety` now requires
actual checked right-first LBegin at the exact pre-left cut; left-first already
comes from its located blockOpening. No swapped trace/diamond is assumed.
`R182O19RevisedSafetyNegative.r182DependentPairRejected` refutes this strengthened
safety on the real count7 provider/ServiceA-consumer pair for any exact bundle.
`R182O19RevisedSafetyPositive.r182IndependentSafety` inhabits the entire revised
predicate on actual independent empty-key components; both six-edge orders,
full bundle, installed blocks and decomposition are constructed. No full old-
safety negative or count7 TraceIndependent is claimed. O19 remains a hole.
All failures and exact producer corrections are in the R182 audit. No escape
hatch, new hole, production change or LocalDiamond change was used.

R182 B additionally corrects the distinction between BlockBefore and actual
adjacency: the owned intervening segment must have count0. The owner authorized
six checked micro-units; the nine-edge Insert2-gap fixture owns all15 bundle
fields but its negative explicitly conditions on the selected gap observation,
not a claimed full old-safety countermodel. A14 still fully inhabits current
safety. Adj6-2 was proactively interrupted (158.8s/15.95GiB); the final universal
bundle formulation/existing Nat contradiction passed13.5s. No unsafe primitive,
new hole or production/LocalDiamond change. See the exact R182 clause addendum.

### R182 checked A/A operational construction milestone

`CP5O19AdjacentReplayProducerSpike.o19AdvanceActivationPair` constructs a genuine
A/A diamond and sealed suffix replay from exact source facts/positive guard,
derives external evidence, and transports original uniqueness. NO CrossTrace
import cycle, private-visibility change or frozen-spike edit. The no-input
`R182O19ActualCrossingPositive.r182ActualFirstCrossing` instantiates the entire
pipeline on A14's source: real first Cartesian crossing and all15 reached
bundle fields, not an assumed result. Exactly one of four required nodes;
general later applicability, other orientations, complete Cartesian/range
update remain open. O19 RHS untouched (zero body attempts because complete
construction prerequisite is missing). No new hole/escape or count7-independence
claim. See R182 audit's exact remaining boundary.

## Status

### R182 final construction status (supersedes the first-node checkpoint)

**Fully proved in research:** owner-authorized right-first and true-adjacency
safety corrections, real count7 dependent-pair rejection, full independent
A14 safety/bundle/both six-edge traces, and the observed-gap rejection with its
explicit `gapObserved` premise. Generic A/A node production invokes the frozen
suffix theorem and retains the same reached bundle and original uniqueness.
Actual checked determinism authenticates opaque reached cuts without arbitrary
state equality. Public sealed folds produce the actual two-Finish suffix view.
Explicit observed-package composition constructs all FOUR concrete crossings
with NO INPUTS (`r182ActualAllFourCrossings`), preserving four actual sealed
results and the complete nonempty source-to-final chain. Generic finite and
nonempty count-addition lemmas are proved by structural induction on observed
derivation data, not scalar observations of dense replay builders.

**Partial / merely stated:** O19 remains the same hole with ZERO body attempts.
The input-free four-node instance is not `WholeBlockSwapDerivation`: no complete
source-origin plan, concrete count-equals-four certificate, target block
installation/range/decomposition or arbitrary-block Cartesian induction is
claimed. A/O, O/A and O/O propagation is still absent from the new producer.
O17/A8, O20 synchronization and O21 withdrawal remain as previously gated.
R181 count7 TraceIndependent is still absent; C/D were not begun. Census5.

**Resource / design notes:** B32-1's case on a computed existential hit the
48GiB guard (517.494s, sampled48.10GiB), was process-group terminated with NO
VERDICT, and is fully charged. B32-2 returned the direct produced package in
8.311s/~4.91GiB; B33 moved elimination to an explicit observed parameter. B38
then simultaneously assembled all four actual nodes (117.258s/~15.75GiB).
This is a resolved proof-engineering boundary, not a specification counterexample.
Separate observation/fixture modules prevent needless rechecks of costly
construction bodies. Exact source snapshots, diagnostics, memory samples and
commit associations are archived. No fourth invocation or failed3/3 B stop.

**Escape hatches:** NONE added. No believe_me/assert_total/postulate/partiality,
new holes, local let/with/as-pattern, callback extensionality, scoped-to-raw cast,
private visibility change or frozen deletion/suffix-body modification. Data
fields remain ordinary executable indexed data; proofs and observations are
quantity0. The new generic modules keep model types abstract; Unit/empty-key
specialization is confined to the honest concrete fixture.

**Next:** follow the seven exact R183 construction nodes in the R182 audit:
produce the current-state cursor, arbitrary later applicability/four orientations,
simultaneous Cartesian iteration plus source-origin equations, exact coverage/
bounds/uniqueness/count, and installed target ranges/decomposition. Only after
that complete construction is committed may O19 RHS receive fresh3/3 and its
mandatory census4/owner closure gate. Never supply those desired outputs as
premises or substitute the independently constructed opposite-order trace.


### R183 bounded construction status (supersedes R182's next-work list)

**Proved in research:** an arbitrary-length A/A BEGIN row now derives every
intermediate guard from the original one-cut guard and the actual replay
bundle, then constructs its own local crossings, sealed suffix replays,
reached bundle, original uniqueness, finite derivation and exact row count.
`o19BubbleBeginRow` is not a four-crossing fixture disguised as induction;
`r183ActualGenericBeginRow` independently instantiates that generic function
on R182's admitted source, with NO INPUTS and two actual first-row crossings.
The reached cursor always retains its own actual trace and evidence.

A separate generic partial-map kernel derives an actual early-right effect
result from original frames, congruence and partial commutation. This is NOT
checked control/tag applicability. A25's attempted actual-pair integration
exhausted three compiler checks (eta/visibility boundary) and was fully
removed; it was NOT retried under a different name. Five later micro-units
proved smaller pointwise composition/commutation transport, primitive actual
forward-map projection, actual captured-map commutation and frame projection.
The actual integration and source-map rebasing remain future work.

Canonical pair selection now chooses both authoritative blocks in the actual
operational-left/right-canonical executions under the fixed accepted bijection,
conditional on genuine existing operational capital. It derives their actual
opening occurrences and both pre-opening WF facts. R181 D6 is instantiated
at these exact cuts. The shared dependency list, successful resolver outputs
and cross-cut effect agreement are INTERNAL induction hypotheses; equal
component headers/programs and whole-prefix effect/control synchronization
are not produced. No arbitrary replacement execution, target state or
caller-chosen bridge bijection is used.

**Partial / stated:** no entire O19 prerequisite group(i)-(v) is complete.
Later Cartesian rows and checked applicability, all four block orientations,
exact original occurrence plan, whole coverage/product count, and installed
target ranges/decomposition/origin update are open. O19 received ZERO body
attempts. One disposable O20 selector probe used2/3 checks: the existing
rank/adjacent guard has the wrong pre-block state index and does not prove
an empty between-block gap. These are sizing diagnostics, not an impossibility
proof for a future selector. Ten finite-linear-extension obligations are
listed in the R183 audit. O20 synchronization and O21 withdrawal remain open;
O17/root placement is untouched. Census remains5=1/3/0/0/1.

**Quantities / escape hatches:** new theorem/specification functions and
proof fields are quantity0; actual states, traces, selected ranges and partial
outputs remain ordinary indexed data. Model types stay abstract except the
honest Unit/empty-key fixture. No unsafe primitive, postulate, partiality, new
hole, new with/local alias, computed-existential local case or scoped-to-raw
cast was introduced. The only permission exception is TWO prior-approved
LocalDiamond visibility keywords: public export on the existing
`RawActivationMove` record, plain export on existing
`beginRawAfterForeignActivation`. Their actual consumers are
`o19CheckObservedRawMove` (both raw projections) and
`o19BeginAfterActivation`. No LocalDiamond declaration/body/signature/order
changed; byte reconstruction and frozen suffix hashes are checked by the
R183 frozen-audit script. No build/seed/LocalDiamond TTC was deleted.

**Next:** use the small actual-map transport/frame lemmas to finish the
actual effect-domain specialization, then DERIVE rebased checked control/tag
applicability for later Cartesian rows. Complete all-four orientation,
source-origin/coverage/product-count and target-installed-block construction
before any O19 RHS attempt. For O20, derive legal complete block selection
with BOTH revised clauses and preserve it through actual replays; establish
the internal paired-prefix effects/controls before claiming an endpoint
bridge. All30 A and8 C slots were consumed; no fourth retry or hidden body.
Exact checks, rollback evidence and final validation are in the R183 audit,
compiler ledger/archive and final evidence report under research-tests.

**Final validation:**65 serialized checks:55 ordinary PASS,2 expected compiler
rejections counted as negative-test PASS,8 charged rejected attempts,0
interruptions. All17 final regressions passed (16 fresh research target checks
and the seeded production package build);207/207 seeds remain. Every37 retained
source-changing commit has an earlier exact-hash fresh PASS. The final evidence
report records frozen/production/CP3/census/cache authentication. No unproved
body is recast as proved, and independent reviewer acceptance remains pending.

## Status — R184: actual effect/resolver capital and guarded candidate search

**Fully proved capital:** actual captured-right partial-effect result by DIRECT
composition of R183 A24/A29/A30 and public frame/respect producers (`50e764e`);
actual checked OInsert shared resolver observation with exact before/after
equations (`f4d691a`, `3de39dd`, `63c173f`); finite neighboring-actor candidate
search whose EVERY positive result owns both sanctioned O19 safety clauses,
both actual-body child exclusions and original insertion uniqueness (`59cf3a21`);
actual Begin component/resolver/destination observations at both authoritative
paired cuts and genuine effect-agreement propagation through those two Begins
(`5cb19b96`).24 new declarations total; all source commits follow exact fresh PASS.

**Partial/open:** O19 orientation rows, Cartesian induction, exact source-origin
plan/product count/coverage, reached installed blocks/origin update and full
same-chain endpoint/external assembly. O19 body0; five holes unchanged. The
selector is a safe-candidate producer, NOT an inversion selector for a common
accepted support/ancestor extension, no decreasing canonicalization measure or
O19 replay/reselection; Nothing proves neither no legal swap nor canonicality.
The actual Begin observations use each component's OWN dependencies. Equality
of those components/lists, full paired-prefix effects/controls, matched program
steps and the O20 bridge remain open. No existing theorem body was restated or
filled with an assumed output. O17/root placement and O21 withdrawal untouched.

**Ratified stops:** A2 insertion-target equation failed3/3 and its new module
was removed; supervisor ordered distinct observation prerequisites A3–A5.
A6 generic target transport from that named observation also failed3/3 and was
reverted. Rewriting/replace could not expose or convert the resolver under the
neutral targetFiber conditional. This is an elaboration wall, NOT a semantic
impossibility or third O19 specification gap. The supervisor ratified the
unit-level stop. Next-shift cure: make the resolved target an EXPLICIT parameter
of the O/A ROW and pass the A3 observation record, keeping targetFiber OUT of
its goal; do not retry A2/A6 as another transport lemma.

**Quantities and boundaries:** new proof/specification functions are quantity0;
actual components, states, traces, views and candidate words remain indexed
ordinary data. B3's simple generated-child-name observer is executable runtime
code. These research checkers are not advertised as a deployed runtime API.
No unsafe primitive, postulate, partiality, new hole, with, local alias, computed
existential case, scoped/raw cast or frozen deletion call. No LocalDiamond edit
or visibility change; frozen suffix and production/CP3 unchanged. Original
uniqueness is explicitly retained in the chosen safety package; one-trace
checks make no claim to generate cross-trace GeneratedOrchestrationMatched.
Existing paired acceptance interfaces remain unchanged. Exact source snapshots,
all rejected checks and fresh validation are archived under research-tests/.

**Next:** resume the explicitly parameterized O/A row, then remaining orientation
rows and Cartesian construction before any O19 body. Direct the safe-candidate
search toward the fixed accepted finite extension and prove existence/descent;
connect actual common components/dependency lists and matched program execution
to the paired-prefix invariant. No new attempt beyond the ratified/capped units.
Independent reviewer acceptance remains pending.

## Status — R180–R191 (2026-09-08)

This addendum supersedes the *current-status interpretation* of the historical
R179 entries above, without deleting their evidence or stop records.

- **O19 closed in R189** at the accepted revised safety boundary. The current
  research census is **4 = 1/2/0/0/1** (CanonicalSort/CrossTrace/DeletionChain/
  LocalDiamond/RenamingComposition). Both O20 bodies remain open; neither was
  attempted in R191. Production, CP3 and the frozen adjacent-swap declaration
  are unchanged.
- **R191 owns 94 new checked declarations.** The accepted supported common
  reference, its transport through the actual operational search, finite
  stopped-order inversion availability and two-sided physical child exclusion
  are proved. The goal-state/full-path plumbing was removed in one expressly
  ratified four-module internal migration because only goal-order uniqueness
  was used. Restricted supported paths are never coerced to arbitrary full
  support paths.
- **Convergence capital advanced:** the general actual Begin adapter now derives
  its shared component through explicit observed values. Actual observed
  Advance/last-step Finish, empty-program Finish and root/child insertion and
  retirement successors preserve all-name cuts. The native-edge paired family
  stores no successor or preservation oracle; its total induction and both
  actual LTS projections are proved. An eleven-edge identity-renamed fixture
  derives the full endpoint cut from a genuine empty origin.
- **Unsupported-birth progress is deliberately weaker:** every actual canonical
  origin owns an exact original stamp and either authentic closing evidence or
  a matched right-original event/birth and generation equation. Closing is not
  discarded, current raw-name equality is not invented, and right-canonical
  retention is not presumed. No O21 withdrawal theorem was consumed.
- **A8 is O17-only initial-placement construction**, not an extra O20 dependency:
  accepted O20 capital already contains root-first placement. Actual operational
  preservation/physical gap ownership remain separate obligations.
- **A10 awaits the owner's grammar-gap decision.** The child-retirement candidate
  owns eleven checked edges, alignment, real registration discipline, all15
  bundle clauses and all3 frozen blocks. Full decomposition/placement/canonical
  acceptance were not inhabited. F7 exhausted3/3 on native finite `BeforeIn`
  coverage and was restored; it is NOT an accepted counterexample. The ratified
  next-shift direction is the R188 target-order selector pattern, not a disguised
  fourth flat-case retry. CF1 also stopped3/3 and was removed; both stops are
  recorded. No proposed grammar cure was implemented.

**Next:** owner A10 decision; selector physical zero gap, right-first Begin,
exact enumeration/orientation wiring and `stoppedOrder = goal`; convergence
canonical paired extraction, Remove/failure/diversion completeness and the
unsupported fixed-current-name/right-canonical triangle. Attempt either body
only after its required clauses are producer-owned. No new unsafe escape,
postulate, partiality or proof hole was added. New proof functions/specifications
are erased; runtime data remain explicit. These results are not a deployed
plugin runtime or a runtime-performance claim.

The exact ownership correspondence, final verification, every compiler
invocation/receipt and remaining gates are in
`research-tests/O6-R191-O20-DESIGN.md`, `O6-R191-VERIFICATION.md`,
`O6-R191-GRIND-SHIFT-AUDIT.md` and the R191 compiler ledger/archive. Author review
and compiler success do not substitute for the required independent acceptance
review.

## R192 binding owner decision — verbatim (2026-09-08)

> OWNER DECISION (2026-09-08, binding, record verbatim in your A8/A10 memo, audit, THM73-PLAN and NOTES): A8 and A10 are resolved by OPTION A — a DEFERRED PRODUCTION UNFREEZE of src/DGamma/CP3.idr limited to the canonical-form definitions: CanonicalInputPlacement (A8: root-first MODULO PROVISION AVAILABILITY, the R178 replacement placement record) and ActorLifecycleOnly (A10: the actor's own generated-child ORetire/ORemove belong to the parent's block). Sequence: (1) research-copies FIRST — prove both cures on research variants (ActorLifecycleOnlyExtended; the R178 placement record), including the zero-gap completeness for the selector and the O17 root phase on those variants, with fixtures (R191 F1–F6 child-retire candidate must fall INSIDE the parent block under the variant; the R174 provision-collision candidate must be admissible under the revised placement); (2) then a single production-unfreeze shift prepares the EXACT CP3 diff (definitions + in-file dependents), the clause map, and a memory-safe seeded rebuild plan (the CP3 change invalidates most downstream TTCs; plan a serialized module-by-module build via the /tmp/dgamma-build-loop.sh pattern under the 48 GiB monitor — the from-scratch Chez peak was ~138 GiB; never run the whole package build in one unmonitored process); (3) the owner signs the production diff before it is committed. Until (3): production stays byte-identical to 34b21c9; the frozen-surface rules are unchanged. Your Unit C memo becomes the plan for (1)–(2): make it precise (names, line numbers, dependents, fixture list, rebuild plan). No production edit this shift.

This ruling supersedes earlier pending/option-comparison language, but does NOT
unfreeze production in R192. Current-shift O17 prohibition remains; variant
root-phase work is planned for the explicitly authorized research sequence.

## R192 A11 exact-field approval / coverage split

Supervisor need_decision gate approved the EXACT existing fourth field of
ReplayedCanonicalEndpointBridge gaining ONLY original-endpoint
`isSupported child leftFinal = True`. The record already binds leftFinal;
constructor and first three fields remain byte-identical. O21's
`replayedCanonicalToOriginalEndpointSpike` declaration/body remains unchanged
and remains a hole. Supported children: fixed current raw-name match plus
exact historical generation/origin triangle. Unsupported histories:
generation-only E8 / o20CanonicalOriginMatchOrClosing. PRESENT unmatched
original remainder: full CP3 VestigialEndpointGeneration in unchanged O21
endpoint statement. Removed names: actual absence, not invented vestigial data.
No production/LocalDiamond/O19 change. Exact field/record old/new hashes,
consumer binder plumbing and serialized guard receipts are specified in
research-tests/O6-R192-A11-SURFACE-MANIFEST.json and the A8/A10 decision memo.
A11 is a research-surface correction toward frozen production fidelity,
NOT a weakening of paper Theorem73 or closure of either protected proof.

### R192 A11 implemented result and retained proof debts

Exact two-line fourth-field scope correction committed `ebaa750e`; supported
constructor consumers retained with fresh expected PASS. New total erased
`o20SupportedBridgeFromOwnedCut` derives the ENTIRE scoped fourth clause from
accepted supported-birth capital, not a opposite-birth callback. Its ALL-name
cut argument is still input: arbitrary canonical paired execution extraction,
failure/diversion and convergence remain open. Actual supported-child positive
and removed-child old-negative/new-vacuous-positive compile. Missing discarded
generation cannot fake PRESENT vestigial status. Full independent-canonical
removed fixture, concrete one-/two-sided full vestigial packet and active-fake
negative are still open. O21's exact declaration/body bytes and proof hole
are unchanged. Unit C's precise deferred CP3/unfreeze sequence, affected
clause map and 48-GiB serialized seeded rebuild protocol are in the owner memo.
No production edits/build-seed deletion or O17 construction occurred in R192.

## Status — R192 checked partial milestone

Fully checked new capital:48 total declarations (A27, B9, C7, D5), including
actual bilateral Begin/Reloading observations, native paired Remove and both
LTS projections, conditional physical right-first Begin, the research extended
actor grammar/inclusion, historical removed-name obstruction, actual supported
positive, and the entire newly scoped fourth bridge clause from an OWNED
all-name cut plus accepted canonical capital. The cut is not extracted here.
The only approved mathematical surface change is A11's two-line ORIGINAL
support guard; first3 fields and O21 statement/body bytes are unchanged.

Partial/stated: arbitrary canonical paired extraction and failure/diversion;
resolver/candidate/orientation/stopped-order completeness; physical zero gap;
full R191 reordering and availability-aware canonical decomposition/O17 phase;
full canonical/vestigial fixtures; selector/convergence/O21 holes (census4).
A9/B10/C4 were exhausted3/3 and wholly reverted, no fourth attempts. No new
postulate/unsafe/partial escape hatch or proof hole was introduced.

Validation:113 serialized invocations,96 expected PASS (including9 negatives),
17 rejected development attempts,0 interrupted;37/37 frozen final checks plus
V38 final-source PASS.52 source commits have independently verified receipts.
V16 is retained but superseded only for an approved three-comment-line fix;
all declaration/type/body bytes of that probe stayed identical. Idris2 0.8.0;
seeded package PASS,207/207 TTC retained, max sampled RSS49,825,328KiB.
Production remains byte-identical to34b21c9; O19/LocalDiamond/adjacent frozen.

Next: close the research placement/relocation and operational extraction debts
with explicit producer ownership, investigate history-sensitive internal maps
versus current endpoint maps, then exact owner-signed CP3/in-file-dependent
diff and the memo's serialized seeded48GiB rebuild plan. No production cure,
O17 body construction, zero-gap coercion or O21 withdrawal consumption in R192.
See O6-R192-GRIND-SHIFT-AUDIT, decision memo, compiler ledger/archive and
verification for exact claims, remaining fixtures and invocation qualification.

## R192 final gate — accepted checked PARTIAL

Supervisor independently verified and RATIFIED9f41aea1; permission to close
granted, no more proof/source edits. Artifact-only gate addendum records the
verbatim ruling and subsequent read-only PASS audits. Independent reviewer
is parent-owned/read-only and pending at this handoff. Remaining proof/fixture
debts and the deferred production-unfreeze requirement are unchanged.


## Status — R193 main A/D research milestone (100 retained, in progress)

The R192 ACCEPT-WITH-NOTES review's citation repair is retained: frozen CP3
CanonicalSchedule starts3240, canonicalBlock is3256--3257, inputPlacement3265.
D5/o20SupportedBridgeFromOwnedCut still CONSUMES an all-name cut.

Fully checked local advances: historical birth transport and live-generation
compatibility, authentic vestigial-vs-non-vestigial endpoint partition,
actual canonical unilateral role classification, separate native Iter/Finish
success observation extraction, local history-cut preservation under checked
Begin/Retire/matched Insert/Remove/empty and observed nonempty Finish/Iter;
actual candidate enumeration and conditional whole finite selection; whole
installed opening+body resolver transport from fixed-reference incomparability.
The last result derives internal immutable component transport, survival,
alignment, owner and resolver frames, not merely one-edge consequences.

Partial/open: arbitrary whole paired canonical alignment and history-cut
production, aligned insertion stamps/fresh names, wiring native single-role
observations through whole paired execution, all-name endpoint rebasing and
vestigial remainder treatment, producer-owned final bridge, automatic
reference-component attachment at the two physical endpoints, four semantic
selector-safety clauses at the actually enumerated cuts, and stopped-order
equality. canonicalSchedulesConvergeSpike remains untouched/ineligible; all
four protected holes and their statements are unchanged. ZeroGapPending is
only CONSUMED in main; lane2 owns relocation/extended grammar/root-phase work.

The actual8-edge present-vestigial fixture proves the historical map cannot
be silently identified with accepted current renaming merely from physical
presence. It has genuine discarded-generation/parent-closing evidence and
full SameOrchestrationModuloGenerated data, but NO independent canonical
capital; it is not a convergence counterexample. The duplicate-order candidate
fixture is algorithmic regression data, not accepted canonical capital.

No new escape hatch, postulate, partial function, with, unsafe cast or assumed
successor cut was added. Existing frozen premises and explicitly conditional
lemmas are not advertised as theorem completion. Rejected attempts remain
archived; E47-1's nonexistent import exited0 but freshness correctly rejected
it, and E52-1 required the existing transitionActor/actionOwner equation.
No3/3 exhaustion. Production/src, CP3, package, LocalDiamond, O19 and protected
adjacent/hole bytes remain frozen; final fresh audit/validation is pending.
Next: targeted native whole-block regression, final serial seeded validations,
lane2 outcome integration, committed evidence and supervisor/reviewer gate.


### R193 source-freeze addendum (ad77399f)

115 retained A30/D10/E75, no exhausted unit. The new native physical fixture
has nonempty [ServiceA] resolution to live provider0, actual Begin2/child3
Insert/Finish2/Begin1, and theorem-produced earlier Begin1 plus whole-block
resolver equality. Its concrete provider-backed starting cut is NOT claimed
to have original/canonical registration history. The callback-driven setup
that failed to normalize is preserved in E66-1; a literal cut cures this
fixture boundary without changing the theorem or claiming runtime failure.
E73's first failure was a missing defining import, not a logical counterexample.
No new proof hole/escape hatch. Final52-check seeded plan is authenticated;
results, lane2 integration and owner/reviewer acceptance remain pending.

The history-cut generation map must be indexed to the actual scanner's birth
ordinals. Original same-inputs stamps and reordered canonical replay stamps
are not interchangeable without occurrence-owned transport. That attachment
is included in the OPEN arbitrary paired-execution/insertion stamp producer,
not smuggled into the local successor conclusions. All producer/consumer
qualifications in the previous status section remain in force.


## Status — R193 frozen115-declaration partial milestone

This supersedes the100-declaration checkpoint above. Main source freeze is
ad77399f55d8bc935e0f26714f532370da4aa918:115 individually fresh-checked,
immediately guarded-committed declarations (A30/D10/E75), no exhausted unit.
Theorem73 remains partial; no protected convergence-body attempt occurred.

### Fully proved local results

- Authentic history-indexed birth/name transport, supported agreement, and
  genuine vestigial-or-agreement endpoint partition; empty-origin and checked
  local history-cut successors for Begin, Retire, matched Insert, Remove,
  empty Finish, and observed nonempty Iter/Finish. Successor cuts are produced,
  not supplied as hypotheses.
- Unilateral actual canonical-role completeness and separate native Iter /
  last-step Finish success extractors. These do not align two whole traces.
- Enumeration completeness for every distinct physical adjacent actor pair,
  carrying the actual selected payload through checking, orientation and
  finite search. Whole selector success is conditional at its OWN slots.
- Whole native InstalledTrace opening+body resolver equality and actual earlier
  right Begin across that block. Internal component transport, survival,
  evaluator alignment and owner/resolver frames are derived. This induction
  uses frozen ActorLifecycleOnly (lifecycle / yielded Insert), not lane2's
  extended Retire/Remove grammar. Endpoint/reference component attachments,
  source WF, physical child exclusion and exact zero
  gap are still explicit.
- Removed-history, actual present-vestigial history, non-head candidate-search,
  and genuinely nonempty-resolver block regressions. The latter proves actual
  [ServiceA] resolution to provider0 and invokes the generic frame theorem.

### Partial / stated / open

A(i): arbitrary initial-to-final history-cut production and endpoint rebasing
remain open. Original birth ordinals need occurrence-owned transport into a
reordered canonical replay; supported/non-vestigial agreement does not settle
all names, and genuine vestigial entries need separate treatment.

A(ii): arbitrary whole paired canonical extraction/alignment remains open.
Matched insertion stamps, fresh-name/parent alignment and native callback
observation wiring are not supplied by the current local successor lemmas.

A(iii): the producer-owned final bridge is still missing. D5 /
o20SupportedBridgeFromOwnedCut CONSUMES an all-name cut; it is not that producer.
canonicalSchedulesConvergeSpike is untouched, its statement unchanged and
its body attempt ineligible. The four protected holes remain4=1/2/0/0/1.

D: four semantic own-cut safety clauses (two NoGeneratedChild clauses, actual
earlier right Begin and actual gap0), the two physical reference-component
attachments and whole stopped-order equality are not generally derived from
accepted inputs. Main consumes ZeroGapPending and does not claim a lane2 cure.

The eight-edge present-vestigial fixture supplies full same-inputs history data
but no independent canonical schedules; the native block fixture begins at
a literal well-formed provider-backed host cut, not an authenticated original
registration history. Neither is a protected-convergence counterexample.
No new escape hatch, hole, postulate, partial function, with, cast, or assumed
successor was added; all production and frozen research bytes stay unchanged.

### Validation and review

All52 effective final checks PASSED (45 positives /7 expected negatives),
completed23:27:55Z against the immutable plan plus its one authorized
substitution. There were53 raw final invocations; overall178 checking/build
invocations matched168 expected outcomes, with9 rejected proof attempts and
1 preserved resource interruption. Original V2
LocalDiamond stopped at48.12408GiB under the48GiB guard; that failed/interrupted
record remains intact. The supervisor authorized exactly one unchanged-source
52GiB retry, V2R1, which passed/fresh/exit0 at48.14221GiB in491.214s while
holding the shared heavy lock. Its separate authenticated continuation manifest
substitutes only the final acceptance slot. All other checks retain48GiB.
Eight noncompiler authorization/immutability regression tests passed.

The premature20-call fully-visible paper-reading attestation was withdrawn,
preserved and corrected: a subsequent36-call visible reread covers all3882
content lines. No mathematical result depends on the premature claim.

Lane2 L2R1 version-pinned evidence reports35 retained declarations (B23/C12)
and15 final checks; the C9 active-source/preflight incident and unavailable
early RSS caveats remain explicit. The exact copied-definition inventory and
remaining B/C debts are in O6-R193-LANE2-INTEGRATION.md. Ongoing L2R2 is not
certified by that report. No lane2 source was edited or merged, and main
baseline checks cannot certify research copies. Final independent/frozen audits PASS at20fbd8e7: all115 source commits and
178 invocation snapshots/logs authenticated; all13 changed Idris targets have
own final checks; production/CP3/LocalDiamond/O19/protected bodies and census
unchanged,207/207 seeds, no main compiler or staged files. Ledger/archive
are committed with the R193 verification packet. Owner/reviewer ruling remains
pending; this is checked local progress, not Theorem73 completion.

Next: produce whole paired history/callback/insertion capital, handle the
vestigial endpoint remainder, produce the final bridge, and derive actual
selector safety/stopped equality before attempting the protected body.
Research grammar/placement changes require the separately owned lane2 route;
production unfreeze still requires explicit owner approval.


## R193 owner gate — checked PARTIAL ratified

Verbatim supervisor ruling:

> R193 FINAL GATE RULING: ACCEPTED — checked PARTIAL milestone RATIFIED at dd8fb9e9 (ACCEPT-WITH-NOTES pending the independent reviewer, who is now running read-only). Supervisor verified independently: HEAD dd8fb9e9, 130 commits over 77a9efe1, clean tree (baseline untracked only), production diff vs 34b21c9 empty, LocalDiamond/O19Surface/CrossTrace/RenamingComposition/CanonicalSort byte-identical to 77a9efe1, independent census 4 = 1/2/0/0/1, no idris2 running, 10 R193 artifacts present, pushed. Honest qualifications accepted as stated: A(i)/(ii) local successors and unilateral role completeness, not whole paired alignment; no bridge producer; D conditional on the four explicit clauses under the frozen grammar; V2 48 GiB stop preserved with the hash-pinned 52 GiB V2R1 continuation; lane-2 results integrated version-pinned only, not certified by main checks (correct — lane 2's own L2R2 gate and reviewer will certify them; any later update is artifact-only, as you say). The withdrawn-then-cured paper-visibility claim is noted as properly handled. Stand down cleanly; no further compiler or source work.

## Status — R194 source-frozen main milestone (46 retained)

Started exactly b81362d8; source freeze408bd21e. A30/B16 binding caps reached
without extension or any 3/3 unit exhaustion. No production, package, O19,
protected hole statement/body, LocalDiamond, A11 bridge-record or lane-owned
source change. All46 new declarations are total and individually guarded
committed. Interim independent audit authenticates52 compiler invocations,
48 PASS/4 rejected, no interruption or target mutation. A8 has two PASSes for
one comment-only precommit correction; exact code equality is independently
checked rather than silently treating the first success as a failed attempt.

**Fully proved locally:** canonical-coordinate conjugation and both bijection
laws; supported generated births carry their authentic opposite occurrence and
both original-origin/physical-ordinal equations, including operational replay.
Native Iter callback/source/target extraction now feeds an actual checked local
history successor with no source lookup/target guard oracle in its public type.
Both former E60 endpoint/reference component attachments are now produced.
Actual installedness and original supportedness produce the necessary native
lookups; the selected reached inversion's earlier right Begin is derived at
its own native left slot. Both child exclusions and native safe-check success
follow from accepted/reached capital, conditional only on literal gap0.

**Fully proved conditional theorem:** `o20StoppedOrderEqualsGoalZeroGap` uses the
ACTUAL stopped reference search, authentic inversion enumeration and the native
selector's own rejection. Its sole unresolved additional safety hypothesis is
quantified `ZeroGapPending`, exactly `transitionCount gap = 0`, for each reached
goal inversion at its native slots. This is not an assertion that arbitrary
gaps are empty. No A12Pending is needed in this frozen exact-zero theorem,
since zero actual transitions already excludes any intervening root. No lane2
extended-grammar or root-availability result follows. No sibling selector body.

**Partial/open:** arbitrary canonical/replayed whole pairing, unsupported
retained/closing birth disposition, root replay ordinal attachment, generic
last-Finish observation ownership, whole initial-to-endpoint cut fold, all-name
rebasing to the supplied current-name map, exact present-vestigial treatment,
and hence a producer-owned D5 endpoint bridge. D5 remains a consumer of its
missing all-name cut. No canonicalSchedulesConvergeSpike body attempt.
`replayGeneratedOrdinalPreserved` covers generated births, not root births.

**Escape-hatch inventory:** none added. No postulate, unsafe primitive, hole,
partial, local let/with, nonlinear state pattern, independent proof-carrying
record equality or scoped-to-raw cast in retained additions. Earlier main and
lane2 qualifications remain historical, not retroactively strengthened.

**Findings sync:** canonicalBlock is CP3:3256–3257 (record starts3240,
inputPlacement3265); R192's corrected memo is preserved. R193's two component
attachment debts are now discharged; whole alignment/rebasing debts remain.
The physically present-vestigial example is still not a convergence
counterexample with both independent canonical capitals. No new paper erratum
is promoted; relevant Theorem73 paragraphs were re-inspected, not a new full-
paper reread. See research-tests/O6-R194-FINDINGS.md and the shift audit.

**Next:** immutable56-check seeded final plan (49 positive/7 expected-negative),
frozen207/207/cache and protected-surface checks, archive/ledger/verification,
then supervisor/reviewer gate. Ten noncompiler evidence-contract regressions
PASS. Main excludes lane-owned source targets and extension-dependent probes;
no main check certifies ongoing lane2 variants. After acceptance, whole pairing
and exact all-name endpoint ownership remain the next main proof frontier.

### R194 preflight owner clarification (C2)

The C1 exclusion interpretation was rejected BEFORE any final compiler. The
supervisor requires all inherited main-baseline modules/fixtures, including
ActorLifecycleOnlyExtended and AvailabilityAwarePlacement, to be validated in
main at their unchanged baseline bytes. This does not certify ongoing lane2-
created results. No inherited target is absent, so the restored immutable plan
has59 checks (52 positives/7 expected negatives), not56. Original56-slot plan,
hash and scope are retained as explicitly withdrawn, unrun preflight evidence.
Exact ruling: research-tests/O6-R194-PREFLIGHT-RULING.md. No Idris edit, retry or
budget extension; source freeze408bd21e remains unchanged.

## Status — R194 checked final PARTIAL milestone

A30/B16:46 retained total declarations,46 authenticated one-declaration source
commits; no cap extension or3/3 exhaustion. Source freeze408bd21e. All59 final
checks PASS (52 positive/7 expected-negative), complete01:43:03Z. All7 changed
Idris targets,5 protected spikes, inherited main fixtures and seeded package
are covered. Across the shift:111 compiler/build invocations,107 matched
outcomes (including7 expected negatives),4 rejected proof attempts. All earlier
snapshots are retained. The ten corrected noncompiler guard regressions PASS.

Final frozen/independent/resource audits PASS at86b7424a. Production/package
remain byte-identical to34b21c9; CP3 blob and all protected files/statements,
O19 and A11 field are unchanged. Census4=1/2/0/0/1;207/207 seeds retained.
LocalDiamond's first planned unchanged-source52GiB validation passed491.187s,
sampled50,461,904KiB (48.12422GiB). Every other check48GiB; all11 known/observed
heavy checks acquired/released the shared lock. No interruption, mutation,
retry, stale-lock cleanup, cold build, seed deletion or orphan kill. Samples
are1s observations, not OS high-water; zero means no live sample captured.

**Fully proved:** the local canonical-ordinal/supported-birth and actual checked
Iter successor results above, both endpoint/reference attachments, and native
own-cut safety under literal gap0. **Conditional, not unconditional:** actual
stoppedOrder=goalOrder under quantified ZeroGapPending at native inversions.
**Still partial/open:** whole canonical pairing (including unsupported/root
births), generic last-Finish extraction ownership, all-name endpoint rebasing
and vestigial remainder, D5 bridge production and the protected convergence
body. No selector body, O17/O21 body work, A12-variant result or new escape hatch.

The original56-slot plan is preserved as withdrawn-unrun; the restored59-slot
plan includes every inherited main-baseline target under the verbatim owner
clarification. No ongoing lane2-created result is certified. Evidence archive
SHA256 b5333f87231d3afbec52bb7ac802292e741e1875c7f4f2d381d6367e77e58d8d,
plus consolidated ledger and reports, is linked from O6-R194-VERIFICATION.md.
Its anchor precedes its own artifact commit; no self-referential receipt claim.
Supervisor final gate and independent reviewer are pending. Next main proof
frontier remains whole paired execution and exact all-name endpoint ownership;
no additional source/compiler work is planned in this bounded shift.

## R194 owner final gate — checked PARTIAL ratified

Verbatim supervisor ruling after committed evidence52e1d308 and current-head
read-only frozen/independent PASS audits:

> R194 FINAL GATE RULING: ACCEPTED — checked PARTIAL milestone RATIFIED at 52e1d308; artifact-only gate note and close PERMITTED. Supervisor verified independently: HEAD 52e1d308, 51 commits over b81362d8, clean tree (baseline untracked only), production diff vs 34b21c9 empty, LocalDiamond/O19Surface/CrossTrace/RenamingComposition/CanonicalSort and the two lane-shared baseline modules (ActorLifecycleOnlyExtended, AvailabilityAwarePlacement) byte-identical to b81362d8, independent census 4 = 1/2/0/0/1, 14 R194 artifacts present, pushed; the two idris2 processes observed are lane 2's (separate worktree). Accepted as stated: A honest partial (supported canonical ordinal attachment, closed actual Iter successor; whole pairing / all-name rebasing / vestigial remainder / D5 bridge unowned; no body attempt); B complete to the requested result — both endpoint attachments discharged, native own-cut safety, and ACTUAL stoppedOrder = goalOrder conditional only on the quantified literal ZeroGapPending (the selector body is now one hypothesis from the CP3 diff); 59/59 restored validations incl. the unchanged LocalDiamond under the 52 GiB ruling. The independent reviewer is being launched now. Stand down cleanly after the note.

This is the permitted artifact-only note. No proof/Idris source or compiler
work followed the ruling. Independent reviewer remains parent-owned and pending;
this note does not claim its acceptance. The theorem is still conditional on
literal ZeroGapPending, and A's whole-pairing/all-name/bridge debts remain open.
The archive stays at its documented pre-artifact anchor and is not regenerated
to claim self-referential or later gate-note receipts. Standing down cleanly.

This addendum is artifact-only. No further Idris/compiler or implementation
source work followed the ruling. Independent review remains parent-owned
and pending; neither ratification nor the52-slot final validation closes
Theorem73 or changes any producer/consumer qualification above. The evidence
archive remains pinned to its documented pre-artifact anchor.

## Status — R195 checked PARTIAL milestone

Source freeze `3bd991710c76170d358dd5dadc07c676dfdb21f0`:42 checked research
proof/specification declarations (A26/B16), each immediately guarded committed.
See [R195 findings](research-tests/O6-R195-FINDINGS.md) and
[micro-unit receipts](research-tests/O6-R195-MICRO-UNITS.md).

Fully proved locally: identity/composition root laws and conditional conjugation;
constructive generic-replay root-law necessity fixture; exact original E8
closing/matched disposition for every actual generated birth, immutable replay-
origin retention and physical generated ordinal attachment; full native identity
all-name/history cuts; constructive ORIGINAL-endpoint rebasing obstruction with
full accepted inputs/internal cut; disagreement-derived original vestigial packet
and actual removed-child absence. None is a whole canonical paired execution.

Partial/open: producer-owned root law for canonical/operational stored maps;
all-stage accepted alignment, whole initial-to-endpoint history fold, actual
canonical all-name rebasing/vestigial absence and opposite image control,
D5 bridge producer, convergence body and unchanged O21 endpoint assembly.
The existing `O20PairedExecutionWithRemoval` is an endpoint-indexed local family,
not a producer on both accepted actual words. C had0 body attempts; all protected
statements/bodies remain frozen. No new escape hatch, postulate, partial, unsafe
cast or named hole. Four rejected compiler snapshots are preserved, not proofs.

Next: the owner-DEFERRED [root storing-contract plan](research-tests/O6-R195-ROOT-CONTRACT-MANIFEST.md)
for R196, not the insufficient three-keyword visibility plan. Strengthen the
adjacent fold and deletion operational capital with erased all-root laws, fill
every actual constructor site and project through the exact canonical/operational
producer chain. It changes no production API or frozen O19/adjacent body; if
that changes during implementation, STOP for an owner-level exception.

### R195 findings decisions synchronized

A11 remains exactly its approved supported-only fourth field; the first three
bridge clauses are still ALL-name. A8/A10 OPTION A stays research-first and
production-frozen until the owner signs the exact CP3 diff. A12 is DECIDED:
ATTACH after the LAST freeing release, with ordered trailing root bundles and
the LEAST key-/barrier-forced closure; roots following a forced root cannot
silently pass it just because their provisions were already available.

The supervisor's recorded paper reading (quoted in R195-FINDINGS, pinned L2R3
main-Git-object inspection) distinguishes Theorem73(1)'s (a) original orchestration
order, (b) all external-root orchestration before lifecycle, and (c) generated
orchestration after registration. A key-forced root exposes tension among these;
Lemma71(2) exchanges lifecycle/orchestration, not two orchestration inputs, and
its smaller-registry premise argument does not justify enlarging a registry by
moving Root Insert backwards past Remove. This is the supervisor's paper-level
A8/A12 diagnosis, not a new R195 formal refutation under every metatheorem premise.
Main paper2170–2399 was re-inspected; no new full-paper-rereading claim.

The selector is one hypothesis from the CP3 diff: R194 already proves the actual
stopped-order result under quantified literal `ZeroGapPending`; selector body
stays untouched. No separate A12Pending is necessary inside that exact-zero
frozen theorem. No lane-owned module or ongoing lane result is changed/certified.

Unchanged LocalDiamond has standing52GiB validation; default48GiB otherwise.
Owner extends52GiB to future prior-gated KEYWORD/FIELD-only root strengthening;
R196 must explicitly settle the necessary new-helper check's classification.
There is no blanket52GiB authorization for arbitrary changed mathematical code.
The244-module conservative invalidation inventory includes UNKNOWN costs and
non-runnable legacy/diagnostic-unclassified fixtures explicitly; it is not a cold
rebuild command or a claim that a lane2 rebuild window has been reserved.

### R195 final validation and bounded handoff

65/65 final expected results:58 positive (including the seeded package) and7 authenticated named negatives, ALL59 inherited main targets plus6 changed targets, exclusions[].112 serialized compiler invocations overall=108 expected PASS +4 rejected development snapshots,0 interrupted,0 mutated.42 source receipts and all six final source snapshots independently authenticated. Package207/207 TTC retained. LocalDiamond unchanged and fresh PASS490.233s; sampled peak50,598,096KiB (48.254105GiB) under52GiB, shared lock acquired/released. Default48GiB elsewhere; samples are not OS high-water. Census4=1/2/0/0/1; production diff vs34b21c9 empty, CP3blob2c697e532e83989de8591fa6a4378747c6a501c0. No own compiler, no staged files, clean tracked tree at the pre-publication audit.12 evidence-contract tests PASS.

A26/B16 caps and parked boundary were explicitly ratified before validation.
The root-contract manifest was accepted as R196 execution BASIS, not executed
in R195. Its helper checks require per-helper classification:52GiB ONLY for
LocalDiamond unchanged or FIELD/KEYWORD-only; every other module48GiB unless
its own measured historical peak exceeds40GiB and its gate names that peak and
requested limit. Unknown costs use serialized48GiB and a per-module record.
No blanket exception or lane2 rebuild-window reservation.

The original vestigial mismatch lemma SELECTS/RETAINS the authenticated FULL
alternative in CurrentEndpointRenaming; it is not a construction from history
alone. The obstruction packet does not package independent canonical capital
or claim all canonical metatheorem premises. No whole pairing/canonical cut/
bridge producer or body was added. Source remains3bd99171.

See O6-R195-VERIFICATION, compiler ledger/archive, frozen/independent/resource
reports and findings. Evidence archive is pinned to the pre-publication anchor;
its own artifact receipt and future gate note are not self-referentially claimed.
Supervisor FINAL gate and independent parent-owned reviewer are pending.

## R195 owner FINAL gate — checked PARTIAL ratified

Verbatim supervisor ruling after committed evidence d7b2fc98 and current-head
read-only frozen/independent PASS audits:

> R195 FINAL GATE RULING: ACCEPTED — checked PARTIAL milestone RATIFIED at d7b2fc98; artifact-only D3 gate note and clean close PERMITTED. Supervisor verified independently: HEAD d7b2fc98, 48 commits over 981e6137, clean tree (baseline untracked only), production diff vs 34b21c9 empty, LocalDiamond/O19Surface/CrossTrace/RenamingComposition/CanonicalSort/DeletionChain and the two lane-shared baseline modules byte-identical to 981e6137, independent census 4 = 1/2/0/0/1, 16 R195 artifacts, pushed. Accepted as stated: A26 (root replay-ordinal necessity witness → structural park; generation-only E8 disposition for every original generated birth carried through any actual occurrence correspondence with the physical ordinal law retained; no whole paired fold), B16 (strengthened ORIGINAL-scope fixture with owned all-name internal cut and Void from the current-map cut; full original VestigialEndpointGeneration derived; removed-child absence; no canonical/replayed all-name rebasing), D1/D2 docs, the root-contract manifest as R196's DOCS-ONLY basis, 65/65 validations with the unchanged LocalDiamond at 48.25 GiB under the 52 GiB rule and the per-helper classification recorded. Exact debts noted verbatim. Independent reviewer is being launched now. Stand down cleanly after the note.

This is the permitted D3 ARTIFACT-ONLY note. No further Idris/source/compiler
work followed the ruling. Independent reviewer is parent-owned and pending;
ratification is not a claim of reviewer acceptance or convergence completion.
Archive remains pinned21269c8e, with its own/later receipt exclusion explicit.
D4 unused; no further work planned in this bounded R195 shift.

## Status — R195 final checked PARTIAL handoff

Fully proved locally: root-law identity/composition/conditional attachment and
necessity witness; whole original generated-birth disposition/occurrence-replay
retention and generated ordinal attachment; native identity all-name/history
cuts; complete original-scope rebasing obstruction; authenticated original
vestigial-alternative selection and actual removed-child absence.

Partial/stated: canonical/operational storing root contract (precise docs-only
R196 basis), whole accepted paired-stage/history fold, canonical vestigial and
opposite-image absence/current-map all-name controls, exact D5 bridge and O21
endpoint assembly. All four inherited holes remain; C had0 attempts. No new
escape hatch or production/statement/lane-owned source delta.

Checked:42 source receipts,65/65 final expected validations,112 total records,
12 evidence tests,207/207 seeds; frozen/independent/resource audits PASS.
Owner final gate ratifiedd7b2fc98. Next is parent-owned independent review and
R196's explicit per-helper root-contract/resource gate, not an R195 extension.
Standing down cleanly after this note; independent reviewer acceptance unclaimed.


## Status — R196 checked root-contract and actual root-law milestone

Source freeze1fd9bbcb60bfb3168ebc001d33d908377268fbd2. Research-only; production
src/ + dgamma.ipkg remain byte-identical to34b21c9, CP3 blob
2c697e532e83989de8591fa6a4378747c6a501c0. No new hole, unsafe escape, postulate,
partial function, scoped-to-raw cast or frozen deletionTheoremProof call.

**Fully proved:** both exact R195 proposed erased storing contracts and their
ACTUAL producer fills. `adjacentOriginRootOrdinal` uses the existing all-action
ordinal relation at the same origin. Deletion uses the same ordinal segments
and spine witness. R19's empty root domain is discharged by its actual two
Advance occurrences. The additional owner-gated opaque erased helper
`deletionBuiltRootOrdinalPreserved` unfolds only the private action origin in
its defining module and projects the same stored capital's root law.

The new CP5O20RootReplayLawProducerSpike proves root laws for actual finite
adjacent derivations, built/exact stored deletion correspondences, the whole
deletion derivation, the EXACT `canonicalOccurrenceCorrespondence capital`,
actual operational permutations and their canonical composition. The final
`o20PermutedCanonicalRootReplayOrdinals` attaches the law to the literal
composition of `canonicalOccurrenceCorrespondence leftCapital` with
`permutationOccurrenceCorrespondence execution`. No new root-law hypothesis or
freely supplied occurrence map enters these consumers. The generic ARRC record
is unchanged; r195ReplayRecordDoesNotOwnRootLaw remains a checked necessity
witness, not a protected-convergence counterexample.

**Still partial/open:** whole accepted paired-stage/history extraction, actual
root/opposite occurrence pairing, canonical vestigial/opposite-image absence,
all-name endpoint rebasing under the expected/current bijection, the D5 bridge
and O21 assembly. No whole paired-stage fold or bridge/body attempt occurred:
C's ten invocation slots were used by the root-law chain, including its one
private-definition rejection and the required defining-module helper check.
R195's generation-only history disposition is available for that NEXT fold;
root laws do not themselves produce paired stages or an all-name cut.
Census remains4=1/2/0/0/1, with all four inherited hole statements unchanged.

**New frozen baselines:** LocalDiamond
9f9216170853624cff30449696f2540da0ed48e0b42504533aa587cb70dfc037;
DeletionChain91e8fd290cc4fedae9656ce5b4ae3ea0b38509f6e0250f51b4a7aa2aea09067b
(the earlier successful A4-only7fadaf6b baseline is superseded by the separately
approved C3 helper). Every other byte is protected by the exact execution,
syntax-amendment and C3 helper manifests. O19 closed declaration/body1286B SHA
cbd0954303c35141af0309e515bdb9e98e988e7c23be70b9764d8c1ce18fd396 unchanged;
adjacent1470B SHA2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf
and1154B statement SHA3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf
unchanged. A11's R192 manifest and all other protected source bodies stay frozen.

**Evidence/protocol:** Unit A:5 native invocations=4PASS/1 parser rejection;
Unit C:10=9PASS/1 private-definition rejection. Thirteen immediate guarded source commits.
B's corrected import-closed133/133 acceptance slots and the second helper
window127/127 slots PASS. Together with A these cover all inherited65 targets,
the five spikes, R8/R16, ReachedBlocks, both all-four fixtures and two
seeded207/207 package checks. Original B1 is separately REJECTED because it also built an excluded
R45 prerequisite: a planning/one-source contract defect, not a resource stop.
Its same-hash B1R1 follows a direct R45 check under the explicit owner ruling.
Total276 native invocations=273 expected PASS/3 preserved rejections, no RSS
stop, source mutation or interruption. Eighteen noncompiler evidence tests PASS.
Both continuous windows were released; C consumers used per-check shared locks.
No lane2 compiler was killed and no lane worktree was entered/edited/built.

The refreshed O6-R196-ROOT-CONTRACT-COSTS.json covers the inherited244 inventory
entries plus the newly added root consumer.100 unclassified fixtures and11
legacy R11 targets remain stale/not re-checked by explicit path; no245-PASS
claim. Samples are not OS high-water; zero means no captured live sample.
B6 CP5UniqueRawNameOrdinalCapital newly measured44,790,080KiB (~42.715GiB),
so a future repeat needs its OWN >40GiB resource gate. LocalDiamond's approved
52GiB checks peaked50,611,312KiB; all other checks stayed48GiB. No blanket52GiB
exception and no from-scratch rebuild or seed deletion.

**Later-shift lane2 candidate only:** "observed retired-head guard at the source".
This owner-supplied lifecycle-replay note is recorded for later main-lane work;
R196 did not implement it or certify lane2's ongoing results. Only unchanged
inherited MAIN variant modules were validated. Next: use the now-owned root
laws with actual original root correspondence and R195's generation-only
history to build real paired stages, then resolve the canonical all-name cut.
Owner final gate and parent-owned independent reviewer remain pending here.


## R196 owner FINAL gate — checked PARTIAL ratified

Verbatim supervisor ruling after committed794719a5 and strict post-publication
read-only frozen/independent/archive PASS verification:

> R196 FINAL GATE RULING: ACCEPTED — checked PARTIAL milestone RATIFIED at 794719a5 (root-contract + exact root-law consumer milestone COMPLETE); artifact-only D4 gate note and clean close PERMITTED; no need to stay active to the boundary. Supervisor verified independently: HEAD 794719a5, 16 commits over 58f88c63, clean tree (baseline untracked only), production diff vs 34b21c9 empty, LocalDiamond SHA 9f921617… and DeletionChain SHA 91e8fd29… (new frozen baselines) confirmed by direct hashing, O19Surface/CrossTrace/RenamingComposition/CanonicalSort byte-identical to 58f88c63, independent census 4 = 1/2/0/0/1, 21 R196 artifacts, pushed. Accepted as stated: A (helper + two erased root-law fields + fixture fill; exact approved diffs; O19 body / adjacentSwapSuffixSpike hashes unchanged), B (import-closed 133/133 + second window 127/127; 135 applicable modules + package; 100 unclassified + 11 legacy stale by path; B6 42.7 GiB datum; no resource stops), C (C6 exact canonical law, C7/C8 operational fold + composition, C9 exact permuted composition — no root-law premise; whole paired fold not attempted), D docs, resource/lock audit. The two observed idris2 processes are lane 2's / wrappers (separate worktree). Independent reviewer is being launched now. Stand down cleanly after the note.

This is the permitted D4 ARTIFACT-ONLY gate note. No further Idris/proof-source
or compiler work followed the ruling. A/C caps remain binding; whole paired
fold and endpoint bridge remain open. The archive stays pinned to1fd9bbcb and
does not claim its own/later artifact receipts. Parent-owned independent review
is pending; owner ratification is not reviewer acceptance or Theorem73 closure.
D4/4 used. Clean close is expressly authorized before the four-hour boundary.


## Status — R197 source-frozen checked PARTIAL milestone

Source freeze e1f608cb; 33 retained declarations (A26 + D7), each freshly
checked and immediately Python-guarded committed. A used30 invocations,
D14, plus S0 baseline1:45 total,34 expected PASS,11 preserved rejections.
No B/C proof invocation; no resource/mutation stop. Final144-check validation
has not run yet at this entry. All compiler work is seeded, detached, monitored,
main-worktree-scoped; ALL invocations acquire/release the shared heavy lock.
Samples0 mean no live sample, not zero memory. Toolchain Idris2 v0.8.0.

### Fully proved capital (not global convergence)

A1–A13 construct an actual opposite original external root and its physical
ordinal equation simultaneously, retain it through native replay, then attach
the SAME canonical right occurrence to both its original origin and the
conjugated physical ordinal. They consume R196 C6/C9 and original right raw
insertion uniqueness, not an opposite-birth/root-equation premise. Root names
absent historically are not silently identified with an endpoint-only map.

Owner explicitly rescoped A14–A26 to a conditional fold and boundary probes.
`O20StampedStage` has actual Begin, Advance, empty Finish, Insert, Retire,
Remove constructors: actual native checks, insertion stamp equation, exact
live-map updates and removal uniqueness. `o20StampedStageCut` produces the
successor cut; no output cut/preservation callback is an input.
`O20StampedHistory` and `o20StampedHistoryCut` perform total finite induction
and return existing `O20HistoryCut` with all-name runtime and BOTH historical
clauses. They are **conditional on a supplied stage synchronization; not
universal pairing**. Epsilon admits only literal same-cut zero-edge paths,
never removal of an unmatched insertion, retirement, or other native edge.

The positive eleven-edge R191 run has actual root stamps0/1/2 and child stamp4;
its endpoint cut is obtained by the fold from empty origin, not supplied.
R193/R195's present vestigial original history remains present through honest
zero-edge epsilon. Root and child-closing alternatives stay paired at one
actual origin. R178's differing child-role words satisfy unary paper-role
classification but FAIL accepted E9 for every generation bijection; this is
not an accepted canonical-capital or convergence counterexample.

D1/D2/D4/D3 prove `providerHeadObserved`: one runtime observed Bool, its native
head guard equation, and both providerIn head equations before/after setting
the retired flag True. The TYPE was read only by approved `git show` at
94273eaab85e4edf0145027418fb0f1c387bb824, not from lane2's worktree. D2 eliminates
an explicit observed Bool with its own guard equation; D4 eliminates that Bool
BEFORE constructing the packet; D3 supplies the actual native guard with its
own equation at the call site. D3 passed its LAST authorized attempt3 after
D4 was separately checked/committed; its signature was unchanged. D6's generic
Bool branch-equation eliminator is independently checked. D7/D8 are actual
TWO-binding active-head and inactive-head/live-tail producer fixtures.

### Partial/stated work and exact next obligations

`O20HistorySynchronization` is UNPRODUCED endpoint/scanner capital, owning a
paired native path between the supplied endpoints and actual final scan
maps. It does NOT assert literal equality of its reconstructed paths to the
two supplied words. `o20CanonicalSynchronizationGoal` is only a total erased
function returning this Type for accepted canonical/replayed inputs at the
actual conjugated generation map. It is not an inhabitant, postulate, hidden
oracle, or new TODO hole. Named missing producer:
`o20SynchronizeCanonicalHistories : o20CanonicalSynchronizationGoal …`.
Actual whole-word extraction needs stronger trace alignment as well.

B eligibility stops there by owner ruling. Additionally, ORIGINAL-scope
`VestigialEndpointGeneration`/closing-retention packets do not produce the
exact canonical/replayed all-name `MaybeFiber` controls under
`expectedBridgeBijection`. Both this rebasing and the actual bridge remain
unproved, even were the synchronization supplied. C is ineligible,0 attempts;
no protected convergence, selector, O17/O21, adjacent or O19 body was edited.

D5 generic packet-consumer failed3/3 and was FULLY reverted to D6 commit
8deec075. Its last approved signature exposed the SAME packet's observed Bool
and its own erased field equation; even explicit replacement of the projected
field rejected two syntactically identical displayed `if` types under
`--show-implicits`. Full error/snapshots/rollback hash are retained in
`O6-R197-D5-STOP-AUDIT.md` and the evidence archive. No fourth/renamed/shrunken
retry, unsafe escape, partial definition, or new hole. Owner diagnosis:
Idris2 v0.8.0 conversion-check wall; lazy Delay desugaring is a possibility,
NOT established internals. Future work may split the producer packet before
projected-guard field types arise, or investigate the compiler. R197 DOES NOT
advertise a generic retirement equality consumer as proved.

### Scope, guards and validation plan

Fresh source-freeze audit: production vs34b21c9 empty; CP3 blob
2c697e532e83989de8591fa6a4378747c6a501c0; all five frozen theorem modules and
O19 unchanged from e2ebe3b5. LocalDiamond9f921617…/DeletionChain91e8fd29…,
O19 body and adjacent statement/body hashes unchanged. Census4=1/2/0/0/1.
All seven source changes are NEW research modules, `%default total`, with no
unsafe escapes/holes/with/let aliases/binder prefix. No lane-owned source edit.

Final plan is immutable and covers ALL R196135 applicable baseline sources
PLUS its late root-law consumer =136 inherited current paths, all present;
seven new paths produce143 source checks + seeded package =144 invocations.
Seven inherited expected-negative checks keep their exact diagnostics/symbols.
Import closure is checked within the inherited245-source invalidation inventory
plus new targets, matching R196's seeded discipline. Unchanged prerequisites
OUTSIDE that inventory (e.g. RankObservation) are source-pinned reused seeds,
NOT called freshly checked. A compiler-free initial plan preflight over the
entire repository import universe was overly broad and rejected that seed;
no plan/native compiler was created before the corrected domain passed.

E2 tightens existing own-Building checks to reject duplicate own lines and
same-module/different-path lines, records runner/plan SHA, and logs heavy-lock
waits. Optional --show-implicits was used only on retained rejected/repair
attempts as shown in their immutable command records.18 compiler-free
adversarial evidence tests pass. No old validation is relabelled as R197 PASS.
Default48GiB; byte-frozen LocalDiamond52GiB only. UniqueRawNameOrdinal remains
unchanged and runs under the explicit48GiB owner gate (prior42.715GiB sample).

Next: finish all144 frozen checks, publish/authenticate full ledger/receipts/
archive/frozen/resource evidence, then owner gate and independent reviewer.
Do not attempt more proof work this shift or widen the protected premises.


### R197 source-audit qualifications during frozen validation

The stamped family is LOCKSTEP: every paired stage increments both physical
offsets, and its only epsilon consumes zero native edges on both sides.
Universal adequacy for accepted schedules is therefore a separate OPEN
obligation, not supplied by either the root attachments or the Type-valued
goal. A richer asymmetric/role synchronization may be needed; no accepted
counterexample or universal impossibility theorem is claimed here.

A broader compiler-free topology audit additionally verifies EVERY direct
import between the144 planned targets, including three edges to the two
inherited baseline variants outside the245-entry invalidation inventory.
All are already ordered correctly; the immutable plan was NOT rewritten.
Those two variants are themselves direct final targets (not among the111
unvalidated inventory paths). “Outside-domain reused seed” does not deny a
separate direct fresh check explicitly listed for such a target.


## Status — R197 final checked PARTIAL (compiler-free resumed publication)

**Fully proved within their stated inputs:** A's actual opposite-root/original-
ordinal and canonical/permuted attachment; six-role stamped stage preservation
and finite conditional history-cut fold; genuine eleven-edge/closing-history/
role-boundary fixtures; D's executable observed-head provider producer, native
observed-Bool equation and packet assembly, generic Bool branch eliminator,
and two-binding active/inactive-head fixtures.33 retained declarations in7 new
research modules, each immediately committed from its fresh own-source PASS.

**Partial/unproduced:** universal/whole-word stage synchronization and its
adequacy (the family is lockstep, zero-edge epsilon only); expected-map
canonical/replayed all-name MaybeFiber endpoint rebasing and D5 bridge; global
convergence body C ineligible,0 attempts. The exact synchronization goal is
only an erased Type function, not an inhabitant/postulate. D5's OPTIONAL
same-packet retirement-equality consumer exhausted3/3 and was fully reverted;
its identical-looking projected-if conversion error remains verbatim.

**Validation complete:**144/144 immutable-plan expected outcomes, including7
exact expected-negative source checks and a seeded package invocation. All136
inherited applicable current R196 source targets +7 new=143 source paths; no
applicable path omitted. Full ledger189 invocations=178 expected PASS+11
honest rejections.33 authenticated source receipts;18 compiler-free adversarial
guard tests pass. Every compiler lifetime is covered by a non-overlapping
shared-lock interval. No source/resource interruption or extra Building line.
LocalDiamond50,615,728KiB (~48.272GiB) under52GiB; UniqueOrdinal44,692,640KiB
(~42.622GiB) under48GiB. RSS is one-second sampling, NOT OS high-water;0 means
no captured live sample.141/252 inventory entries rechecked, plus2 directly
checked inherited baseline variants outside that inventory=143;100 unclassified
and11 legacy inventory paths remain NOT freshly checked. No cold-build claim.

Frozen/census authentication passes: production vs34b21c9 empty; CP3 blob
2c697e532e83989de8591fa6a4378747c6a501c0; LocalDiamond
9f9216170853624cff30449696f2540da0ed48e0b42504533aa587cb70dfc037 and
DeletionChain91e8fd290cc4fedae9656ce5b4ae3ea0b38509f6e0250f51b4a7aa2aea09067b;
all other protected module/declaration and O19/adjacent hashes unchanged.
Census4=1/2/0/0/1. No new unsafe escape, hole, partial function, with/let alias,
binder prefix, source API widening, or lane-owned edit.

The detached run finished08:15:37Z before any native cutoff. A provider usage
limit interrupted the interactive session, not the compiler work. The owner
reset the limit and supervisor explicitly revived only E3 artifacts and final
gate, declaring proof work closed. Printed publication UTC08:38 is earlier
than the recorded09:38 proof/10:03 gate bounds, so a missed UTC deadline is NOT
asserted. No clock extension, native rerun or source edit is claimed. The
archive resume note originally conflated the closed-work instruction with UTC
lateness; O6-R197-TIMING-QUALIFICATION.json explicitly corrects that NON-NATIVE
note without rewriting the archive. Archive anchors precede later receipts to avoid circular
self-attestation. Machine verification is not independent human proof review.

**Next:** owner/reviewer gate; future separately authorized whole-word/asymmetric
synchronization adequacy and producer, exact all-name rebasing, then bridge.
C remains barred until those producers exist. D5 may need a producer boundary
avoiding projected-if types or compiler investigation, never a fourth R197
retry. No further proof work in this shift.


## R197 owner FINAL gate — checked PARTIAL ratified

Owner ACCEPTED checked PARTIAL at3a42d1f2 and authorized this E4 artifact-only
note/clean close; E3 was pushed by the supervisor. Exact ruling is preserved
in `research-tests/O6-R197-OWNER-FINAL-GATE.md`. A remains conditional, B's two
named producers/bridge OPEN, C0/ineligible, D5 generic consumer STOP3/3/reverted.
144/144 expected validation outcomes and unchanged4=1/2/0/0/1 census stand.
Independent human review is parent-owned and begins after E4; it is not
claimed complete. No further source/native work, clock extension or archive
rewrite. The revival proof window was closed by ruling, not a proved missed
UTC deadline. E4 closes this authorized shift cleanly.


## Status

### R198 source freeze — checked PARTIAL, final validation pending

41 total new declarations in7 research-only modules (A25 retained/26 units,
33 compiler invocations; B16 retained/16 first-attempt invocations). A3 native
repeated-tag path STOP3/3, reverted; only its parent/candidate cuts remain.
A20 includes a real PASS rejected by whitespace commit guard, then a fresh
whitespace-only PASS. No unsafe escape, new hole, partial function or production
change. Census stays4=1/2/0/0/1; all protected bytes and R197 D5 remain frozen.

**Fully proved:** old stamped goal forces final-live birth-ordinal preservation,
including authentic scan attachment. Owner-approved new occurrence-stamped
native family, finite cut fold and exact-conjugated conditional history-cut
consumer. R191 eleven-edge actual identity path+two scans; R193/R195 closing
retention at a zero-edge terminal path. Native projections and their equal
counts (NOT the supplied words' count equality). Executable all-name ONE-TRACE
original/canonical MaybeFiber observation with erased exact equations and
explicit observed library decision; actual canonical and operational-replayed
absence from original absence; current-map removed controls conditional on BOTH
original absences. Raw closing-identity boundary fixture is NOT canonical capital.

**Partial / merely typed:** `o20CanonicalSynchronizationGoalModulo` is a new
TYPE, not a producer. Whole-word/per-actor coverage/order and exchange are not
supplied by the family and remain debt. The new fold yields internal history
cuts, not all-name current-name rebasing. B still needs actual canonical
vestigial disappearance and opposite CURRENT-image canonical absence; R194
non-vestigial agreement cannot discharge those. The convergence hole is untouched;
C0/ineligible. No exact all-name cut or D5 bridge by fiat, and no D5 retry.

**Research-spec deviation:** owner activated the new unprotected occurrence
specification after the old-goal necessity theorem, without a successful full
accepted shuffle countermodel. Old goal/fold remain byte-unchanged superseded
candidates. The failed native fixture is a proof-origin representation seam,
not an input rejection or paper/convergence counterexample. The new family
attaches actual word occurrences, but does NOT encode ordered whole-word
coverage. Arbitrary skips are NOT asserted to be zero native edges.

**Boundary discovery:** the RAW `CanonicalEndpointRelation` permits empty-
withdrawal identity at the actual present-vestigial R193 original endpoint.
Thus that endpoint predicate alone cannot establish vestigial disappearance;
the literal canonical construction must produce it. This is not a compiled
countermodel of accepted `IndependentCanonicalSchedule` capital.

**Validation pending at D1:** immutable151-check plan = ALL143 inherited current
sources +7 new + seeded package,7 exact expected negatives, no absent exclusions.
21 guard tests and pre-validation51-record/41-source-receipt/frozen/resource
machine audits pass. Machine authentication is not independent human review.
See R198 audit, synchronization/ruling and canonical-controls analyses. Next:
finish final validation/archive/reviewer gate; future separately authorized A
producer and B missing lemmas, then bridge and only then C. No self-extension.


### R198 final validation complete — D2 checked PARTIAL

Final validation ended10:51:21Z:151/151 expected outcomes (ALL143 inherited
main sources +7 new + seeded package,7 exact negatives, no exclusions).
202 native invocations overall:195 expected PASS (188 exit0 +7 negatives),7
rejected snapshots;41 source receipts;21 guard tests. Independent machine
source/log/receipt/plan/resource/frozen authentication PASS. Source commits
retain every prior code line. No resource/mutation/extra-Building/lock-wait or
stale-removal event. Samples50,540,272KiB LocalDiamond<52GiB and44,786,256KiB
other/Unique<48GiB; zero samples are not zero actual memory. NOT a cold build.

No proof status changed: A is a conditional occurrence fold/TYPE, not an
accepted-input synchronization producer; B has executable observations and
actual absence transport, not the present-vestigial/current-image all-name
producer or bridge. C0; D5 still exhausted; all four frozen holes unchanged.
D2/4 closes validation. Next D3 archive and D4 verification/owner/reviewer gate;
no further source/native work or self-extension. Machine authentication is
not independent human review.


### R198 archive published/verified — D3

Append-only archive anchored at5887867f:SHA256
05e1fef0ec134fb00b1235dc237864b2314baf433b3865d2031e90d9cc9abc51,
1,162,349 bytes/1042 files. Read-only full-byte/native-record/receipt verification
PASS;202 snapshots+logs,41 source/5 pre-publication artifact receipts,151 final
checks, all7 rejections retained. Complete259-entry cost inventory honestly
marks148 directly checked entries +2 auxiliary paths and111 unvalidated legacy/
unclassified entries. Archive anchor excludes its own/future publication/gate
receipts; no circular attestation. Main A/B debts and C0 unchanged. D3/4;
D4 final machine/owner/reviewer gate only. No further source/native work.


## R198 owner FINAL gate — D4 clean close

Owner ACCEPTED checked PARTIAL atbe6addfb and authorized D4 artifact-only close;
owner reports pushingbe6addfb. Verbatim ruling:
`research-tests/O6-R198-OWNER-FINAL-GATE.md`. Post-D3 independent machine audit
PASS authenticates202 native records,41 source +6 artifact receipts,151 final
checks; full1042-file archive verification PASS; tracked tree clean, baseline
untracked only, no staged files/main compiler/lock, unchanged frozen census
4=1/2/0/0/1 and production. D4 itself is outside those prior receipt/anchor counts.

A synchronization/coverage/exchange producer and B present-vestigial/current-
image all-name rebase remain OPEN; C0, no D5 bridge/retry. All41 retained source
declarations are within the parent's read-only review scope ≤be6addfb. Human
review is being launched by the parent, NOT claimed finished. D4 adds no source,
native invocation, new proof claim, archive rewrite or clock extension. D4/4;
stand down cleanly. Any further proof work requires a separate owner task.

## Status

### R199 source-frozen checked PARTIAL (D1)

44 new declarations/7 new modules; A26 units/31 calls, B18 units/21 calls,
C0/ineligible. All proofs typechecked before guarded commits;7 failed snapshots
retained. B3 has an additional genuine PASS rejected by EOF-whitespace guard,
then a fresh whitespace-only check. No exhausted/reverted micro-unit. No new
hole/postulate/unsafe/partial/with/let/prefix, no production/frozen-source edit.

Fully proved: own-trace canonical role coverage/order; accepted shared Begin
component/program; whole actor-body consumption/frame invariant; accepted
AUGMENTED per-actor word equality. Not proved: actual end remainders empty,
generated Insert alignment, ordered occurrence-labelled whole histories and
exchange. The requested universal modulo synchronization remains unimplemented.

B proves exact accepted/deletion current-table agreement using PUBLIC bilateral
scanner induction. Frozen private helpers required standalone public counterparts;
B6's private-type attempt failed, repaired by direct public-constructor induction.
Full present-vestigial packets have BOTH current/discarded environments from one
accepted original scan. For generations selected at the ACTUAL first deletion
node, native deletion owns disappearance and its whole remaining chain, sorting
and operational replay preserve it. **Head selection membership remains a premise**;
global discarded-to-selection coverage and later-node transport are not supplied.
The mixed head-vestigial/original-absent current-map class is proved. Universal
all-name rebase/bridge remains open; D5 bridge not applied; C unchanged.

Fixtures apply the native actor fold to unchanged R191/R193 cuts and produce full
actual R193/R192 generation scans. R193's canonical current-map boundary still
requires independent capital/permutation and head membership; it is NOT fabricated
canonical capital or an unconditional convergence instance. Existing four-hole
census4=1/2/0/0/1 unchanged. No new merely-stated theorem/hole introduced.

21 evidence tests and53-record source/receipt/lock audits pass. Final158-check
plan =150 inherited +7 new sources + seeded package,7 exact expected negatives,
no exclusions; validation pending at D1. Next: validation/archive/owner/reviewer
closure, then separately authorized proof work on the exact A/B debts. No scope
or clock extension. Machine verification is not independent human proof review.


### R199 final validation complete — D2 checked PARTIAL

158/158 planned outcomes PASS by13:01:05Z: ALL150 inherited sources +7 new +
seeded package (7 exact expected negatives).211 total invocations,204 expected
PASS,7 retained failed attempts;44 guarded source commits;28 distinct guard/
policy tests. Independent machine source/log/receipt/plan/frozen/resource checks
PASS. Production/frozen bytes and4=1/2/0/0/1 frontier unchanged. No new holes,
unsafe escapes or source changes after the a240d372 proof freeze.

Owner abolished the cross-lane lock mid-validation: V11 finished/released its
old lock normally, then the SAME immutable plan continued at V12 with no shared
lock operations or repeated checks. One compiler per lane and52/48GiB own RSS
guards remain; overlap observations are timestamps only. This was an authorized
scheduler-policy continuation, not a task/proof restart or clock extension.

A's universal occurrence synchronization and B's exhaustive vestigial selection/
all-name rebase remain OPEN; new word equality retains end remainders, and B's
head-selection membership remains explicit. D5 bridge uncalled; C0/ineligible.
D3 archive and D4 owner/clean close remain; required human review is parent-owned
and NOT claimed complete. See the R199 audit, verification and owner-policy files.


## R199 D3 — append-only archive published and verified

Archive anchor `4987a366df85a9d33e89c8e4baaed62ac129a150`; SHA256
`b10faf5e75b57f53dd7f17d6f287c2a4df461e6c4dc072f29941f990a1c9dd8a`; 1,229,236 bytes,
1104 regular files. Full read-only archive authentication PASS:
211 native records/source snapshots/raw logs,44 source receipts,3 historical
artifact receipts,158 final outcomes and all7 rejected snapshots. The archive
also authenticates the explicit owner policy transition and old/new runner
boundary. Its own/future publication and gate receipts are intentionally outside
its anchor, not circularly asserted inside it.

The refreshed266-entry inventory marks155 directly checked inventory entries
plus2 auxiliary inherited sources =157 source targets.111 excluded legacy/
unclassified inventory entries remain NOT rechecked. Future cross-lane heavy-
lock flags are false under the owner ruling; older per-check lock use is retained
as historical, not rewritten. No archive replacement, source/native work or
clock extension. D3/4; final owner D4 gate/clean close remains. Independent human
review is parent-owned and not claimed complete.

Mathematical status remains checked PARTIAL: A universal ordered occurrence
synchronization, B exhaustive vestigial selection/all-name rebase and bridge
remain OPEN. Head-selection membership and augmented-word end remainders remain
explicit; conditional canonical fixtures are not fabricated capital. C0.


## R199 owner FINAL gate — D4 clean close

Owner ACCEPTED checked PARTIAL at a7e44e75 and authorized D4 artifact-only close;
owner reports pushing that commit. Verbatim ruling:
`research-tests/O6-R199-OWNER-FINAL-GATE.md`. Post-D3 source/log/receipt/plan/
frozen/policy machine audits and1104-file archive authentication PASS:211 native
records,44 source +4 prior artifact receipts,158 final expected outcomes. D4 is
outside those earlier receipt/anchor counts. No production/frozen-source change,
new hole, archive replacement, native invocation or clock extension in D4.

A remains AUGMENTED-word capital, not universal occurrence synchronization;
B remains head-selected disappearance/mixed name-class capital, not exhaustive
global discarded coverage/all-name rebase or bridge. Conditional R193 capital
stays explicit; C0/ineligible. One compiler per lane and52/48GiB RSS guards remain;
owner's cross-lane lock abolition remains effective. Required independent read-
only human review is being launched by the parent scoped to ≤a7e44e75 and is
NOT claimed complete. All44 source additions are already within that scope.
D4/4; stand down cleanly. Any further proof work requires a separate owner task.

## Status — R200 checked PARTIAL (source freeze; validation pending)

R200 main baseline `60869648`, source freeze `5ca8e587`; **B24/24 then A20/20**,
all44 native micro-units PASS on attempt1, each immediately guarded-committed.
No failed/exhausted micro-unit or new hole/escape hatch. All new modules use
`%default total`; theorem fields and occurrence certificates are erased.
Production `src/` and `dgamma.ipkg` remain byte-identical to `34b21c9`.
The frozen five-module census is still **4 = 1/2/0/0/1**. No O17/O21 work or
frozen deletion theorem call; lane-owned sources and all protected declarations
remain byte-identical to the accepted baseline.

### Fully proved capital (not the whole O20 theorem)

- B: `o20ClosingFreeDiscardedEmpty` and `o20ClosingFreeNoPresentVestigial`
  establish the actual accepted scanner's closing-free empty-origin base.
  `o20AcceptedDiscardedBirthClassified` reverses the entire bilateral scanner:
  every discarded generation has its exact original birth and a later parent
  Unload. `o20UnselectedVestigialStillPresent` derives actual-node target presence
  and controls for an unselected current vestigial packet. The R193/R195 native
  eight-edge fixture authenticates the base contradiction and reverse classifier.
- A: `o20LocatedBlockEndRemainderEmpty` applies to EVERY actual aligned located
  open block, using its own final Active field and no-later-lifecycle suffix.
  The induction handles real owner Insert/Retire/Remove and foreign actions;
  it does not assume an empty suffix. `o20SelectedCanonicalRoleWords` consequently
  removes both residuals from R199's accepted paired-block equation, yielding
  plain lifecycle-role-word equality. All three actual R191 blocks instantiate
  the endpoint theorem, including nonempty later suffixes.
- A: `o20SupportedCanonicalInsertPositions` produces both authentic ORIGINAL
  scanner Insert occurrences, their exact mapped generation and per-parent-
  activation position equality for a canonical birth supported at its original
  endpoint. These positions are NOT exchanged-canonical trace positions, and
  the erased packet does not itself assert a runtime cut or support predicate.

### Partial / merely requested next

B is NOT global discarded-to-selected coverage. The exact missing semantic
transport is **`o20DeletionRetainedClosingBirth`**: an original deleted-birth
classification must survive a nonselecting actual deletion, in that result's
`generationForward` coordinates, retaining a genuine later parent Unload.
Present controls alone do not transport current/discarded generation indices
or that history. Only after this can induction prove membership in the actual
`closingFreeDeletionGenerations` (head selections plus backward-rebased tail).
Thus global `everyPresentVestigialSelected`, both-sided supported/present-
unsupported/removed ALL-NAME rebase, endpoint `O20AllNameCut`, and the D5
`ReplayedCanonicalEndpointBridge` producer remain OPEN. Existing first-selected
R199 disappearance is not misrepresented as global some-node coverage.

A is NOT occurrence-stamped history synchronization. Lifecycle words omit
physical yielded Inserts. Original E8 positions still need transport/attachment
to real exchanged canonical Insert occurrences, with true one-sided occurrence
witnesses for skips; paired blocks then need whole orchestration-order histories.
`o20SynchronizeCanonicalHistoriesModulo` remains OPEN. No new source theorem
statement or hole was added for these missing producers. C has **zero attempts**:
`canonicalSchedulesConvergeSpike` cannot be attempted until BOTH A and B close.
The old lockstep goal and old scalar/one-origin exhausted seams were not retried.

### Authorized comment correction and validation discipline

R199 ACCEPT-WITH-NOTES P2 authorized only the docstring of
`o20SelectedVestigialDisappears`: it CONSUMES the actual deletion result and
produces table reconciliation and absence. Its signature/body and the chain's
construction-owned result claim are unchanged. Whole-file SHA256 before:
`ee4f73c2427bdca5b34e266710660c8a0c3daa9c6a5283f00c3c0dc59aa4152c`;
after: `550fa9472bdf9b1366d59e8417ee26821e4d61fd2a1b926ea40857c1124b9315`.
Fresh own-target `D1-COMMENT` PASS4.174s, one Building line, sampled4,253,664KiB,
no mutation/resource stop; guarded commit `5ca8e587` checks the exact authorized
replacement and non-doc identity. See `O6-R200-COMMENT-CORRECTION.json`.

The immutable final plan covers **ALL157 inherited R199 sources +8 new =165
sources, plus seeded package =166 checks**, including the changed inherited
comment target, seven exact expected negatives, R8/R16 and R191/R193/R195
fixtures. No inherited source is excluded by path. Validation is pending here,
not a claimed PASS. It is seeded/import-closed, NOT a cold build or certification
of all274 inventory entries. No lock paths are inspected, acquired or removed;
only one main compiler runs, with timestamp-only cross-lane overlaps and own
RSS guards (48GiB, byte-frozen LocalDiamond52GiB). Evidence tests21+7 PASS.
Next after validation/audit: reviewer gate for PARTIAL capital, then producer-
owned historical transport in B and physical Insert attachment/whole folds in A.


## Status

### R200 D3 final checked PARTIAL

Full validation completed14:53:22Z: ALL157 inherited+8 new=165 source checks plus
seeded package166, seven exact expected negatives;212/212 shift invocations met
expectations.42 proved functions+2 indexed families, no failed micro-unit, no
new hole/escape. The sole inherited Idris change is the exact authorized
comment correction, not a theorem/body revision. Source/log/commit/immutable-
plan/resource/frozen and archive machine authentication PASS; independent human
review remains required. Full statistics and archive hash are in the R200 audit.

Proved: actual closing-free scanner base, reverse discarded-birth origin,
nonselecting-node presence/controls, universal actual block-end residual
elimination, plain selected-pair lifecycle words, and supported ORIGINAL Insert
position packets. Partial/open: historical deletion transport to the tail,
global some-node selected coverage/ALL-NAME rebase/D5 bridge, actual canonical
Insert position/occurrence pairing and whole modulo synchronization. C0 remains
ineligible; convergence is not proved. Next work remains exactly those producer
seams after reviewer gate, not retrying exhausted scalar/one-origin statements.

Production and all protected surfaces remain frozen; census4. No lock or lane-2
worktree access; timestamp-only overlaps, own resource guards, no interruption
or mutation. Archive anchor precedes publication/gate receipts by design.
274 inventory entries include111 NOT rechecked;165 source targets plus seeded
package is not a cold-build/all-inventory certification. Zero RSS samples in13
checks mean no captured live peak, not zero memory. See O6-R200-* evidence.


## R200 owner FINAL gate — D4 checked PARTIAL seal

Full165-source+seeded-package validation and all212 expected outcomes are
complete. Post-D3 machine authentication reports clean tracked tree, no staged
files, and only the permitted untracked paper/review artifacts. See
`research-tests/O6-R200-OWNER-FINAL-GATE.md` for the exact checked B base type,
missing historical transport, closed A residual result, still-open Insert/whole
history producers, C0, comment hashes, resource/census evidence and archive
anchor limitations. Independent reviewer/owner decision is requested; no new
budget, proof attempt or full confluence completion is implied by this seal.


## Status — R201 source freeze (2026-09-09)

Checked PARTIAL at `df921f18`:45 new supporting declarations in6 new research
sources,40 proof functions +5 indexed families/records; no new holes or escapes.
Production `src/` and `dgamma.ipkg` remain byte-identical to34b21c9. No frozen
surface, selector, O17/O21, lane-owned module or superseded goal is changed.

**B — retained birth and native Unloads, not the retained-closing join.**
`o20DeletionRetainedBirth` constructs the actual nonselected surviving generated
Insert and its exact stored `generationForward` coordinate from the actual
step's accounting/origin equations. `o20DeletionRegisteredUnloadFree` derives
whole original-scan exclusion of registered-generation Unloads from the
candidate's no-registered-episode certificate and the native Inactive invariant.
`o20DeletionRetainedUnloads` then produces physical Unload retention for the
actual before segment (all actors), center (FOREIGN actors only), and after
segment (all actors). This is historical output, not just endpoint presence.
The R193/R195 full vestigial fixture applies both producers with real step and
nonselection explicitly conditional; it does not fabricate canonical capital.

The EXACT `o20DeletionRetainedClosingBirth` is still OPEN: join the retained birth
with a retained later parent Unload in its OWN suffix. In the selected-parent
case, the supplied original close may be the removed center close: another
retained close or actual selected-birth membership must be derived. Native
retention on the three segments alone does not prove birth-relative order.
No logical insufficiency of existing stored capital was established, so no
new-field manifest/oracle or frozen-edit gate was asserted. Global
`everyPresentVestigialSelected` over the actual backward-rebased
`closingFreeDeletionGenerations`, current-coordinate transport, both-side
present-unsupported cases, per-class ALL-name rebasing at
`expectedBridgeBijection`, O20AllNameCut and D5 bridge remain OPEN.

**A — actual supported physical Insert stages, not synchronization.**
`o20PermutedCanonicalInsertOrigins` attaches both original scanners' per-activation
positions to the SAME actual exchanged/canonical Insert origins and exact
conjugated physical stamps. `o20PermutedCanonicalPhysicalInsertAttachment` adds
an actual native O20StampedStage at those two births' own source/target states.
Both target observations are produced from their exact checked evaluator
results using the public single-constructor insertion-plan producer; no target
state equality, successor cut, paired stage or opposite birth is a new premise.
Whole accepted uniqueness/support/matching/operational inputs remain explicit.
The original position counters are NOT asserted to be canonical per-activation
counters. R191/R193 native child cuts exercise the NEW stage observation producer.
This fixture is not independent accepted canonical capital or a complete history.

The next A debt is `o20ReplayPreservesActivationInsertPosition` (not yet a source
statement): transport actual per-parent-activation counts/order through block
exchange, use R200 empty remainders/plain role words, attach root occurrences
with existing C6/C9 laws, produce genuine unsupported/closing skips, then fold
whole ordered occurrence-labelled paths. `o20SynchronizeCanonicalHistoriesModulo`
remains OPEN against the unchanged `o20CanonicalSynchronizationGoalModulo`.
A stage at two actual cuts is NOT their common predecessor relation, whole-word
coverage, a skip proof, or a whole execution. No arbitrary edge is declared zero.

**C0/ineligible.** Neither full A nor B closes; no convergence-body attempt.
Census remains4=1/2/0/0/1, not the conditional3-hole milestone.

Budgets: B26 micro-units/26 invocations, A19 micro-units/21 invocations,45 immediate
GUARDED source commits. A5-1 had a generated-signature text replacement error,
repaired on attempt2. A19-1 incorrectly expected front insertion of a fresh
current-generation entry; CP3 appends. Owner clarified that caps count
MICRO-UNITS (R199 precedent) and authorized ONLY the expected-list correction;
A19-2 PASS. This is a fixture-expectation error, not a producer defect. No3/3 or
exhausted-statement retry. A20 was not started; owner explicitly permitted freeze
after A19 when the next transport was not a well-defined single micro-unit.

D1 prepares the complete immutable validation plan: ALL165 inherited main
sources+6 new=171 source targets, plus seeded package=172 checks,7 exact
expected-negative diagnostics AND symbols, no path exclusions.21 evidence and7
no-lock policy tests PASS. Final native validation is pending at this checkpoint.
No cold build or inventory-wide fresh check is claimed. RSS guards remain52GiB
for unchanged LocalDiamond,48GiB for all other main checks including the
explicitly gated unchanged UniqueOrdinal; one own compiler, timestamp-only
foreign overlaps, no lock paths or lane2 worktree operations.


## Status

### R201 D2 — final validation complete, checked PARTIAL

Final native validation completed **2026-09-09T16:54:11Z**: ALL165 inherited
applicable sources+6 new=171 source targets, plus seeded package=172 checks.
Seven are exact expected-negative diagnostics AND symbols, not positive
proofs.220 native invocations total,218 expected outcomes and2 rejected
development snapshots (A5-1 signature text-generation error, A19-1 fixture
append-order expectation error); neither rejection is laundered as PASS.
The45 retained declarations are all guarded-committed, one per invocation:
40 proof functions+5 indexed families/records, no source changes afterdf921f18.

Compiler-free final independent authentication, frozen audit and resource audit
PASS. Every source receipt and source commit is authenticated, as are the
immutable172-check plan, source snapshots and native logs.21 evidence-contract
and7 no-lock-policy adversarial tests PASS. Native lifetimes do not overlap in
this lane; no source mutation, resource stop, unexpected prerequisite Building
line, unknown-source PASS or staged file. One-second sampled peaks: LocalDiamond
50,505,488KiB under52GiB; UniqueOrdinal and all other main checks at most
44,795,856KiB under48GiB. These are samples, NOT OS high-water measurements;
zero-sample short checks are explicitly labelled, not assigned a fictitious peak.

Fully proved **supporting statements**, not completed headline producers:
actual nonselected retained birth/stamp, actual original-scan registered-Unload
exclusion, before/foreign-center/after physical Unload retention, and actual
supported physical Insert attachment/stage with original position coordinates.
A18's incoming `leftLive`/`rightLive` are arbitrary explicit parameters, NOT
produced native prefix-scanned environments. Actual source/target states and
physical ordinal counts are native; a whole scanner/history/cut is still needed.

PARTIAL/OPEN: retained-closing join -> actual global vestigial selection coverage
-> exact current-coordinate/all-name endpoint rebase -> D5; canonical activation
position/order transport -> real root/unsupported/closing skips -> whole ordered
occurrence history -> `o20SynchronizeCanonicalHistoriesModulo`. The modulo goal
is unchanged. C0/ineligible; no convergence-body attempt and census remains
**4=1/2/0/0/1**. No capital-insufficiency result or new-field manifest was produced.
No production, five approved contract, selector, O17/O21 or lane-owned source edit.
Production byte-identical to34b21c9, frozen hashes match their accepted anchors.

Next: prove the retained birth-relative Unload in the selected-parent removed
center case (or derive selected membership), then the actual global induction;
for A, produce native prefix-scanned environments and canonical per-activation
count/order transport, rather than treating original positions as canonical ones.
Only after BOTH close may the convergence body be attempted. Independent owner
review and append-only evidence publication/final gate follow; this paragraph is
not a claim of independent acceptance.

The complete extracted paper text was read in eight consecutive tool ranges to
EOF (3882 lines,301314 bytes), SHA256
9b40364ab67f944406c6f40980cdc78dbba044d6eb3125aa1087f2ffdfc9a78b.
See `O6-R201-PAPER-READ.json`; this is not PDF typography verification.


### R201 D4 — owner-accepted checked partial seal

Owner accepted the EXACT partial boundary and authorized D4 after independently
checking D3's48 commits, scope, clean tree, production/frozen identity, census
and no main compiler. The owner pushed D3 and is launching the separate
read-only reviewer; that review is not claimed complete here. See
`O6-R201-SUPERVISOR-GATE.md` and the three post-publication verification artifacts.
The archive is1,247,702bytes/1135files atD2, SHA256
1ea37aa6e459a35cc96ebcbb3c792e7f487786da01addec6e74f1cedc96bb9ec;
all220 native records authenticated,45 source+2 prior artifact receipts inside,
D3/D4 receipts outside by construction. No new compiler/source attempt followed
V172. D4's resulting receipt is delivered in the structured completion report;
no cyclic self-containing receipt is claimed. Stand down after final read-only
checks. No headline closure or cold build is asserted.


## Status

### R202 D2 — checked PARTIAL, native prefix scans and local own-suffix joins

Source freeze `2a28e44e058ecf30a587c9151fc5de0bf52254c6`, baseline `bc791641`.
Thirty guarded declarations (29 quantity-zero proof/fixture functions and one
new erased record) in five new sources. No inherited Idris file or production
API changed. All new proof modules are total; no new escape hatch, postulate,
partial function or hole. Existing protected census remains4=1/2/0/0/1.

**Fully proved supporting B statements:** a deleted classification supplies its
actual birth-relative original close; exact source-index preserving Unload
transport through registered/foreign filters; strict subsequence order
reflection; the retained close lies in that SAME retained birth's own suffix
when both live in ONE shared segment/subsequence; and actual step accounting
produces a retained birth with the original parent/component in its result type
and exact forward generation stamp. B2 derives nonselection contradiction only
from an explicitly located selected-center birth and exact stamp equation.

**B remains partial:** joining the three physical deletion segments and deriving
the selected-center birth location from the selected-parent removed-center close
are still open. `o20DeletionRetainedClosingBirth`, global actual-chain discarded
coverage, current-coordinate/all-name rebase and D5 are NOT produced or applied.
B11/B12 still take a retained birth and its exact native source-index equation.
B14's genuine R193 eight-edge history has birth2/close7/suffix4, but target
subsequence, Unload exclusion and retained-birth origin remain conditional. No
insufficiency of stored capital has been established; no new field manifest.

**Fully proved supporting A statements:** native final scan ordinal equals the
starting ordinal plus actual trace count. The new supported physical Insert
attachment computes BOTH native environments and scan certificates from the
actual attached births' preceding traces. A18-style arbitrary `leftLive` and
`rightLive` arguments are removed in the new producer, without editing A18.
`o20PrefixScannedInsertCut` derives the successor all-name cut only conditional
on its genuine native scanned predecessor. Local native registration-index
laws prove deleted classifications consume zero surviving positions, while a
retained classification consumes exactly one within the observed SAME complete
parent activation (generation and L-Begin stamps retained). Typed explicit
observation/equation pairs are used, never inferred case views or let aliases.

**A remains partial:** these positions are local classifier laws, NOT whole
canonical per-activation count/order preservation. The attached existing
position metadata remains ORIGINAL scanner positions. Accepted-input all-name
predecessor production, actual root/unsupported/closing skips, complete ordered
paired histories and `o20SynchronizeCanonicalHistoriesModulo` remain OPEN at
unchanged specifications. A7 checks real R191/R193 prefix outputs; A16 checks
local classifier algebra, not two accepted classifications of one birth. No
arbitrary native edge is declared epsilon. **C0/ineligible**: neither headline
A nor B closes, so no convergence-body attempt is authorized or performed.

**Evidence:** final native validation ended 2026-09-09T18:19:31.367209+00:00, with all171 inherited
applicable main sources +5 new =176 direct source targets plus seeded package,
177 planned expected outcomes, including seven diagnostic-AND-symbol negative
fixtures.211 total invocations,207 expected outcomes and four retained rejected
snapshots: B2-1 missing direct import; A8-1 opaque event-position motive; A13-1
second Boolean test exposed after update reduction; A16-1 missing explicit
LBegin action family. Each passed attempt2. A8's honest field-input statement
was followed by actual observed-position transport in A9/A10. No rejection is
laundered, no exhausted retry, B15 or A17. Caps B14/A16 reached; D≤4.

Immutable import-closed plan SHA256:
`e0f83271b9b493b3f602771c8c300a3e0fc4c06891e1967a7efa80f7302abb34`.
All171 inherited applicable paths included, no exclusions. Source-pinned
unchanged dependencies outside the inherited280-source inventory/plan remain
reused seeds, not fresh-PASS claims.21 evidence-contract and10 policy-contract
tests PASS. Read-only machine authentication verifies source snapshots, logs,
every immediate source receipt/commit, one declaration per proof commit, plan
closure/topological order, runner/driver hashes and unchanged frozen sources.
This is NOT independent human review or a cold package build.

One main compiler at a time, no lock operations, foreign overlap timestamps
only. One-second samples: LocalDiamond 50,506,768KiB under52GiB; UniqueOrdinal
44,779,824KiB and all other checks at most 44,779,824KiB under48GiB. No resource
stop, source mutation or unexpected prerequisite build. Samples are NOT OS
high-water; zero-sample short checks are explicitly unmeasured. Production and
package remain byte-identical to34b21c9; five protected contracts, named bodies,
O19 and superseded synchronization/stamped-history surfaces remain unchanged.

**Evidence metadata deviation:** the inherited policy label erroneously said
R201 through A6 while its actual enforcement/runner fields already implemented
R202. Only `shift` was corrected at the recorded timestamp; prior bytes and
all prior invocation hashes remain unchanged. Independent authentication proves
the label-only difference, exact before/after hash and affected prefix. Tests
reject unapproved old labels and changed enforcement. The pinned runner's old
explanatory timing comment is nonexecuting; actual guards are R20220:22/20:37.
This is catalogued in O6-R202-POLICY-LABEL-CORRECTION, not silently relabeled.

**Next:** derive exact three-segment birth/close origin compatibility and the
selected-parent center contradiction, then global coverage/all-name rebase.
For A, transport whole canonical activation counts/order and build the actual
predecessor/skips/ordered occurrence synchronization using the now-computed
prefix environments. Only after BOTH headline producers close may C proceed.
Review/owner gate is parent-owned and remains unclaimed here. Archive publication
is append-only; its anchor deliberately predates later publication/gate receipts.


### R202 D4 — owner-accepted checked partial seal

Owner accepted the exact partial boundary atD3 `396e963d`, authorized artifact-
only D4, and reports pushing D3. Verbatim ruling:
`research-tests/O6-R202-OWNER-FINAL-GATE.md`. Post-D3 machine audits authenticate
all211 native records,30 source+3 prior artifact receipts,177 final expected
outcomes, frozen bytes/census and clean tracked/no-staged state. The1091-file
archive is anchored atD2 `2dfd42bf`, SHA256
`576461e728ee5ebad405c4319a24e4b7a3f8720649cb97515aa21c7225932701`;
D3/D4 receipts deliberately follow that anchor. D4's own resulting receipt is
supplied in the final structured response, not cyclically inside its commit.

B whole-step/selected-center join, global coverage/rebase/D5 and A global
position transport/predecessor/skips/synchronization remain OPEN; C0/ineligible.
No new proof/native invocation afterV177, frozen-source change, new hole,
archive replacement or self-extension. D4/4; stand down. The separate read-only
reviewer is being launched by the parent and is NOT claimed complete here.

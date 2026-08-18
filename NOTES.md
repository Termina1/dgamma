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

   The former global no-rebirth condition has been removed. The paper explicitly
   says a name freed by O-Remove may be reissued (lines 1855–1858); current
   freshness plus located occurrence evidence distinguishes each birth instead
   of banning that legal behavior. The finite catalog tag/rank is an explicit
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

7. **Lemma 56's global raw-name action is ambiguous under legal name reuse.**
   Lemma 56 states equivariance for one bijection on raw names, while the
   Preservation discussion explicitly permits O-Remove followed by reuse of
   the freed raw name. Those clauses do not compose across two complete traces
   when one raw name denotes a historical generated child and later a shared
   live root: the historical child may need to map to a different fresh raw
   name, while the current root is an externally fixed input. The mechanization
   therefore uses `RegistrationGenerationBijection` on `(raw name, birth
   ordinal)` for historical/generated registration trees, and a separate
   `CurrentEndpointRenaming` for the current registries with live roots fixed.
   This is a generation-wise interpretation of Lemma 56, not a ban on reuse.
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
13. **CP4 Finding #8 — Lemma 72's raw R filter deleted later generations.**
    The accepted CP3 statement used `RegisteredActor (List name)` before and
    after the selected episode. After the selected child generation was
    O-Removed, a legal later O-Insert could reuse its raw name; the raw filter
    then deleted that unrelated root birth too. At a quiet endpoint where the
    reissued root is non-retired with unavailable dependencies,
    `RegisteredNamesWithdrawn` was impossible. This is the same raw-name-reuse
    genus as CP3 rounds 6–7 and paper erratum #3 (Lemma 56), now surfacing in
    Lemma 72; the future authors letter should consolidate the genealogy.

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

## Escape-hatch and hole audit

There are no uses of `believe_me`, `assert_total`, `postulate`, unsafe FFI, or
`%default partial`. Every Idris module has `%default total`.

The following are statement-only `Type`s. They export no value and therefore
cannot silently introduce a proof:

- `OperationsRespectIndistinguishability` and
  `CoarsestRespectedEquivalence` — Lemma 35.
- `distinctKeysIndependent` — Theorem 40.
- `MediatedIndependenceTheorem` — Theorem 42.
- `terminalRecoveryTheorem` — Corollary 62.
- `resolutionCoherenceTheorem` — the recovery-combined form of Theorem 64.
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
  and dynamic provider-value constancy. `orderingTheoremProof` now proves the
  complete statement by factoring snapshot/value induction from strict
  last-opening/first-closing episode extraction.
- The global `resolutionStructureTheorem` is anchored by `EpisodePrefix`, so the
  round-1 Unloading-suffix counterexample is unrepresentable. The local
  Equation-59 facts and the whole-episode first-exit split are proved by
  `resolutionStructureTheoremProof`. `resolutionCoherenceFromTerminalRecovery`
  proves all remaining dependent packaging from Corollary 62; the exported
  recovery-combined theorem remains statement-only only because terminal
  recovery itself is open.

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

Theorem 61 and Corollary 62 remain stated. The hard obligation is the **temporal
accumulator induction**: show that the actual dependent accumulator stored by
all L-Iter/L-Divert/L-Raise paths factors into the yielded inverse generators,
then commute each factor across foreign transformations and replay the suffix.
The generated-monoid premise now contains exactly the needed per-yield facts,
but the indexed induction through `InstalledTrace` is not yet implemented.
`resolutionCoherenceFromTerminalRecovery` proves that Corollary 62 immediately
completes the recovery branch of Theorem 64; resolution structure and final
packaging are no longer debt.

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
  provenance needed by Lemma 70. Legal post-remove name reissue is retained.
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
scan. The remaining obligation-2 step is now only construction of
`GenerationReplayReady` from the cross-boundary invariant identifying each
incrementally built survivor with its corresponding original boundary minus the
selected episode/current-R plan. No theorem alias or runtime evaluator changed,
and no escape hatch was introduced.

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

## Status

**Fully proved:** all previously approved Section 3 results; raw Theorem 59
Preservation; Equation 58; local relied guards; per-step Equation 59; whole-
episode resolution structure; global spatial Ordering/Theorem 63 including
strict containment, resolution constancy, and provider-value constancy; and
finite-specialized Lemma 68, including combined support well-foundedness and
unique Definition-67 support-solution equality with the executable closure;
and Lemma 70, including endpoint Active-table totality, non-retired-child
parent safety, both Active/support fixed-point directions, and final Lemma-68
uniqueness assembly; and Progress/Theorem 66, including lifecycle program and
continuation preservation, precedence-acyclicity preservation, complete
unloading-chain no-deadlock, all-rule potential decrease, amortized Equation
61, maximality, and final public-alias assembly; and recovery Theorem 61,
including the conditional selected-step inverse, foreign generated-map
commutation, congruent replay transport, simultaneous installed-trace
induction, and exact public-alias endpoint assembly. The repaired Definition-69/
Lemma-70 and Theorem-66 statement shapes still await end-of-CP4 re-review.

**Partial:** Lemma 71 (effect commutation projection); Lemma 72 (candidate
lifecycle-only deletion statement, exhaustive ten-tag actual-forward effect
frames, generation-correct action/result filtering, proved birth-ordinal bounds
and verbatim pre-episode subsequence construction, a total dependent filter
that exposes kept-action replay failure, exact located splitting of the
no-R-episode and Definition-69 premises, conditional trace/final-record
assembly, executable exact-generation Inactive-leaf plan/actor-outside
construction, constructive plan success from the explicit current-R leaf
invariant, scanner live-name uniqueness plus the public-outside bridge, proved checked
lifecycle and orchestration applicability through that plan (including the
child-O-Insert parent guard), and a complete `CurrentRegisteredChildless`
induction from disciplined registration,
well-formed parent closure, and exact-generation no-episode evidence;
selected-episode/suffix applicability and endpoint effect/control/withdrawal
invariants remain);
Confluence/Theorem
73 (surviving parent-
activation structural cross-trace, generation-stamped canonical proposition,
and vestigial-aware outside-R endpoint relation submitted for round-10 review;
the round-7 cross-parent/historical-root, round-8 closing-episode, and round-9
vestigial-endpoint defects have complete typed regressions, while constructive
deletion/sorting and general endpoint assembly remain open); and recovery-
combined Theorem 64
(complete conditional assembly
from Corollary 62). Lemmas 54–57 have many rule, frame, and boundary analogues
but are not individually complete.

**Merely stated:** Lemma 35, Theorems 40/42, Corollary 62,
`resolutionCoherenceTheorem`, `deletionTheorem`, and `confluenceTheorem`.
These remain escape-hatch-free proposition types.

**Deviations:** Definition 32 finite approximations; finite static-list
continuations; finite tagged/catalogued explicit registration rather than a
recursive nested yield (including the documented one-source-head/many-child-name
over-approximation); trace-anchored full-effect generated monoids; exact full-
effect equality; and explicit `AlignedTransitions` dictionary alignment.

**Next:** apply the now-inhabited Theorem 61 to Lemma-72 selected-episode
recovery/effect equivalence, join it to the constructed deletion skeleton, then
derive final control/withdrawal evidence and inhabit `deletionTheorem`.
After that, use deletion
for constructive canonical sorting. Fresh-choice,
cross-parent, 24/18 activation-reset,
and no-O-Remove 23/18 and 27/18 vestigial pairs reach the literal public premise
chain; the latter two also project the vestigial-aware result. Live providers
and complete-relation historical-root reassignment are rejected. An inhabited
positive canonical schedule remains constructive proof debt.

# dgamma

`dgamma` is an executable Idris 2 mechanization of **“A Programming Paradigm for
Spatiotemporal Composability”** (Shi, Zhang, Cui). Runtime functions remain
computational data; laws and witnesses are erased with quantity `0`.

## Build

```sh
idris2 --build dgamma.ipkg
```

The package contains the approved Section 3 and Checkpoint 2 mechanizations.
Checkpoint 3 (global ordering, Progress, Confluence, and reconciliation) is in
progress.

## Design map

- `DGamma.Core`: equivalences and state-indexed `Undo after before` /
  `Loaded current initial` handles.
- `DGamma.Effects`: twisted composition, effect contexts, witnessed effect
  functions, tracking/recovery, generated transformation monoids and
  independence.
- `DGamma.Coeffects`: finite dependent coeffect tables, safe `get`/`set`,
  notifications, operations, isolation and interception.
- `DGamma.Unified`: explicitly finite context-tower approximation,
  observational equivalence, witnessing up to equivalence, partial-operation
  tests, and coeffect-mediated programs.
- `DGamma.Section3Example`: executable typed-table/notification checks plus a
  two-component effect+coeffect load/load/unload/unload scenario applying both
  base and actual-lifted recovery theorems; mediated failure also propagates.
- `DGamma.Calculus`: capability-confined dynamic per-fiber tables, declared
  dependency values, order-preserving erased-certificate normalization at
  L-Advance/L-Unload effect sources and between accumulated undos, components,
  intrinsically total committed views, name-unique registries, the four-state
  lifecycle, all ten executable rules,
  a checked proof-indexed LTS, and episode extraction.
- `DGamma.Metatheory`: executable well-formedness, raw-rule Preservation,
  whole-episode resolution structure, precise remaining recovery/ordering
  statement types, and their supporting indexed trace predicates.
- `DGamma.CalculusChecks`: dynamic-table/dependency-consumption regressions plus
  executable coverage of all ten tags, both L-Divert alternatives, stale empty
  iterators, per-yield full-state inverse exposure, bit-identical old/new
  multi-effect accumulator recovery, failure, relied/L-Unload ordering,
  recovery, and removal.
- `DGamma.CP3`: finite-host Lemmas 68–72/Theorem 73 interfaces, including
  activation-stamped parent-local surviving-registration trees, exact
  historical external-root coupling, and endpoint equivalence modulo inert
  vestigial generations from deleted closing episodes.
- `DGamma.CP4Support`: registration-rank preservation and rank descent for the
  combined parent/precedence support relation.
- `DGamma.CP4SupportSolution`: constructive fixed-point, soundness, minimality,
  and uniqueness proofs for the executable Definition-67 support closure; it
  exports the accepted Lemma-68 proof.
- `DGamma.CP4ParentSafety`: forward preservation of child-retirement
  provenance; every current non-retired child has a still-open parent.
- `DGamma.CP4SupportQuiescence`: repaired trace-indexed Definition-69 evidence,
  proof-producing actual-boundary validation, and the derived endpoint
  Active-table totality invariant used by Lemma 70.
- `DGamma.CP4SupportActive`: both directions between the runtime Active
  predicate and one unfolding of the Definition-67 support equation at a
  quiet, failure-free endpoint.
- `DGamma.CP4Lemma70`: constructive fixed-point assembly of Lemma 70 from
  Lemma 68, parent safety, and repaired Definition 69.
- `DGamma.CP4ProgressBound`: approved Theorem-66 continuation-bound repair
  infrastructure, including proof that every evaluator rule preserves the
  repaired premise under the declared-program bound.
- `DGamma.CP4ProgressFinite`, `DGamma.CP4ProgressReliance`, and the
  `DGamma.CP4ProgressUnloading*` modules: finite precedence accessibility,
  reflection of a true reliance guard into a concrete precedence successor,
  isolated Reloading/Active clauses, and the total well-founded unloading
  descent.
- `DGamma.CP4ProgressNoDeadlockFinal`: exact lifecycle scan and the proved
  Theorem-66 no-deadlock core `progressNoDeadlockAt`.
- `DGamma.CP4ProgressPotential` and `DGamma.CP4ProgressStep*`: executable
  same-target lifecycle potential, its proved `K + 4` interval upper bound,
  and checked strict-decrease frames for all five lifecycle action forms.
- `DGamma.CP4ProgressNumeric`, `DGamma.CP4ProgressPrecedence`, and
  `DGamma.CP4ProgressProof`: amortized Equation-61 induction, lifecycle
  preservation of precedence acyclicity, and the complete constructive
  `progressTheoremProof` assembly.
- `DGamma.CP4ProgressChecks`: old-shape overlong-continuation countermodel,
  repaired-premise rejection, and a positive checked Reloading witness.
- `DGamma.CP4DeletionFrameCore` and `DGamma.CP4DeletionFrame*`: relational
  soundness of actual-forward effect generators and checked frames for O-Insert,
  all ten Table-1 tags, including both empty/effectful L-Finish, explicit and
  landing L-Divert, L-Iter, L-Raise, and accumulator-driven L-Unload branches;
  `actualTransitionEffectFrame` is the exhaustive checked aggregate.
- `DGamma.CP4DeletionControl*`: executable Lemma-57 control frames showing that
  deleting an Inactive leaf preserves active-provider targets, committed
  capability resolution, and reliance; all five lifecycle action forms remain
  raw- and checked-applicable through an indexed multi-leaf deletion plan.
  `DGamma.CP4DeletionControlOrchestration` proves the complementary O-Insert,
  O-Retire, and O-Remove applicability frames through the same plan. Its
  `OrchestrationOutsideDeletionPlan` records both owner exclusion and the extra
  child-O-Insert parent exclusion, so all retained action classes now have a
  checked plan-level replay theorem. `DGamma.CP4DeletionRetainedAction` derives
  those certificates per original boundary: fresh insertion gives owner
  exclusion, disciplined parent-yield provenance excludes an Inactive R parent,
  and the complement of exact generation ownership handles every non-insertion
  action. Threading these one-step results through the two dependent filters
  remains the final filter-success part of obligation 2.
  `DGamma.CP4DeletionControlChecks` supplies a nonempty checked L-Finish replay.
  `DGamma.CP4DeletionPlanBuilder` scans the final live generation environment,
  skips historical generations and later raw-name reissues, constructs the
  indexed Inactive-leaf plan, and projects actor-outside certificates. Scanner
  uniqueness proves the public `CurrentGenerationOutside` premise supplies the
  stronger pointwise actor-outside certificate the plan requires;
  `checkedLifecycleAfterCurrentRegisteredPlan` integrates that bridge with the
  proved all-lifecycle control replay theorem.
  `DGamma.CP4DeletionInactiveInvariant` proves every current exact R generation
  remains Inactive across the full checked trace from the generation-indexed
  no-episode premise. `DGamma.CP4DeletionPlanSuccess`
  proves the builder's checked plan exists from the exact
  `CurrentRegisteredInactiveLeaves` boundary invariant and proves leaf deletion
  cannot create children. `DGamma.CP4DeletionPlanBoundary` combines inactivity
  and scanner uniqueness. `DGamma.CP4DeletionChildlessInvariant` proves the
  remaining generation-indexed `CurrentRegisteredChildless` property by forward
  induction from `RegistrationDiscipline`, well-formed parent closure, and exact
  `NoRegisteredEpisode` evidence; `reachedDisciplinedBoundaryGivesDeletionPlan`
  now derives the complete current-R plan without a hand-supplied boundary fact.
- `DGamma.CP4DeletionGenerationChecks`,
  `DGamma.CP4DeletionGenerationScan`,
  `DGamma.CP4DeletionGenerationBounds`,
  `DGamma.CP4DeletionGenerationUnique`,
  `DGamma.CP4DeletionGenerationFilter`,
  `DGamma.CP4DeletionFilterSuccess`, `DGamma.CP4DeletionPremiseSplit`,
  `DGamma.CP4DeletionSkeleton`, and `DGamma.CP4DeletionSkeletonSuccess`:
  Finding-8 checked reuse countermodel,
  a total proof-producing scanner, proved birth-before-current-ordinal,
  live-name-uniqueness, and key/stamp-name coherence invariants, decidable
  exact-generation deletion
  predicates, and a total
  `Maybe` keep/delete/replay constructor for every finite trace. The old raw-name
  filter provably deletes a later root reissue, while the repaired `(name,
  birth ordinal)` filter preserves it; registrations born in the selected
  episode are proved unable to delete any prefix action. The constructor
  returns `Nothing` precisely at a kept action that fails in the smaller state.
  `GenerationReplayReady` packages exact retained `fireNamed` successes, and
  `generationReplayReadyGivesFilterSuccess` proves the executable filter itself
  returns `Just` (with selected-episode and suffix specializations).
  `DGamma.CP4DeletionReadiness` proves both structural readiness inductions:
  `selectedEpisodeRetainedReplayGivesReadiness` and
  `registeredGenerationRetainedReplayGivesReadiness` thread exact deletion
  decisions and survivor endpoints from one record-saturated retained-head
  interface. `DGamma.CP4RuntimeBindings` proves the exhaustive eight-action
  `transportApplyActionAcrossRuntimeSnapshot` keystone: evaluator tags and exact
  ambient/ordered-binding results are invariant under changes to erased
  uniqueness certificates; `DGamma.CP4RuntimeBindingsChecks` pins that rationale
  with separately defined singleton certificates. `DGamma.CP4DeletionPlanRuntime`
  proves the matching dependent plan reindexing theorem across exact ordered
  bindings, preserving every Inactive/childless leaf, every actor-outside
  certificate, and the final target binding list without proof irrelevance.
  `DGamma.CP4DeletionPlanComplete` strengthens
  the canonical current-R leaf builder with the erased converse: every current
  exact R generation occurs in the plan, and derives that complete plan directly
  from the public reached/discipline/no-episode premises.
  `DGamma.CP4DeletionCommuteCore` proves exact ordered-binding commutation for
  distinct insert/delete, replace/delete, and delete/delete updates.
  `DGamma.CP4DeletionPlanCommute` lifts those laws through an indexed leaf plan:
  retained insertions, parent-preserving replacements, and deletions commute
  through the whole plan, while a deleted actor's exact occurrence is removed
  from the plan. The additional `retireExactActorInInactivePlan` fold handles
  the evaluator's legal idempotent re-retirement of an exact deleted leaf. All
  results compare runtime bindings only and transport the dependent tail rather
  than equating `UniqueKeys` proof terms. Their strong boundary forms also prove
  exact preservation of plan actors; exact removal proves the dropped actor is
  outside the new plan and all distinct leaves survive.
  `DGamma.CP4DeletionBoundaryPlan` lifts those actor facts to complete current-R
  plans across retained insertion/replacement/removal and exact deleted removal,
  with generation environments updated in lockstep.
  `DGamma.CP4DeletionNoEpisodeReplay`
  proves the suffix retained-head frame for all eight actions at a current-R
  plan boundary and names `NoEpisodeReplayBoundary` at this exact runtime
  representation. The boundary now coherently owns the complete current-R plan
  (not a separate side invariant), and runtime plan transport preserves its
  exact actor list as erased metadata. `DGamma.CP4DeletionBoundaryDeleted`
  proves the exhaustive deleted-head preservation theorem: birth bounds exclude
  O-Insert, no-episode evidence excludes L-Begin, Inactive leaves exclude the
  other lifecycle actions, and exact O-Retire/O-Remove preserve the boundary.
  `DGamma.CP4DeletionBoundaryRetained` proves all retained head forms.
  O-Insert/O-Retire/O-Remove commute registry updates through the plan. The five
  lifecycle cases use rule-specific exact one-leaf comparisons plus the shared
  `lifecycleActionThroughInactivePlan` fold, preserving callback results,
  lifecycle controls, complete actor coverage, ambient state, and ordered
  bindings without proof irrelevance. Both exhaustive orchestration and
  lifecycle dispatchers are closed. `DGamma.CP4DeletionSuffixFold` now performs
  the dependent whole-trace no-selected-episode suffix induction, constructing
  its generation scan, concrete-filter readiness, and final complete boundary
  simultaneously. `DGamma.CP4DeletionSelectedEffectCore` starts the selected
  quotient with an accumulator-indexed effect boundary: checked L-Begin proves
  the base against the untouched survivor, and every selected installed step
  preserves that boundary when its lifecycle action is erased.
  `DGamma.CP4DeletionSelectedEffectForeign` then proves the foreign half of the
  Lemma-71 diamond: the corrected actual map runs on the related survivor, its
  ordered-table output matches target recovery, and a later checked-control
  proof can package the next boundary without repeating commutation.
  `DGamma.CP4DeletionSelectedBoundary` combines that effect relation with a
  complete current-R plan, exact controls outside the selected/R generations,
  and checked well-formedness. It proves the post-L-Begin base and preserves all
  foreign controls across any skipped selected installed step.
  `DGamma.CP4DeletionSelectedOwn` combines scanner stamp coherence with the
  public selected/R exclusion, commutes every selected installed replacement
  through the complete plan, and consumes the selected accumulator step to
  preserve the full boundary while the survivor skips it.
  `deletedSelectedInstalledHeadPreservesEpisodeBoundary` dispatches every
  checked selected interior lifecycle head through the exhaustive recovery
  infrastructure. The remaining selected layer must rebuild retained foreign
  controls, handle deleted R heads, and close L-Unload.
  `DGamma.CP4DeletionRelationalBoundary` is the primary selected-to-suffix
  interface: it relates the actual survivor to the complete plan target by
  ordered effects and an ordered control skeleton with extensional accumulators.
  The former exact snapshot boundary
  embeds as a specialization, but selected recovery is never strengthened to
  function/proof equality. `selectedUnloadClosesEffectBoundary` identifies the
  boundary model's handle with checked L-Unload's handle and closes exact
  post-episode effect agreement with the untouched survivor. The
  located-episode splitter
  derives the episode/suffix generation scans and restricts both no-R-episode
  and repaired Definition-69 evidence without new public premises.
  `DeletionTraceSkeleton` integrates those proofs with both dependent filters;
  `deletionReplayReadyGivesTraceSkeleton` is its non-`Maybe` proof-driven
  assembly and runs both executable filters through their exact success
  theorems. `assembleDeletionResult` proves final record construction from
  exactly the three remaining endpoint invariants.
- `DGamma.CP4RecoveryAccumulator`, `DGamma.CP4RecoveryTrace`, the selected-step
  recovery modules, `DGamma.CP4RecoveryForeignCommute`,
  `DGamma.CP4RecoveryReplay`, and `DGamma.CP4TerminalRecovery`: complete
  constructive Theorem-61 recovery and Corollary-62 terminal recovery.
  L-Begin establishes the normalized identity base; every selected installed
  branch recovers its source (including conditional-law L-Advance), foreign
  generated transformations commute across the accumulator, and simultaneous
  temporal induction assembles the exact full-effect `ForeignReplay` result
  without function extensionality.
- `DGamma.CP4ResolutionCoherence`: complete Theorem-64 assembly from the proved
  whole-episode resolution structure and Corollary-62 terminal recovery.
- `DGamma.CP4IndependenceNonVacuity` and `DGamma.CP4RestrictionChecks`:
  Finding-7 order-preserving Definition-60 restriction, reverse-order
  old/new/actual regression, and nonempty corrected `TraceIndependent` /
  `PrefixRecoveryIndependent` witnesses.
- `DGamma.CP4TotalityChecks`: checked foreign-interleaving countermodel to the
  old uninterrupted Definition-69 reading plus a genuinely total positive
  interleaving regression.
- `DGamma.CP3StatementChecks`: checked positive/negative proposition-shape
  regressions, including the delay/divert/delete/reopen activation-episode pair.
- `DGamma.CP3VestigialChecks`: checked 23/18 and 27/18 no-O-Remove schedules,
  complete public Theorem-73 premise chains, and live-provider rejection.

`Pointwise` equality is used for functions rather than assuming function
extensionality.

## `StepEffect` author obligation

A successful step's recovery law is exact on the canonical evaluator domain.
For `runStepEffect capability before = Right (after, undo)`, an author must prove

```text
normalizeLocal provision before = before ->
undo (normalizeLocal provision after) = before
```

The precondition is not optional bookkeeping: public callbacks can otherwise be
called with proof-distinct, noncanonical erased table certificates. L-Advance
and Definition 60 always construct `before` by one
`restrictOwnedPreservingOrder`; `restrictedLocalCanonical`,
`advanceSourceStepRecovery`, and `yieldedInverseStepRecovery` discharge the
precondition. `pushLocalUndoRecoversStep` proves that composed LIFO accumulators
continue to feed canonical sources to every older undo.

## Paper correspondence

“Stated” means the proposition is present as an Idris `Type`, but no inhabitant
is exported. It is not a postulate and cannot be used as a proof.

| Paper | Idris name | Status |
|---|---|---|
| Def 1 | `DGamma.Effects.Twisted`, `twisted`, `twistedUnit` | proved/executable; monoid laws proved pointwise |
| Def 2 | `EffectContext` | executable |
| Def 3 | `track` | executable |
| Thm 4 | `trackProjection` | proved |
| Thm 5 | `trackUnit*`, `trackComposition*` | proved pointwise |
| Def 6 | `recover` | executable |
| Thm 7 | `recoverTracked` | proved |
| Def 8 | `EffFn`, `EffStar`, `Applied`, `Undo` | executable; witnesses erased |
| Def 9 | `diamond` | executable |
| Thm 10 | `diamondAssociative*`, `diamond*Unit*`, `embedTwisted*` | both monoid clauses and unconditional homomorphism proved pointwise |
| Thm 11 | `diamondStar`, `etaStar`, `fromTwistedStar` | proved |
| Def 12 | `effect` | executable |
| Thm 13 | `effectPreservesDiamond*` | proved on every forward/inverse field, pointwise |
| Thm 14 | `effectForwardProjection`, `effectInverseProjection` | proved |
| Thm 15 | `effectUndoCurrent`, `effectUndoAccumulatorFormula`, `effectLiftWitnessIff` | exact state/formula/soundness and uniform-inverse iff proved pointwise |
| Thm 16 | `reverseActual`, `reverseActualRecovery`, `actualLifoEveryIntermediateProof` | actual lifted accumulator carried through every reverse boundary; current-state and recovery invariant proved |
| Def 17 | `Generator`, `Transformation`, `runTransformation` | executable inductive generated monoid |
| Lem 18(1) | `generatorsSettleCommutation` | proved |
| Lem 18(2) | `diamondDoesNotEnlarge`, `diamondDoesNotEnlargeProof` | proved by embedding generated transformations into `JointTransformation` |
| Def 19 | `Independent`, `PairwiseIndependent` | exact executable/proof interface |
| Thm 20 | `forwardAcross`, `withdrawAcross`, `theorem20EveryIntermediateProof`, `outOfLIFOProof` | both equations for every intermediate `u`, plus later-inverse stability, proved |
| Cor 21 | `Permutation`, `anyPermutationRecoveryProof` | proved for every adjacent-swap permutation |
| Def 22 | `Binding`, `UniqueKeys`, `CoeffectContext`, `lookupBinding` | executable finite dependent partial function; duplicate domains unrepresentable |
| Def 23 | `get`, `setFresh`, `CoeffectApplied`, `CoeffectUndo` | executable; successful set returns an indexed witnessed **partial** key-deleting undo |
| Def 24 | `CoeffectOperation`, `OperationResultsRelated`, `CoeffectInterface`, `LiftedUndo`, `liftOperation` | partial inverses, witnesses, observational laws/outcomes, and witness-carrying runtime table lift mechanized |
| Def 25 | `CoeffectSpec`, `UniqueKeys`, `satisfies` | executable intrinsically unique finite set/decidable predicate |
| Def 26 | `Notification`, `notify` | executable; activation/deactivation facts proved |
| Def 27 | `Realisation`, `recoverRealisation`, `inPlaceRecovery`, `derivedRecoveryDiscardsChild` | both distinct recovery algorithms executable and proved |
| Def 28 | `RealmEmbedding`, unique-map `Assoc`, `IsoContext` | executable; default key-to-realm map injective and overrides duplicate-free |
| Def 29 | `IsoSetResult`, `isoUndoValid`, `isoGet`, `isoSet`, `isolateRealisation` | indexed partial set/inverse; certificate proves dependency-table projection recovery (non-table fields preserved by smart constructor) |
| Def 30 | `MetadataMonoid`, `InterContext`, `InterSpec` | context and unique interception specification executable; laws erased |
| Def 31 | `InterSetResult`, `interUndoValid`, `interGet`, `interSet`, `interceptRealisation` | indexed partial set/inverse; certificate proves provider-table projection recovery (ambient metadata preserved by smart constructor) |
| Def 32 | `UnifiedLayer`, `ContextTower`, `GammaInfinityApprox` | **partial/deviation**: executable finite approximations only; literal negative fixed point is not claimed |
| Def 33 | `MaybeRelated`, `TableRelated`, `StateRelated` | mechanized; equivalence laws proved |
| Def 34 | `OperationSuite`, `FixedInverseStep`, `YieldedInverseStep`, `runTest`, `Indistinguishable` | executable tests observe both fixed-inverse respect and dynamically yielded-inverse relatedness |
| Lem 35 | `IndistResultAgreement`, `CandidateResultAgreement`, `OperationsRespectIndistinguishability`, `CoarsestRespectedEquivalence` | redesigned non-countermodel universal-property statements, unproved (`TODO(proof)`) |
| Def 36 | `MapRespects`, `MapsRelated` | mechanized |
| Def 37 | `RelResult`, `RelEffStar`, `fromEffStar` | executable/witnessed |
| Lem 38 | `relDiamond`, `RelEffectStack`, `relPushStack` | **partial**: relational composition/accumulator soundness proved; full transport of every Section 3.1 theorem not claimed |
| Def 39 | `PartialTransformation`, `OperationsIndependent`, `LiftedOperationsIndependent` | partial generated monoids, commutation up to equivalence, inverse/outcome stability mechanized |
| Thm 40 | `KeyedOperationSuite`, `distinctKeysIndependent` | correctly confined distinct-key lift theorem stated, unproved (`TODO(proof)`) |
| Def 41 | `Mediated`, `runMediated`, `failurePropagates` | executable partial continuation tree; operation failure remains failure |
| Thm 42 | `Occurs`, `ProgramUsesKey`, `keyCommutative`, `sharedKeysCommutative`, `MediatedIndependenceTheorem` | exact interface-wide shared-key-commutativity hypothesis restored; stated, unproved (`TODO(proof)`) |
| Def 43 | `Component`, `OwnedTable`, `componentDependencies`, `componentProvisions` | executable; provider tables are dynamic fiber state and intrinsically confined to declared provisions |
| Def 44 | `Parent`, `Fiber`, `View`, `freshFiber` | executable; fibers own dynamic tables and views are intrinsically total on the exact dependency list |
| Def 45 | `Registry`, `SystemState`, `activeCoeffects`, `providerOf` | executable; registry names and coeffect keys are intrinsically unique |
| Def 46 | `targetFiber`, `targetAt`, `quietFiber`, `quiet` | executable |
| Def 47 | `Registration`, `registration`, `registrationYieldTag`, `RegistrationProtocol`, `ParentRegistrationYield` | **explicit finite-host representation/over-approximation**: a step carries an optional deterministic catalog tag; theorem traces tie child O-Insert/O-Retire to that exact nonempty iterator stage while the evaluator remains unchanged. Because O-Insert does not consume the source head, one tagged head may license several fresh child names, unlike one literal Def-47 application; strict per-component ranks and per-child retirement retain the support argument |
| Def 48 | `DepValues`, `LocalState`, `StepEffect`, `resolveCommittedValues`, `restrictedLocalCanonical`, `advanceSourceStepRecovery` | executable capability confinement: a step reads exactly declared dependency values and mutates only ambient world plus its own provision-confined table; optional registration metadata does not widen local mutation; exact recovery is required on the canonical restricted-source domain, with the precondition discharged for every evaluator source |
| Def 49 | `Lifecycle`, `installed`, `committed` | executable four-state lifecycle with outcomes |
| Def 50 | `relied`, `reliedOnBy` | executable |
| Def 51–52 | `StepEffect`, `componentProgram`, `applyAction` L-Iter/L-Finish/L-Divert/L-Raise cases, `pushLocalUndoRecoversStep` | executable finite failing iterator with per-step exact recovery witnesses on canonical restricted sources and a proved canonical composed-accumulator chain; accumulators normalize between captured undos to align erased certificates with Definition-60 maps without changing runtime bindings; recursive/infinite iterators are not represented |
| Def 53 | `RuleTag`, `Action`, `applyAction`, `checkedApplyAction`, `Transition`, `fire`, `Transitions`, `EpisodePrefix`, `ClosedEpisode`, `episodes` | ten-rule evaluator; proof traces are checked for Def-58 targets; episode types require L-Begin left boundaries and L-Unload right boundaries |
| Lem 54–57 | `VestigialEndpointGeneration`, `vestigialEndpointGeneration`, `InactiveLeafDeletionPlan`, `checkedLifecycleAfterInactivePlan`, structural rule inventory/equivariance/registration facts | **partial**: the exact Lemma-57 inert endpoint shape is executable and live fibers are proved unable to inhabit it. Its control-applicability direction is proved constructively for every lifecycle rule through an indexed multi-leaf deletion plan (target/capability/reliance guards plus checked replay); the converse operational clauses and Lemmas 54–56 are not separately complete |
| Def 58 | `registryWellFormed`, `wellFormed`, `viewBindingsInvariant` | executable decision procedure; committed views require installed providers **and matching provider-table keys**, plus parent, disjointness, and acyclicity checks |
| Thm 59 | `preservationTheorem`, `preservationTheoremProof`, `checkedTransitionTargetValid`, `applyActionDeterministic` | raw invariant preservation proved by exhaustive rule dispatch; checked target admission and same-action determinism separately proved |
| Def 60 | `EffectStateRelated`, `ReachableSuffix`, `IteratorStage`, `iteratorStageEffect`, `TraceEffectGenerator`, `TraceEffectTransformation`, `runTraceEffectTransformation`, `restrictOwnedPreservingOrder`, `restrictOwnedPreservingOrderIdempotent`, `yieldedInverseStepRecovery`, `IteratorYieldAgreement`, `TraceIndependent`, `PrefixRecoveryIndependent`, `singletonTraceIndependent`, `strengthenedRelationRejectsOrderMismatch` | full-effect-state M(i): actual forwards, every statically reachable continuation forward, and every per-origin yielded inverse generate each actor's partial transformation monoid; moved effect tables preserve stored binding order (Finding #7), lifecycle accumulators normalize between undos (Finding #9), exact effect equality compares each complete ordered table pointwise in the actor name without function extensionality (Finding #10), and yielded inverse recovery is proved on the canonical restricted-source domain (Finding #11). Cross-actor monoids commute, yields are stable, concrete independence remains non-vacuous, and the old lookup-only relation is rejected by an order-sensitive executable regression |
| Thm 61 | `AccumulatorHandle`, `AccumulatorModel`, `selectedAdvanceAccumulatorRecovery`, `selectedInstalledAccumulatorStep`, `foreignAccumulatorStep`, `accumulatorReplayAlongSegment`, `foreignReplayInitialRelated`, `recoveryExactnessTheorem`, `recoveryExactnessTheoremProof` | **proved**: L-Begin supplies the normalized identity base; every selected installed action recovers the source accumulator, every foreign action commutes across its generated inverse transformation, and simultaneous installed-trace induction constructs the exact full-effect `ForeignReplay`; Findings #9–#11 discharge ordered normalization, exact-map respect, and the canonical conditional recovery law |
| Cor 62 | `terminalRecoveryTheorem`, `terminalRecoveryTheoremProof`, `ClosingAccumulatorResult`, `appendOwnReplay`, `raiseMapIsIdentity`, `foreignReplayEmpty` | **proved**: Theorem 61 runs on the maximal installed body in the complete closed-trace generator universe; the checked L-Unload exposes the same actual accumulator and its exact full-effect target frame, then appends as the selected own step |
| Thm 63 | `beginSatisfactionTheorem`, `unloadGuardTheorem`, `InstallationEvolution`, `ProviderContainsConsumer`, `extractContainingProviderEpisode`, `providerValueConstantTrace`, `orderingTheorem`, `orderingTheoremProof` | **proved**: selects the same-global-trace provider episode, proves both strict boundaries, constant consumer resolution, and constant provider value; `AlignedTransitions` is the explicit dictionary-alignment premise |
| Thm 64 | `advanceStructureTheorem`, `abortDivertStructureTheorem`, `resolutionStructureTheoremProof`, `resolutionCoherenceTheorem`, `resolutionCoherenceFromTerminalRecovery`, `resolutionCoherenceTheoremProof` | **proved**: Equation 59, whole-episode resolution structure, Corollary-62 terminal recovery, and dependent final packaging are all constructive |
| Def 65 | `precedesFiber`, `PrecedenceEdge`, `PrecedencePath`, `PrecedenceAcyclic` | executable finite precedence graph and precise acyclicity premise |
| Thm 66 | `ProgressResult`, `progressTheorem`, `progressTheoremProof`, `actorTraceEquation61`, `progressNoDeadlockAt`, `lifecycleTracePrecedenceAcyclic`, `continuationsBoundedBy`, `transitionPreservesContinuationsBoundedBy`, `progressCounterAligned`, `UnboundedProgressTheorem`, `unboundedProgressAliasCounterexample`, `progressAliasCounterexample`, `progressCounterContinuationRejected`, `repairedContinuationPremisePositive` | **proved on the approved repaired alias; repaired shape awaits end-of-CP4 re-review**: every lifecycle rule strictly consumes the same-target potential, each target change contributes a fresh `K + 4` interval, lifecycle traces preserve program/continuation bounds and precedence acyclicity, and finite unloading descent proves no-deadlock. The old continuation shape remains constructively refuted at `K=0`; the repaired premise rejects that countermodel and `AlignedTransitions` restores the paper's single global equality discipline. |
| Def 67 | `SupportEdge`, `SupportPath`, `supportClause`, `supportSet`, `isSupported` | executable bounded least-support computation; Equation 62 includes both precedence and immediate-parent edges |
| Lem 68 | `ReachedFromEmpty`, `RegistrationProtocol`, `RegistrationProvenance`, `ParentRegistrationYield`, `SupportWellFoundedResult`, `supportWellFoundedTheorem`, `supportWellFoundedTheoremProof` | **proved (finite specialization)**: reached-trace provenance preserves strict protocol ranks for every registration; parent and precedence edges strictly increase rank, so their union is well founded. The executable bounded support closure is a fixed point, is contained in every Boolean solution, and contains every solution by well-founded rank induction, hence the Definition-67 solution is unique. Legal post-remove raw-name reissue remains allowed. The finite host's documented one-source-head/many-name over-approximation remains unchanged |
| Def 69 | `TransitionComponentTotal`, `TraceComponentsTotal`, `ActiveFiberProvidesAll`, `buildCertifiedActionTrace`; rejected diagnostic `UninterruptedComponentTotalOnProvision` | **CP4 statement repair; re-review required**: totality now ranges over actual checked actor boundaries in an interleaved trace, hence every activation that finishes has every declared provision in its actual table. The old uninterrupted `ProgramFinishes` reading is retained only to type the committed countermodel |
| Lem 70 | `SupportMatchesActive`, `RegistrationDiscipline`, `supportAtQuiescenceTheorem`, `supportAtQuiescenceTheoremProof`, `reachedActiveFibersProvideAll`, `reachedNonRetiredChildParentOpen` | **proved; repaired statement awaits end-of-CP4 re-review**: actual Active-table totality follows from repaired trace-indexed Definition 69; child-retirement provenance keeps every non-retired child's parent open; quiescence and failure-freedom make the runtime Active predicate a Definition-67 fixed point; Lemma 68 uniqueness identifies it pointwise with executable support |
| Lem 71 | `activationEffectTransposition` | **partial**: generated-monoid effect commutation premise is projected; control applicability frames remain open |
| Lem 72 | `GenerationActionSubsequence`, `RegistrationGeneration`, `RegisteredGenerationsDuring`, `EpisodeGenerationDeletedActor`, `WithdrawnGenerationResult`, `ControlEquivalentOutsideGenerations`, `DeletionResult`, `ActualEffectFrame`, `InactiveLeafDeletionPlan`, `checkedLifecycleAfterInactivePlan`, `buildCurrentRegisteredDeletionPlan`, `CurrentRegisteredInactiveFibers`, `reachedCurrentRegisteredInactive`, `CurrentRegisteredChildless`, `reachedCurrentRegisteredChildless`, `reachedDisciplinedBoundaryGivesDeletionPlan`, `CurrentRegisteredInactiveLeaves`, `currentRegisteredLeavesGivePlan`, `GenerationEnvironmentBounded`, `generationTraceScanPreservesUnique`, `currentGenerationOutsideImpliesActorOutsidePlan`, `checkedLifecycleAfterCurrentRegisteredPlan`, `deletionBeforeFromRegisteredDuring`, `decEpisodeGenerationDeletedActor`, `filterGenerationActions`, `splitLocatedNoRegisteredSegments`, `DeletionTraceSkeleton`, `selectedEpisodeRetainedReplayGivesReadiness`, `registeredGenerationRetainedReplayGivesReadiness`, `NoEpisodeReplayBoundary`, `retainedSuffixHeadAfterCurrentPlan`, `retainedSuffixHeadAtBoundary`, `assembleDeletionResult`, `deletionTheorem` | **CP4 Findings #8 repair / partial; re-review required**: filtering, no-episode evidence, outside controls, and endpoint withdrawal use exact `(raw name, birth ordinal)` generations, so later legal reissues survive. A checked quiet-root countermodel proves the old raw filter wrong and the new filter right. Actual-effect frames cover all ten tags, every surviving lifecycle rule remains checked-applicable after indexed Inactive-leaf deletion, scanner ordinal bounds prove the complete pre-episode segment is retained verbatim, the total filter constructs the dependent subsequence whenever each kept replay action fires, and global no-episode/totality evidence is constructively split at exact generation boundaries. Trace/result assembly is proved conditional on filter success and the three exact endpoint invariants. Exact no-episode evidence proves current R generations remain Inactive; disciplined child-registration provenance plus well-formed parent closure now proves they are childless, including safe raw-name reissue, so the full exact-generation boundary plan is constructive. The selected-episode/suffix structural readiness inductions are proved from a saturated retained-head interface; the all-action suffix retained-head frame is proved at an exact current-R plan boundary; all retained and deleted one-head cases preserve the complete boundary with exact ambient/ordered-binding comparison, and `noEpisodeSuffixReplayFold` assembles the entire suffix with its final boundary; the selected-segment Lemma-71 lifecycle/effect quotient, recovery/effect endpoint joining, and final control/withdrawal evidence remain open; the accumulator algebra and complete selected installed-trace temporal induction (all control branches, boundary exclusions, and successful L-Advance pushes) are proved. Finding #10 now makes exact effect equality retain complete ordered tables, and all endpoint/vestigial consumers were revalidated. |
| Thm 73 | `RegistrationActivation`, `SurvivingRegistration`, `DeletedClosingRegistration`, `VestigialEndpointGeneration`, `RegistrationGenerationBijection`, `RegistrationEventMatch`, `RegistrationTraceCorrespondence`, `ExternalRootBirthCorrespondence`, `RegistrationCorrespondenceByGeneration`, `CurrentEndpointRenaming`, `SystemEquivalentByRenamingModuloVestigial`, `CanonicalRegistrationCorrespondence`, `ConfluenceResult`, `confluenceTheorem` | **statement submitted for round-10 review, finite specialization**: surviving births are matched by activation-local parent positions; discarded births carry later `L-Unload parent` evidence and are stamped separately. Current generation coupling bijects only non-vestigials. Final effects remain exact under renaming, controls are exact on non-vestigial domains, and every unmatched present name must be a retired/clean-Inactive/empty-table/childless/unsupported discarded generation. Full public-premise checks cover fresh choice, cross-parent interleaving, the earlier 24/18 activation reset, and paper-normal no-O-Remove 23/18 and 27/18 vestigial endpoints; all were revalidated after Finding #10 strengthened `EffectStateRelated`, while the separate renamed-table endpoint field remains structurally unchanged. A supported ServiceA provider is rejected as vestigial. Removed historical-root permutation is still rejected. Constructive deletion/sorting and general endpoint assembly remain unproved |

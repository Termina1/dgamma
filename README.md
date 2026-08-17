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
  L-Advance/L-Unload effect sources, components, intrinsically total committed views,
  name-unique registries, the four-state lifecycle, all ten executable rules,
  a checked proof-indexed LTS, and episode extraction.
- `DGamma.Metatheory`: executable well-formedness, raw-rule Preservation,
  whole-episode resolution structure, precise remaining recovery/ordering
  statement types, and their supporting indexed trace predicates.
- `DGamma.CalculusChecks`: dynamic-table/dependency-consumption regressions plus
  executable coverage of all ten tags, both L-Divert alternatives, stale empty
  iterators, per-yield full-state inverse exposure, failure, relied/L-Unload
  ordering, recovery, and removal.
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
  cannot create children.
- `DGamma.CP4DeletionGenerationChecks`,
  `DGamma.CP4DeletionGenerationScan`,
  `DGamma.CP4DeletionGenerationBounds`,
  `DGamma.CP4DeletionGenerationUnique`,
  `DGamma.CP4DeletionGenerationFilter`,
  `DGamma.CP4DeletionPremiseSplit`, and `DGamma.CP4DeletionSkeleton`:
  Finding-8 checked reuse countermodel,
  a total proof-producing scanner, proved birth-before-current-ordinal and
  live-name-uniqueness invariants, decidable exact-generation deletion
  predicates, and a total
  `Maybe` keep/delete/replay constructor for every finite trace. The old raw-name
  filter provably deletes a later root reissue, while the repaired `(name,
  birth ordinal)` filter preserves it; registrations born in the selected
  episode are proved unable to delete any prefix action. The constructor
  returns `Nothing` precisely at a kept action that fails in the smaller state,
  leaving that control obligation visible to the remaining Lemma-72 proof.
  The located-episode splitter derives the episode/suffix generation scans and
  restricts both no-R-episode and repaired Definition-69 evidence without new
  public premises. `DeletionTraceSkeleton` integrates those proofs with both
  dependent filters, while `assembleDeletionResult` proves final record
  construction from exactly the three remaining endpoint invariants.
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
| Def 48 | `DepValues`, `LocalState`, `StepEffect`, `resolveCommittedValues` | executable capability confinement: a step reads exactly declared dependency values and mutates only ambient world plus its own provision-confined table; optional registration metadata does not widen local mutation |
| Def 49 | `Lifecycle`, `installed`, `committed` | executable four-state lifecycle with outcomes |
| Def 50 | `relied`, `reliedOnBy` | executable |
| Def 51–52 | `StepEffect`, `componentProgram`, `applyAction` L-Iter/L-Finish/L-Divert/L-Raise cases | executable finite failing iterator with per-step exact recovery witnesses and LIFO accumulator; recursive/infinite iterators are not represented |
| Def 53 | `RuleTag`, `Action`, `applyAction`, `checkedApplyAction`, `Transition`, `fire`, `Transitions`, `EpisodePrefix`, `ClosedEpisode`, `episodes` | ten-rule evaluator; proof traces are checked for Def-58 targets; episode types require L-Begin left boundaries and L-Unload right boundaries |
| Lem 54–57 | `VestigialEndpointGeneration`, `vestigialEndpointGeneration`, `InactiveLeafDeletionPlan`, `checkedLifecycleAfterInactivePlan`, structural rule inventory/equivariance/registration facts | **partial**: the exact Lemma-57 inert endpoint shape is executable and live fibers are proved unable to inhabit it. Its control-applicability direction is proved constructively for every lifecycle rule through an indexed multi-leaf deletion plan (target/capability/reliance guards plus checked replay); the converse operational clauses and Lemmas 54–56 are not separately complete |
| Def 58 | `registryWellFormed`, `wellFormed`, `viewBindingsInvariant` | executable decision procedure; committed views require installed providers **and matching provider-table keys**, plus parent, disjointness, and acyclicity checks |
| Thm 59 | `preservationTheorem`, `preservationTheoremProof`, `checkedTransitionTargetValid`, `applyActionDeterministic` | raw invariant preservation proved by exhaustive rule dispatch; checked target admission and same-action determinism separately proved |
| Def 60 | `ReachableSuffix`, `IteratorStage`, `iteratorStageEffect`, `TraceEffectGenerator`, `TraceEffectTransformation`, `runTraceEffectTransformation`, `restrictOwnedPreservingOrder`, `IteratorYieldAgreement`, `TraceIndependent`, `PrefixRecoveryIndependent`, `singletonTraceIndependent` | full-effect-state M(i): actual forwards, every statically reachable continuation forward, and every per-origin yielded inverse generate each actor's partial transformation monoid; moved effect tables are restricted without changing stored binding order (CP4 Finding #7), cross-actor monoids commute, inverse+continuation yields are stable, and both empty and concrete nonempty traces have constructive independence witnesses |
| Thm 61 | `AccumulatorHandle`, `actualAccumulatorAt`, `accumulatorEffectMap`, `ForeignReplay`, `recoveryExactnessTheorem` | **stated**: L-Begin anchored; all premises and conclusions use the same full effect state; temporal accumulator-factorization induction remains open |
| Cor 62 | `terminalRecoveryTheorem`, `raiseMapIsIdentity`, `foreignReplayEmpty` | **stated**: one full-effect replay equation; L-Raise identity and the empty replay core are proved, but terminal recovery remains open |
| Thm 63 | `beginSatisfactionTheorem`, `unloadGuardTheorem`, `InstallationEvolution`, `ProviderContainsConsumer`, `extractContainingProviderEpisode`, `providerValueConstantTrace`, `orderingTheorem`, `orderingTheoremProof` | **proved**: selects the same-global-trace provider episode, proves both strict boundaries, constant consumer resolution, and constant provider value; `AlignedTransitions` is the explicit dictionary-alignment premise |
| Thm 64 | `advanceStructureTheorem`, `abortDivertStructureTheorem`, `resolutionStructureTheoremProof`, `resolutionCoherenceTheorem`, `resolutionCoherenceFromTerminalRecovery` | **partial/stated**: Equation 59 and whole-episode resolution structure are proved; final packaging from Corollary 62 is proved; only terminal recovery is missing |
| Def 65 | `precedesFiber`, `PrecedenceEdge`, `PrecedencePath`, `PrecedenceAcyclic` | executable finite precedence graph and precise acyclicity premise |
| Thm 66 | `ProgressResult`, `progressTheorem`, `progressTheoremProof`, `actorTraceEquation61`, `progressNoDeadlockAt`, `lifecycleTracePrecedenceAcyclic`, `continuationsBoundedBy`, `transitionPreservesContinuationsBoundedBy`, `progressCounterAligned`, `UnboundedProgressTheorem`, `unboundedProgressAliasCounterexample`, `progressAliasCounterexample`, `progressCounterContinuationRejected`, `repairedContinuationPremisePositive` | **proved on the approved repaired alias; repaired shape awaits end-of-CP4 re-review**: every lifecycle rule strictly consumes the same-target potential, each target change contributes a fresh `K + 4` interval, lifecycle traces preserve program/continuation bounds and precedence acyclicity, and finite unloading descent proves no-deadlock. The old continuation shape remains constructively refuted at `K=0`; the repaired premise rejects that countermodel and `AlignedTransitions` restores the paper's single global equality discipline. |
| Def 67 | `SupportEdge`, `SupportPath`, `supportClause`, `supportSet`, `isSupported` | executable bounded least-support computation; Equation 62 includes both precedence and immediate-parent edges |
| Lem 68 | `ReachedFromEmpty`, `RegistrationProtocol`, `RegistrationProvenance`, `ParentRegistrationYield`, `SupportWellFoundedResult`, `supportWellFoundedTheorem`, `supportWellFoundedTheoremProof` | **proved (finite specialization)**: reached-trace provenance preserves strict protocol ranks for every registration; parent and precedence edges strictly increase rank, so their union is well founded. The executable bounded support closure is a fixed point, is contained in every Boolean solution, and contains every solution by well-founded rank induction, hence the Definition-67 solution is unique. Legal post-remove raw-name reissue remains allowed. The finite host's documented one-source-head/many-name over-approximation remains unchanged |
| Def 69 | `TransitionComponentTotal`, `TraceComponentsTotal`, `ActiveFiberProvidesAll`, `buildCertifiedActionTrace`; rejected diagnostic `UninterruptedComponentTotalOnProvision` | **CP4 statement repair; re-review required**: totality now ranges over actual checked actor boundaries in an interleaved trace, hence every activation that finishes has every declared provision in its actual table. The old uninterrupted `ProgramFinishes` reading is retained only to type the committed countermodel |
| Lem 70 | `SupportMatchesActive`, `RegistrationDiscipline`, `supportAtQuiescenceTheorem`, `supportAtQuiescenceTheoremProof`, `reachedActiveFibersProvideAll`, `reachedNonRetiredChildParentOpen` | **proved; repaired statement awaits end-of-CP4 re-review**: actual Active-table totality follows from repaired trace-indexed Definition 69; child-retirement provenance keeps every non-retired child's parent open; quiescence and failure-freedom make the runtime Active predicate a Definition-67 fixed point; Lemma 68 uniqueness identifies it pointwise with executable support |
| Lem 71 | `activationEffectTransposition` | **partial**: generated-monoid effect commutation premise is projected; control applicability frames remain open |
| Lem 72 | `GenerationActionSubsequence`, `RegistrationGeneration`, `RegisteredGenerationsDuring`, `EpisodeGenerationDeletedActor`, `WithdrawnGenerationResult`, `ControlEquivalentOutsideGenerations`, `DeletionResult`, `ActualEffectFrame`, `InactiveLeafDeletionPlan`, `checkedLifecycleAfterInactivePlan`, `buildCurrentRegisteredDeletionPlan`, `CurrentRegisteredInactiveFibers`, `reachedCurrentRegisteredInactive`, `CurrentRegisteredInactiveLeaves`, `currentRegisteredLeavesGivePlan`, `GenerationEnvironmentBounded`, `generationTraceScanPreservesUnique`, `currentGenerationOutsideImpliesActorOutsidePlan`, `checkedLifecycleAfterCurrentRegisteredPlan`, `deletionBeforeFromRegisteredDuring`, `decEpisodeGenerationDeletedActor`, `filterGenerationActions`, `splitLocatedNoRegisteredSegments`, `DeletionTraceSkeleton`, `assembleDeletionResult`, `deletionTheorem` | **CP4 Findings #8 repair / partial; re-review required**: filtering, no-episode evidence, outside controls, and endpoint withdrawal use exact `(raw name, birth ordinal)` generations, so later legal reissues survive. A checked quiet-root countermodel proves the old raw filter wrong and the new filter right. Actual-effect frames cover all ten tags, every surviving lifecycle rule remains checked-applicable after indexed Inactive-leaf deletion, scanner ordinal bounds prove the complete pre-episode segment is retained verbatim, the total filter constructs the dependent subsequence whenever each kept replay action fires, and global no-episode/totality evidence is constructively split at exact generation boundaries. Trace/result assembly is proved conditional on filter success and the three exact endpoint invariants. The exact-generation Inactive-leaf plan and actor-outside projection are executable; generation-indexed no-episode evidence now proves the Inactive half of the current-R boundary invariant. Proving current R names are childless from disciplined registration, discharging selected-episode replay/recovery, and proving effect/control/withdrawal endpoint evidence remain open. |
| Thm 73 | `RegistrationActivation`, `SurvivingRegistration`, `DeletedClosingRegistration`, `VestigialEndpointGeneration`, `RegistrationGenerationBijection`, `RegistrationEventMatch`, `RegistrationTraceCorrespondence`, `ExternalRootBirthCorrespondence`, `RegistrationCorrespondenceByGeneration`, `CurrentEndpointRenaming`, `SystemEquivalentByRenamingModuloVestigial`, `CanonicalRegistrationCorrespondence`, `ConfluenceResult`, `confluenceTheorem` | **statement submitted for round-10 review, finite specialization**: surviving births are matched by activation-local parent positions; discarded births carry later `L-Unload parent` evidence and are stamped separately. Current generation coupling bijects only non-vestigials. Final effects remain exact under renaming, controls are exact on non-vestigial domains, and every unmatched present name must be a retired/clean-Inactive/empty-table/childless/unsupported discarded generation. Full public-premise checks cover fresh choice, cross-parent interleaving, the earlier 24/18 activation reset, and paper-normal no-O-Remove 23/18 and 27/18 vestigial endpoints; a supported ServiceA provider is rejected as vestigial. Removed historical-root permutation is still rejected. Constructive deletion/sorting and general endpoint assembly remain unproved |

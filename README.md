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
  dependency values, components, intrinsically total committed views,
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
- `DGamma.CP4ProgressChecks`: checked overlong-initial-continuation
  countermodel showing the current Theorem-66 alias needs an explicit initial
  continuation bound before its numeric conclusion can be inhabited.
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
| Lem 54–57 | `VestigialEndpointGeneration`, `vestigialEndpointGeneration`, structural rule inventory/equivariance/registration facts | **partial**: the exact Lemma-57 inert endpoint shape (discarded current birth, retired, clean Inactive, empty installed table, childless, unsupported) is executable and live fibers are proved unable to inhabit it; the operational rule-bisimulation clauses and Lemmas 54–56 are not separately complete |
| Def 58 | `registryWellFormed`, `wellFormed`, `viewBindingsInvariant` | executable decision procedure; committed views require installed providers **and matching provider-table keys**, plus parent, disjointness, and acyclicity checks |
| Thm 59 | `preservationTheorem`, `preservationTheoremProof`, `checkedTransitionTargetValid`, `applyActionDeterministic` | raw invariant preservation proved by exhaustive rule dispatch; checked target admission and same-action determinism separately proved |
| Def 60 | `ReachableSuffix`, `IteratorStage`, `iteratorStageEffect`, `TraceEffectGenerator`, `TraceEffectTransformation`, `runTraceEffectTransformation`, `IteratorYieldAgreement`, `TraceIndependent`, `PrefixRecoveryIndependent` | full-effect-state M(i): actual forwards, every statically reachable continuation forward, and every per-origin yielded inverse generate each actor's partial transformation monoid; cross-actor monoids commute and inverse+continuation yields are stable; empty traces remain constructibly non-vacuous |
| Thm 61 | `AccumulatorHandle`, `actualAccumulatorAt`, `accumulatorEffectMap`, `ForeignReplay`, `recoveryExactnessTheorem` | **stated**: L-Begin anchored; all premises and conclusions use the same full effect state; temporal accumulator-factorization induction remains open |
| Cor 62 | `terminalRecoveryTheorem`, `raiseMapIsIdentity`, `foreignReplayEmpty` | **stated**: one full-effect replay equation; L-Raise identity and the empty replay core are proved, but terminal recovery remains open |
| Thm 63 | `beginSatisfactionTheorem`, `unloadGuardTheorem`, `InstallationEvolution`, `ProviderContainsConsumer`, `extractContainingProviderEpisode`, `providerValueConstantTrace`, `orderingTheorem`, `orderingTheoremProof` | **proved**: selects the same-global-trace provider episode, proves both strict boundaries, constant consumer resolution, and constant provider value; `AlignedTransitions` is the explicit dictionary-alignment premise |
| Thm 64 | `advanceStructureTheorem`, `abortDivertStructureTheorem`, `resolutionStructureTheoremProof`, `resolutionCoherenceTheorem`, `resolutionCoherenceFromTerminalRecovery` | **partial/stated**: Equation 59 and whole-episode resolution structure are proved; final packaging from Corollary 62 is proved; only terminal recovery is missing |
| Def 65 | `precedesFiber`, `PrecedenceEdge`, `PrecedencePath`, `PrecedenceAcyclic` | executable finite precedence graph and precise acyclicity premise |
| Thm 66 | `ProgressResult`, `progressTheorem`, `progressAliasCounterexample`, `searchedLifecycleMove`, `maximalQuietFromNoDeadlock`, `progressEndFromNoDeadlock`, `progressEndFromSearch` | **statement repair required; decision pending**: the current alias permits an arbitrary initial `Reloading` continuation longer than the declared program while bounding steps only by declared program length. `DGamma.CP4ProgressChecks` inhabits every premise with `K=0`, takes five same-target actor steps, and refutes the required `5 <= 4`. Search soundness, maximality, and the empty-suffix base remain proved; no alias change has been made without approval |
| Def 67 | `SupportEdge`, `SupportPath`, `supportClause`, `supportSet`, `isSupported` | executable bounded least-support computation; Equation 62 includes both precedence and immediate-parent edges |
| Lem 68 | `ReachedFromEmpty`, `RegistrationProtocol`, `RegistrationProvenance`, `ParentRegistrationYield`, `SupportWellFoundedResult`, `supportWellFoundedTheorem`, `supportWellFoundedTheoremProof` | **proved (finite specialization)**: reached-trace provenance preserves strict protocol ranks for every registration; parent and precedence edges strictly increase rank, so their union is well founded. The executable bounded support closure is a fixed point, is contained in every Boolean solution, and contains every solution by well-founded rank induction, hence the Definition-67 solution is unique. Legal post-remove raw-name reissue remains allowed. The finite host's documented one-source-head/many-name over-approximation remains unchanged |
| Def 69 | `TransitionComponentTotal`, `TraceComponentsTotal`, `ActiveFiberProvidesAll`, `buildCertifiedActionTrace`; rejected diagnostic `UninterruptedComponentTotalOnProvision` | **CP4 statement repair; re-review required**: totality now ranges over actual checked actor boundaries in an interleaved trace, hence every activation that finishes has every declared provision in its actual table. The old uninterrupted `ProgramFinishes` reading is retained only to type the committed countermodel |
| Lem 70 | `SupportMatchesActive`, `RegistrationDiscipline`, `supportAtQuiescenceTheorem`, `supportAtQuiescenceTheoremProof`, `reachedActiveFibersProvideAll`, `reachedNonRetiredChildParentOpen` | **proved; repaired statement awaits end-of-CP4 re-review**: actual Active-table totality follows from repaired trace-indexed Definition 69; child-retirement provenance keeps every non-retired child's parent open; quiescence and failure-freedom make the runtime Active predicate a Definition-67 fixed point; Lemma 68 uniqueness identifies it pointwise with executable support |
| Lem 71 | `activationEffectTransposition` | **partial**: generated-monoid effect commutation premise is projected; control applicability frames remain open |
| Lem 72 | `ActionSubsequence`, `EpisodeDeletedActor`, `RegisteredNamesDuring`, `WithdrawnNameResult`, `DeletionResult`, `deletionTheorem` | **statement under repair/review, unproved**: selected deletion is lifecycle-only; R-owned actions and relevant-time guards remain explicit; registered endpoints cover both vestigial/absent and already-absent/absent cases |
| Thm 73 | `RegistrationActivation`, `SurvivingRegistration`, `DeletedClosingRegistration`, `VestigialEndpointGeneration`, `RegistrationGenerationBijection`, `RegistrationEventMatch`, `RegistrationTraceCorrespondence`, `ExternalRootBirthCorrespondence`, `RegistrationCorrespondenceByGeneration`, `CurrentEndpointRenaming`, `SystemEquivalentByRenamingModuloVestigial`, `CanonicalRegistrationCorrespondence`, `ConfluenceResult`, `confluenceTheorem` | **statement submitted for round-10 review, finite specialization**: surviving births are matched by activation-local parent positions; discarded births carry later `L-Unload parent` evidence and are stamped separately. Current generation coupling bijects only non-vestigials. Final effects remain exact under renaming, controls are exact on non-vestigial domains, and every unmatched present name must be a retired/clean-Inactive/empty-table/childless/unsupported discarded generation. Full public-premise checks cover fresh choice, cross-parent interleaving, the earlier 24/18 activation reset, and paper-normal no-O-Remove 23/18 and 27/18 vestigial endpoints; a supported ServiceA provider is rejected as vestigial. Removed historical-root permutation is still rejected. Constructive deletion/sorting and general endpoint assembly remain unproved |

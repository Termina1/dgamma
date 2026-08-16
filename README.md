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
| Def 47 | `Registration`, `registration`, `registrationYieldTag`, `RegistrationProtocol`, `ParentRegistrationYield` | **explicit finite-host representation**: a step carries an optional deterministic catalog tag; theorem traces tie child O-Insert/O-Retire to that exact nonempty iterator stage while the evaluator remains unchanged |
| Def 48 | `DepValues`, `LocalState`, `StepEffect`, `resolveCommittedValues` | executable capability confinement: a step reads exactly declared dependency values and mutates only ambient world plus its own provision-confined table; optional registration metadata does not widen local mutation |
| Def 49 | `Lifecycle`, `installed`, `committed` | executable four-state lifecycle with outcomes |
| Def 50 | `relied`, `reliedOnBy` | executable |
| Def 51–52 | `StepEffect`, `componentProgram`, `applyAction` L-Iter/L-Finish/L-Divert/L-Raise cases | executable finite failing iterator with per-step exact recovery witnesses and LIFO accumulator; recursive/infinite iterators are not represented |
| Def 53 | `RuleTag`, `Action`, `applyAction`, `checkedApplyAction`, `Transition`, `fire`, `Transitions`, `EpisodePrefix`, `ClosedEpisode`, `episodes` | ten-rule evaluator; proof traces are checked for Def-58 targets; episode types require L-Begin left boundaries and L-Unload right boundaries |
| Lem 54–57 | structural rule inventory/equivariance/registration/vestigial facts | **not yet separately packaged as theorem declarations**; several facts hold by representation, but no proof status is claimed |
| Def 58 | `registryWellFormed`, `wellFormed`, `viewBindingsInvariant` | executable decision procedure; committed views require installed providers **and matching provider-table keys**, plus parent, disjointness, and acyclicity checks |
| Thm 59 | `preservationTheorem`, `preservationTheoremProof`, `checkedTransitionTargetValid`, `applyActionDeterministic` | raw invariant preservation proved by exhaustive rule dispatch; checked target admission and same-action determinism separately proved |
| Def 60 | `ReachableSuffix`, `IteratorStage`, `iteratorStageEffect`, `TraceEffectGenerator`, `TraceEffectTransformation`, `runTraceEffectTransformation`, `IteratorYieldAgreement`, `TraceIndependent`, `PrefixRecoveryIndependent` | full-effect-state M(i): actual forwards, every statically reachable continuation forward, and every per-origin yielded inverse generate each actor's partial transformation monoid; cross-actor monoids commute and inverse+continuation yields are stable; empty traces remain constructibly non-vacuous |
| Thm 61 | `AccumulatorHandle`, `actualAccumulatorAt`, `accumulatorEffectMap`, `ForeignReplay`, `recoveryExactnessTheorem` | **stated**: L-Begin anchored; all premises and conclusions use the same full effect state; temporal accumulator-factorization induction remains open |
| Cor 62 | `terminalRecoveryTheorem`, `raiseMapIsIdentity`, `foreignReplayEmpty` | **stated**: one full-effect replay equation; L-Raise identity and the empty replay core are proved, but terminal recovery remains open |
| Thm 63 | `beginSatisfactionTheorem`, `unloadGuardTheorem`, `InstallationEvolution`, `ProviderContainsConsumer`, `extractContainingProviderEpisode`, `providerValueConstantTrace`, `orderingTheorem`, `orderingTheoremProof` | **proved**: selects the same-global-trace provider episode, proves both strict boundaries, constant consumer resolution, and constant provider value; `AlignedTransitions` is the explicit dictionary-alignment premise |
| Thm 64 | `advanceStructureTheorem`, `abortDivertStructureTheorem`, `resolutionStructureTheoremProof`, `resolutionCoherenceTheorem`, `resolutionCoherenceFromTerminalRecovery` | **partial/stated**: Equation 59 and whole-episode resolution structure are proved; final packaging from Corollary 62 is proved; only terminal recovery is missing |
| Def 65 | `precedesFiber`, `PrecedenceEdge`, `PrecedencePath`, `PrecedenceAcyclic` | executable finite precedence graph and precise acyclicity premise |
| Thm 66 | `ProgressResult`, `progressTheorem`, `searchedLifecycleMove`, `maximalQuietFromNoDeadlock`, `progressEndFromNoDeadlock`, `progressEndFromSearch` | **partial/stated finite specialization**: search soundness, maximality consequence, and the empty-suffix quantitative base are proved; unloading-chain no-deadlock and the precedence-count bound remain open |
| Def 67 | `SupportEdge`, `SupportPath`, `supportClause`, `supportSet`, `isSupported` | executable bounded least-support computation; Equation 62 includes both precedence and immediate-parent edges |
| Lem 68 | `ReachedFromEmpty`, `RegistrationProtocol`, `RegistrationProvenance`, `ParentRegistrationYield`, `SupportWellFoundedResult`, `supportWellFoundedTheorem` | **statement under repair/review**: child insertion is tied to a tagged step that is actually an `Elem` of the parent program; yielded-parent and precedence ranks increase; legal post-remove name reissue remains allowed; a concrete child-yield witness guards non-vacuity |
| Def 69 | `ProgramFinishes`, `ComponentTotalOnProvision`, `TraceComponentsTotal` | semantic component-level totality over every successful full program execution and every component inserted anywhere in a trace; endpoint-only and runtime diagnostics are explicitly weaker helpers |
| Lem 70 | `SupportMatchesActive`, `RegistrationDiscipline`, `supportAtQuiescenceTheorem`, `supportMatchesActiveEmpty` | **statement under repair/review**: adds child retirement-before-parent-recovery to Lemma 68's yielded-registration provenance and semantic Definition-69 totality; only the empty-registry base is proved |
| Lem 71 | `activationEffectTransposition` | **partial**: generated-monoid effect commutation premise is projected; control applicability frames remain open |
| Lem 72 | `ActionSubsequence`, `EpisodeDeletedActor`, `RegisteredNamesDuring`, `WithdrawnNameResult`, `DeletionResult`, `deletionTheorem` | **statement under repair/review, unproved**: selected deletion is lifecycle-only; R-owned actions and relevant-time guards remain explicit; registered endpoints cover both vestigial/absent and already-absent/absent cases |
| Thm 73 | `LocatedGeneratedRegistration`, `NameBijection`, `RegistrationCorrespondenceByRenaming`, `SystemEquivalentByRenaming`, `CanonicalRegistrationCorrespondence`, `ConfluenceResult`, `confluenceTheorem` | **statement under repair/review, finite specialization**: correspondence is occurrence/ordinal-bijective across legal reissue; only live root generations are fixed; canonical parent blocks admit yielded child insertion and withdrawals are tied to removed registration occurrences |

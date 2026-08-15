# dgamma

`dgamma` is an executable Idris 2 mechanization of **“A Programming Paradigm for
Spatiotemporal Composability”** (Shi, Zhang, Cui). Runtime functions remain
computational data; laws and witnesses are erased with quantity `0`.

## Build

```sh
idris2 --build dgamma.ipkg
```

The package contains the approved Section 3 checkpoint and the Checkpoint 2
Section 4 calculus/metatheory candidate.

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
- `DGamma.Calculus`: components, intrinsically total committed views,
  name-unique registries, four-state fibers, target/quiet/relied predicates, the
  ten executable rules, indexed transition traces, and episode extraction.
- `DGamma.Metatheory`: executable well-formedness and precise statement types
  for Preservation, recovery exactness/terminal recovery, spatial ordering,
  and resolution coherence, plus their supporting trace predicates.
- `DGamma.CalculusChecks`: an executable provider/consumer lifecycle regression
  whose recovery, active-coeffect withdrawal, and final well-formedness checks
  all evaluate to `True`.

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
| Def 43 | `Component`, `componentDependencies`, `componentProvisions`, `provisionSound` | executable **restricted normalization**: the final local provision table is immutable component data and becomes visible only in `Active`; computed table values are not modeled |
| Def 44 | `Parent`, `Fiber`, `View`, `freshFiber` | executable; views are intrinsically total on the exact dependency list |
| Def 45 | `Registry`, `SystemState`, `activeCoeffects`, `providerOf` | executable; registry names and coeffect keys are intrinsically unique |
| Def 46 | `targetFiber`, `targetAt`, `quietFiber`, `quiet` | executable |
| Def 47 | `Registration`, `registration` | **partial/restricted**: checked O-Insert/O-Retire pair is executable, but `StepEffect` has no nested-registration yield channel |
| Def 48 | `ConfinedStep` | **structural restricted fragment**: steps cannot access any registry; own-table mutation/declared coeffect reads are normalized away, stronger than the write boundary but less expressive than the paper |
| Def 49 | `Lifecycle`, `installed`, `committed` | executable four-state lifecycle with outcomes |
| Def 50 | `relied`, `reliedOnBy` | executable |
| Def 51–52 | `StepEffect`, `componentProgram`, `applyAction` L-Iter/L-Finish/L-Divert/L-Raise cases | executable finite failing iterator with per-step exact recovery witnesses and LIFO accumulator; recursive/infinite iterators are not represented |
| Def 53 | `RuleTag`, `Action`, `applyAction`, `Transition`, `Transitions`, `EpisodeTrace`, `episodes` | ten-rule evaluator plus equation-indexed inductive LTS and closed/maximal installed intervals |
| Lem 54–57 | structural rule inventory/equivariance/registration/vestigial facts | **not yet separately packaged as theorem declarations**; several facts hold by representation, but no proof status is claimed |
| Def 58 | `wellFormed`, `parentChainSafe`, `pairwiseProvisionDisjoint`, `lifecycleProvidersInstalled` | executable decision procedure; clauses 3–4 use intrinsic total views and installed-provider checking; acyclicity is additionally checked |
| Thm 59 | `preservationTheorem`, `applyActionDeterministic` | Preservation precisely stated, unproved (`TODO(proof)`); same-action evaluator determinism proved |
| Def 60 | `stepPartialEffect`, `programPartialEffect`, `ComponentsIndependent`, `AllComponentsIndependent` | **restricted** exact-equality/whole-program partial-effect independence; reachable-iterator continuation stability is not fully encoded |
| Thm 61 | `OpenEpisodeTrace`, `ForeignReplay`, `recoveryExactnessTheorem` | exact world-state recovery statement at every open episode prefix; unproved (`TODO(proof)`) |
| Cor 62 | `EpisodeTrace`, `terminalRecoveryTheorem` | exact world-state terminal recovery against foreign replay; stated, unproved (`TODO(proof)`) |
| Thm 63 | `ResolvesAt`, `ProviderAvailable`, `ProviderValueConstant`, `OrderingResult`, `providerVisibilityTheorem`, `orderingTheorem` | all three clauses (start order, close order, provider-table constancy) precisely stated; unproved (`TODO(proof)`) |
| Thm 64 | `transitionResolutionCoherent`, `ReloadingThroughout`, `ResolutionExit`, `ResolutionOutcome`, `resolutionCoherenceTheorem` | Equation 59 plus exact Finish vs Divert/Raise-and-terminal-recovery dichotomy stated; unproved (`TODO(proof)`) |

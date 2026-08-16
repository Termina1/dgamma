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
- `DGamma.Calculus`: capability-confined dynamic per-fiber tables, declared
  dependency values, components, intrinsically total committed views,
  name-unique registries, the four-state lifecycle, all ten executable rules,
  a checked proof-indexed LTS, and episode extraction.
- `DGamma.Metatheory`: executable well-formedness and precise statement types
  for Preservation, recovery exactness/terminal recovery, spatial ordering,
  and resolution coherence, plus their supporting trace predicates.
- `DGamma.CalculusChecks`: dynamic-table/dependency-consumption regressions plus
  executable coverage of all ten tags, both L-Divert alternatives, stale empty
  iterators, failure, relied/L-Unload ordering, recovery, and removal.

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
| Def 47 | `Registration`, `registration` | **partial/restricted**: checked O-Insert/O-Retire pair is executable, but `StepEffect` has no nested-registration yield channel |
| Def 48 | `DepValues`, `LocalState`, `StepEffect`, `resolveCommittedValues` | executable capability confinement: a step reads exactly declared dependency values and mutates only ambient world plus its own provision-confined table |
| Def 49 | `Lifecycle`, `installed`, `committed` | executable four-state lifecycle with outcomes |
| Def 50 | `relied`, `reliedOnBy` | executable |
| Def 51–52 | `StepEffect`, `componentProgram`, `applyAction` L-Iter/L-Finish/L-Divert/L-Raise cases | executable finite failing iterator with per-step exact recovery witnesses and LIFO accumulator; recursive/infinite iterators are not represented |
| Def 53 | `RuleTag`, `Action`, `applyAction`, `checkedApplyAction`, `Transition`, `fire`, `Transitions`, `EpisodePrefix`, `ClosedEpisode`, `episodes` | ten-rule evaluator; proof traces are checked for Def-58 targets; episode types require L-Begin left boundaries and L-Unload right boundaries |
| Lem 54–57 | structural rule inventory/equivariance/registration/vestigial facts | **not yet separately packaged as theorem declarations**; several facts hold by representation, but no proof status is claimed |
| Def 58 | `registryWellFormed`, `wellFormed`, `viewBindingsInvariant` | executable decision procedure; committed views require installed providers **and matching provider-table keys**, plus parent, disjointness, and acyclicity checks |
| Thm 59 | `preservationTheorem`, `checkedTransitionTargetValid`, `applyActionDeterministic` | raw invariant-preservation direction now precisely stated but unproved; checked target admission and same-action determinism proved |
| Def 60 | `OccursIn`, `TraceIndependent`, `PrefixRecoveryIndependent`, `emptyTraceIndependent` | trace-indexed actual-map commutation/definedness; no universal open `Component` quantifier; constructibly non-vacuous on every world |
| Thm 61 | `AccumulatorHandle`, `actualAccumulatorAt`, `SelectedTableRecovered`, `recoveryExactnessTheorem` | L-Begin anchored and tied to the endpoint's actual dependent accumulator; conclusion includes ambient replay and selected-table recovery; unproved |
| Cor 62 | `TerminalTableRecovery`, `terminalRecoveryTheorem`, `raiseMapIsIdentity` | L-Raise replay fixed to identity; maximal close conclusion compares ambient state and all owned tables modulo control; unproved |
| Thm 63 | `beginSatisfactionTheorem`, `unloadGuardTheorem`, `reliedProviderCannotUnload`, `ProviderContainsConsumer`, `orderingTheorem` | Equation 58 and local relied-on provider close exclusion proved; consumer/value constancy now ends before L-Unload; global provider selection remains unproved |
| Thm 64 | `AdvanceStructure`, `advanceStructureTheorem`, `AbortDivertStructure`, `abortDivertStructureTheorem`, `ResolutionStructure`, `resolutionStructureTheorem` | one-step Equation 59 plus exact Active/Unloading endpoint shapes and aborting L-Divert proved; whole-episode exit location/recovery combination remains stated |

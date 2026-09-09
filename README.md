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
  vestigial generations from deleted closing episodes. Equation-53 accumulator
  controls compare pointwise ambient values and complete ordered bindings,
  never erased `OwnedTable` certificates (CP4 Finding #12). Pushed
  accumulators canonicalize each callback input by construction, so this
  all-input relation remains compositional without adding equality dictionaries
  to the public control family.
- `DGamma.CP4AccumulatorControlChecks`: proof-distinct accumulator/table
  certificates with identical runtime observations, plus a concrete non-vacuous
  `FiberControlRelated` witness under the Finding-12 relation and the rejected
  old exact-state obligation retained as a diagnostic.
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
  action. `CP4DeletionPostCloseFold`, `CP4DeletionWithdrawalJoin`, and
  `CP4DeletionTheorem` now thread these results through both dependent filters
  and complete Lemma 72.
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
  Finding-8 checked reuse countermodel (necessity evidence for global freshness,
  not a paper or implementation bug),
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
  `DGamma.CP4DeletionEmptyTableInvariant` proves from public exact-generation
  no-episode evidence that every current R table stays empty across the checked
  trace. `DGamma.CP4DeletionPlanEmpty` constructively identifies every plan leaf
  with a current R generation using the plan's outside projection, thereby
  deriving `EmptyTableInactivePlan`; `DGamma.CP4DeletionPlanEffects` then proves
  that erasing the complete plan preserves exact ambient/ordered-table effects
  without registry extensionality. `DGamma.CP4DeletionSelectedDeletedPlan`,
  `DGamma.CP4DeletionSelectedDeletedCore`,
  `DGamma.CP4DeletionSelectedDeletedOrchestration`, and
  `DGamma.CP4DeletionSelectedDeletedDispatch` propagate the selected replay
  boundary across every deleted R orchestration head. Fresh O-Insert prepends an
  empty Inactive leaf, idempotent O-Retire updates the exact leaf, and O-Remove
  drops it; all three keep the survivor fixed while transporting complete plans
  across ordered runtime bindings rather than equating uniqueness proofs.
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
  complete current-R plan, an ordered selected-exempt control skeleton against
  the plan target, and checked well-formedness. The skeleton retains exact
  registry domain/order (hence R absence); its selected cell keeps component,
  parent, and retirement exact while allowing the erased lifecycle to differ.
  A separate erased certificate retains the survivor's exact clean-Inactive
  selected cell, which is required by provider and reliance scans and is
  preserved by every foreign action.
  Outside-control agreement is now derived from this one coherent invariant.
  `DGamma.CP4DeletionSelectedOwn` combines scanner stamp coherence with the
  public selected/R exclusion, commutes every selected installed replacement
  through the complete plan, and preserves that ordered skeleton while the
  survivor skips the action. The selected recovery dispatcher now also proves
  retirement stability for all possible interior L-Advance/L-Divert/L-Leave
  heads, so `deletedSelectedInstalledHeadPreservesEpisodeBoundary` remains
  exhaustive under the stronger boundary. `DGamma.CP4DeletionSelectedForeignControlCore`
  proves the first control-rebuild layer: lookup presence, parent presence,
  ordered provision-disjointness, no-child, retirement/Inactive observations,
  and foreign retirement are invariant across the skeleton. The remaining
  `DGamma.CP4DeletionSelectedForeignOrchestration` uses those frames to rebuild
  all three retained orchestration rules (O-Insert/O-Retire/O-Remove), preserves
  the ordered skeleton, proves checked well-formed targets, and joins each target
  to the already-transposed Definition-60 output.
  `DGamma.CP4DeletionSelectedForeignLifecycleCore` begins the retained lifecycle
  half with an ordered runtime/control source relation, a saturated structural
  guard frame, and proved lifecycle-result constructors for L-Begin, empty
  L-Finish, L-Raise, L-Divert, L-Leave, and reset-to-Inactive L-Unload. Successful
  effectful L-Advance composes through the named
  `pushLocalUndoRuntimeRelated` keystone.
  `DGamma.CP4DeletionSelectedForeignLifecycleAnchorCore`,
  `DGamma.CP4DeletionSelectedForeignLifecycleAnchorEndpoint`,
  `DGamma.CP4DeletionSelectedForeignLifecycleAnchorTrace`, and
  `DGamma.CP4DeletionSelectedForeignLifecycleAnchorOpen` split the retained
  lifecycle anchor proof into its two honest cases. Closed consumers expose the
  exact Definition-65 edge rejected by `NoDependentClosingEpisode`; an
  open-at-quiescence consumer uses protocol-rank acyclicity plus Lemma 70 and
  pairwise provision uniqueness to exclude an Inactive selected provider.
  Occurrence location, installed-prefix splitting, and component preservation
  across checked traces are constructive and proof-irrelevance-free.
  `DGamma.CP4DeletionSelectedForeignLifecycleFrame` consumes either anchor to
  construct the same saturated ordered guard frame without registry equality.
  `DGamma.CP4DeletionSelectedForeignLifecycleGuards` folds those source cells
  into exact first-provider and complete `resolveView` equality for every owner
  dependency, retaining executable registry scan order rather than replacing it
  by lookup extensionality.
  `DGamma.CP4DeletionSelectedForeignLifecycleReplayCore` fixes the common
  concrete replay result (raw step, checked step, and next ordered controls) and
  projects every saturated source relation back to the selected-exempt skeleton.
  `DGamma.CP4DeletionSelectedForeignLifecycleBegin` now inhabits that result for
  L-Begin: it transports the exact dependent target view, reconstructs the
  survivor's declared continuation/identity accumulator, proves Preservation,
  and replaces both ordered foreign controls.
  `DGamma.CP4DeletionSelectedForeignLifecycleDivert` does the same for retained
  L-Divert: exact ordered target resolution preserves the stale-target guard,
  related accumulators/views become related Unloading controls, and the real
  survivor transition is checked by Preservation.
  `DGamma.CP4DeletionSelectedForeignLifecycleLeave` reconstructs retained
  L-Leave analogously from related Active controls: the saturated ordered target
  scan preserves the stale-target guard, both cells enter related Unloading
  controls, and Preservation supplies the checked survivor step.
  `DGamma.CP4DeletionSelectedForeignLifecycleUnload` transfers the false
  reliance guard, executes the survivor's own related accumulator on its actual
  ambient/table input, resets both controls to the common Inactive outcome, and
  proves the concrete survivor step checked. Ambient/table comparison remains
  correctly owned by the already-transposed effect layer.
  The anchor's closed/open eliminations, Lemma-70 endpoint bridge, occurrence
  splitting, and installed component transport are proved.
  `DGamma.CP4DeletionSelectedForeignLifecycleAnchorClassify` now gives every
  exact retained lifecycle occurrence its action-specific installed point
  (after L-Begin, before every other lifecycle rule) and scans forward to the
  first close rather than inspecting the raw final installed bit. A closing
  branch reconstructs the exact located activation even across later
  close/reopen or remove/reinsert reuse. `SelectedUnloadRelianceAnchor` records
  the critical alternative at the selected episode's own L-Unload source, so a
  later selected activation or reused raw endpoint is never assumed Inactive.
  The `DGamma.CP4DeletionSelectedForeignLifecycleAnchorReliance*` split proves
  the missing stays-installed exclusion: intrinsic committed views, current
  well-formedness, and pairwise provision uniqueness identify any selected
  provider candidate with the owner's committed provider; resolution constancy
  then contradicts the selected L-Unload reliance guard. The split is an
  elaboration-performance boundary only. `DGamma.CP4DeletionSelectedForeignLifecycleProviderFrame`
  joins that evidence with the closed/open precedence alternatives (including
  Lemma 70) and constructs the same saturated ordered guard frame without raw
  endpoint identity or registry equality.
  `DGamma.CP4DeletionSelectedForeignLifecycleAdvanceOutcome` factors the
  selected boundary through its generated transformation and instantiates the
  repaired Equation-55 outcome clause. The concrete L-Advance module then
  reconstructs empty finish/divert, exact-error raise, and every successful
  finish/iter/landing-divert survivor; yielded inverse equivalence composes via
  `pushLocalUndoRuntimeRelated`. The split
  `DGamma.CP4DeletionSelectedForeignLifecycleAdvanceDispatch*` modules project
  failure-aware outcome agreement to those concrete evaluator branches, and
  `DGamma.CP4DeletionSelectedForeignLifecycleDispatch` is the exhaustive
  five-rule provider-evidence dispatcher. Deleted R O-Insert/O-Retire/O-Remove
  heads now preserve the selected boundary and derived empty-table invariant.
  `DGamma.CP4DeletionRelationalBoundary` is the primary selected-to-suffix
  interface: it relates the actual survivor to the complete plan target by
  ordered effects and an ordered control skeleton with extensional accumulators.
  The former exact snapshot boundary
  embeds as a specialization, but selected recovery is never strengthened to
  function/proof equality. `selectedUnloadClosesEffectBoundary` identifies the
  boundary model's handle with checked L-Unload's handle and closes exact
  post-episode effect agreement with the untouched survivor.
  `DGamma.CP4DeletionRelationalSuffixFold` proves the simultaneous relational
  suffix induction; its deleted heads are unconditional and retained heads
  consume the explicit `RelationalActionReplayer`. The new relational action
  core proves ordered lookup/edit/guard algebra, the lifecycle-source module
  derives exact provider/target/reliance observations from effect plus control
  relations, and `DGamma.CP4DeletionRelationalActionOrchestration` now inhabits
  the replayer for O-Insert/O-Retire/O-Remove; all lifecycle tags are now
  replayed constructively as well. The located-episode splitter
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
- `DGamma.CP4IndependenceNonVacuity`, `DGamma.CP4RestrictionChecks`, and
  `DGamma.CP4FailureOutcomeChecks`: Finding-7 order-preserving Definition-60
  restriction, reverse-order old/new/actual regression, and nonempty repaired
  `TraceIndependent` / `PrefixRecoveryIndependent` witnesses. Finding #13 also
  retains exact L-Raise errors in Equation-55 outcome agreement; a two-error
  countermodel inhabits the rejected old premise, refutes endpoint controls,
  and is rejected by the repaired premise, while a genuinely failing singleton
  trace constructively satisfies the repair.
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
| Def 51–52 | `StepEffect`, `componentProgram`, `applyAction` L-Iter/L-Finish/L-Divert/L-Raise cases, `pushLocalUndoRecoversStep`, `pushLocalUndoRuntimeRelated`, `interUndoNormalizationRuntimeIdentity` | executable finite failing iterator with per-step exact recovery witnesses on canonical restricted sources and a proved canonical composed-accumulator chain; accumulators normalize before and after each captured undo, making the canonical evaluator domain explicit while preserving reachable behavior; the two-step old/new runtime regression remains bit-identical; recursive/infinite iterators are not represented |
| Def 53 | `RuleTag`, `Action`, `applyAction`, `checkedApplyAction`, `Transition`, `fire`, `Transitions`, `EpisodePrefix`, `ClosedEpisode`, `episodes` | ten-rule evaluator; proof traces are checked for Def-58 targets; episode types require L-Begin left boundaries and L-Unload right boundaries |
| Lem 54–57 | `VestigialEndpointGeneration`, `vestigialEndpointGeneration`, `InactiveLeafDeletionPlan`, `checkedLifecycleAfterInactivePlan`, structural rule inventory/equivariance/registration facts | **partial**: the exact Lemma-57 inert endpoint shape is executable and live fibers are proved unable to inhabit it. Its control-applicability direction is proved constructively for every lifecycle rule through an indexed multi-leaf deletion plan (target/capability/reliance guards plus checked replay); the converse operational clauses and Lemmas 54–56 are not separately complete |
| Def 58 | `registryWellFormed`, `wellFormed`, `viewBindingsInvariant` | executable decision procedure; committed views require installed providers **and matching provider-table keys**, plus parent, disjointness, and acyclicity checks |
| Thm 59 | `preservationTheorem`, `preservationTheoremProof`, `checkedTransitionTargetValid`, `applyActionDeterministic` | raw invariant preservation proved by exhaustive rule dispatch; checked target admission and same-action determinism separately proved |
| Def 60 | `EffectStateRelated`, `ReachableSuffix`, `IteratorStage`, `iteratorStageEffect`, `iteratorStageOutcome`, `IteratorStageOutcome`, `IteratorOutcomeAgreement`, `TraceEffectGenerator`, `TraceEffectTransformation`, `runTraceEffectTransformation`, `restrictOwnedPreservingOrder`, `restrictOwnedPreservingOrderIdempotent`, `yieldedInverseStepRecovery`, `IteratorYieldAgreement`, `TraceIndependent`, `PrefixRecoveryIndependent`, `singletonTraceIndependent`, `strengthenedRelationRejectsOrderMismatch`, `oldFailurePremiseAccepted`, `repairedFailurePremiseRejected`, `divergentFailuresBreakControl`, `agreeingFailureTraceIndependent` | **CP4 Finding #13 statement repair; re-review required**: full-effect-state M(i) contains actual forwards, every statically reachable continuation forward, and every per-origin yielded inverse. Findings #7/#9/#10/#11/#12 preserve evaluator order, normalization rhythm, exact ordered tables, canonical recovery, and runtime accumulator controls. Equation 55 now also retains exact observable L-Raise errors instead of treating every failure as undefined; successful continuation/inverse clauses are unchanged. A checked two-error countermodel inhabits the rejected old premise and refutes final controls, while the repaired premise rejects it and admits a genuinely failing singleton trace. Cross-actor monoids commute, successful yields and failure outcomes are stable, and all rejected weaker relations remain pinned by discriminating regressions |
| Thm 61 | `AccumulatorHandle`, `AccumulatorModel`, `selectedAdvanceAccumulatorRecovery`, `selectedInstalledAccumulatorStep`, `foreignAccumulatorStep`, `accumulatorReplayAlongSegment`, `foreignReplayInitialRelated`, `recoveryExactnessTheorem`, `recoveryExactnessTheoremProof` | **proved**: L-Begin supplies the normalized identity base; every selected installed action recovers the source accumulator, every foreign action commutes across its generated inverse transformation, and simultaneous installed-trace induction constructs the exact full-effect `ForeignReplay`; Findings #9–#11 discharge ordered normalization, exact-map respect, and the canonical conditional recovery law |
| Cor 62 | `terminalRecoveryTheorem`, `terminalRecoveryTheoremProof`, `ClosingAccumulatorResult`, `appendOwnReplay`, `raiseMapIsIdentity`, `foreignReplayEmpty` | **proved**: Theorem 61 runs on the maximal installed body in the complete closed-trace generator universe; the checked L-Unload exposes the same actual accumulator and its exact full-effect target frame, then appends as the selected own step |
| Thm 63 | `beginSatisfactionTheorem`, `unloadGuardTheorem`, `InstallationEvolution`, `ProviderContainsConsumer`, `extractContainingProviderEpisode`, `providerValueConstantTrace`, `orderingTheorem`, `orderingTheoremProof` | **proved**: selects the same-global-trace provider episode, proves both strict boundaries, constant consumer resolution, and constant provider value; `AlignedTransitions` is the explicit dictionary-alignment premise |
| Thm 64 | `advanceStructureTheorem`, `abortDivertStructureTheorem`, `resolutionStructureTheoremProof`, `resolutionCoherenceTheorem`, `resolutionCoherenceFromTerminalRecovery`, `resolutionCoherenceTheoremProof` | **proved**: Equation 59, whole-episode resolution structure, Corollary-62 terminal recovery, and dependent final packaging are all constructive |
| Def 65 | `precedesFiber`, `PrecedenceEdge`, `PrecedencePath`, `PrecedenceAcyclic` | executable finite precedence graph and precise acyclicity premise |
| Thm 66 | `ProgressResult`, `progressTheorem`, `progressTheoremProof`, `actorTraceEquation61`, `progressNoDeadlockAt`, `lifecycleTracePrecedenceAcyclic`, `continuationsBoundedBy`, `transitionPreservesContinuationsBoundedBy`, `progressCounterAligned`, `UnboundedProgressTheorem`, `unboundedProgressAliasCounterexample`, `progressAliasCounterexample`, `progressCounterContinuationRejected`, `repairedContinuationPremisePositive` | **proved on the approved repaired alias; repaired shape awaits end-of-CP4 re-review**: every lifecycle rule strictly consumes the same-target potential, each target change contributes a fresh `K + 4` interval, lifecycle traces preserve program/continuation bounds and precedence acyclicity, and finite unloading descent proves no-deadlock. The old continuation shape remains constructively refuted at `K=0`; the repaired premise rejects that countermodel and `AlignedTransitions` restores the paper's single global equality discipline. |
| Def 67 | `SupportEdge`, `SupportPath`, `supportClause`, `supportSet`, `isSupported` | executable bounded least-support computation; Equation 62 includes both precedence and immediate-parent edges |
| Lem 68 | `ReachedFromEmpty`, `RegistrationProtocol`, `RegistrationProvenance`, `ParentRegistrationYield`, `SupportWellFoundedResult`, `supportWellFoundedTheorem`, `supportWellFoundedTheoremProof` | **proved (finite specialization)**: reached-trace provenance preserves strict protocol ranks for every registration; parent and precedence edges strictly increase rank, so their union is well founded. The executable bounded support closure is a fixed point, is contained in every Boolean solution, and contains every solution by well-founded rank induction, hence the Definition-67 solution is unique. Post-remove raw-name reissue remains allowed by the LOCAL O-Insert rule (Def 47), but is excluded by Theorem 73's missing GLOBAL-freshness hypothesis and the implementation's never-reused UIDs; these countermodels establish necessity, not a bug. The finite host's documented one-source-head/many-name over-approximation remains unchanged |
| Def 69 | `TransitionComponentTotal`, `TraceComponentsTotal`, `ActiveFiberProvidesAll`, `buildCertifiedActionTrace`; rejected diagnostic `UninterruptedComponentTotalOnProvision` | **CP4 statement repair; re-review required**: totality now ranges over actual checked actor boundaries in an interleaved trace, hence every activation that finishes has every declared provision in its actual table. The old uninterrupted `ProgramFinishes` reading is retained only to type the committed countermodel |
| Lem 70 | `SupportMatchesActive`, `RegistrationDiscipline`, `supportAtQuiescenceTheorem`, `supportAtQuiescenceTheoremProof`, `reachedActiveFibersProvideAll`, `reachedNonRetiredChildParentOpen` | **proved; repaired statement awaits end-of-CP4 re-review**: actual Active-table totality follows from repaired trace-indexed Definition 69; child-retirement provenance keeps every non-retired child's parent open; quiescence and failure-freedom make the runtime Active predicate a Definition-67 fixed point; Lemma 68 uniqueness identifies it pointwise with executable support |
| Lem 71 | `activationEffectTransposition`, `SelectedEffectReplayBoundary`, `foreignStepTransposesSelectedEffectBoundary`, `selectedStepPreservesEffectReplayBoundary` | **partial**: generated-monoid commutation is instantiated at every selected-episode boundary; skipped selected installed steps preserve accumulator recovery, and every foreign corrected Definition-60 map is joined to a concrete checked orchestration/lifecycle survivor step with ordered controls. Whole-trace theorem packaging remains part of Lemma 72's pending structural fold. |
| Lem 72 | `deletionTheorem`, `DGamma.CP4DeletionTheorem.deletionTheoremProof`, `postCloseSuffixFold`, `currentRegisteredWithdrawableFromTrace`, `relationalBoundaryGivesEndpointEvidence` | **proved**: the unchanged public theorem is inhabited. The selected episode and complete post-close suffix are folded with executable generation filtering; selected removal/rebegin and clean endpoints discharge the selected-static quotient; exact generated retirement occurrences are joined to scanner suffixes to prove current-generation withdrawal; endpoint effects, outside-R controls, and withdrawal are packaged into `DeletionResult`. |
| Thm 73 | `RegistrationActivation`, `SurvivingRegistration`, `DeletedClosingRegistration`, `VestigialEndpointGeneration`, `RegistrationGenerationBijection`, `RegistrationEventMatch`, `RegistrationTraceCorrespondence`, `ExternalRootBirthCorrespondence`, `RegistrationCorrespondenceByGeneration`, `CurrentEndpointRenaming`, `SystemEquivalentByRenamingModuloVestigial`, `CanonicalRegistrationCorrespondence`, `ConfluenceResult`, `confluenceTheorem` | **statement submitted for round-10 review, finite specialization**: surviving births are matched by activation-local parent positions; discarded births carry later `L-Unload parent` evidence and are stamped separately. Current generation coupling bijects only non-vestigials. Final effects remain exact under renaming, controls are exact on non-vestigial domains, and every unmatched present name must be a retired/clean-Inactive/empty-table/childless/unsupported discarded generation. Full public-premise checks cover fresh choice, cross-parent interleaving, the earlier 24/18 activation reset, and paper-normal no-O-Remove 23/18 and 27/18 vestigial endpoints; all were revalidated after Finding #10 strengthened `EffectStateRelated`, while the separate renamed-table endpoint field remains structurally unchanged. A supported ServiceA provider is rejected as vestigial. Removed historical-root permutation is still rejected. **Production surface remains frozen; its raw premise has a missing hypothesis at the frozen surface, with satisfiability under uniqueness proved for genuine closing episodes in R176. Research-only R173:** generation-scoped DeletionChain and `CP5ConfluenceCanonicalSortSpike.supportOrderingSpike` are proved. `UniqueRawNameInsertions` is IMPLEMENTED (`5450c88`), required by O17 (`511b2e6`), rejected by the R172 reuse fixture (`849d3f5`) and derived for actual reduced traces (`ecc3f6b`). O17 remains open. **R174:** its observed-value C58 cure, actual reached-shape preservation, simultaneous worklist reinspection, local right-ordinal decrease and actual selected non-Begin provenance are proved in `CP5ConfluenceCanonicalSortSpike`; early applicability, the global measure and body are not. Root placement is owner-paused after a checked provision-guard experiment, not a full-input countermodel. The R137/R172 reuse countermodels are necessity evidence for Theorem 73's missing global-freshness hypothesis: Def 47 checks local absence, Lemma 71 reasons with globally fresh registrations, and §5.1 draws UIDs fresh and never reuses them. Neither a paper nor implementation bug is claimed; the implementation satisfies this hypothesis by construction. The unfinished global sorting negation remains unproved and is no prerequisite for the revised O17. Operational sorting and general confluence are not proved. Five research holes remain after R183 (1/3/0/0/1), plus explicit producer/fixture debts; see `THM73-PLAN.md` |

### R177 research milestone (historical; superseded by R178 below)

At R177, production remained frozen and the Thm 73 research census was **six holes**
(**1/4/0/0/1**); no support-order or confluence body was closed.

| Paper / research boundary | Idris correspondence | Status |
|---|---|---|
| Thm 73 / O17 sorting measure | `CP5ConfluenceCanonicalSortSpike.canonicalWorkAcceptedObservedPairDrops` | Proved for the same supplied accepted descending pair; pair discovery/orientation and owner-paused root placement remain open |
| Def 67 / O18 exact current births | `CP5ConfluenceRenamingCompositionSpike.acceptedLeftCurrentBirth`, `acceptedRightCurrentBirth` | Proved from the accepted scanners; original located insertion and exact stamp |
| Def 67 / O18 generated static coherence | `CP5MatchedBirthMetadataSpike.acceptedSupportedGeneratedCoherenceForward`, `acceptedSupportedGeneratedCoherenceBackward` | Proved for an accepted retained-event member: actual opposite fiber, exact dependency/provision metadata, current parent stamps and parent renaming coherence |
| Def 67 / O18 support truth | `CP5ConfluenceCrossTraceSpike.canonicalSupportOrdersMatchSpike` | Open at R177; closed conditionally in R178 below |
| Thm 73 / O21 endpoint recovery | `CP5ConfluenceRenamingCompositionSpike.replayedCanonicalToOriginalEndpointSpike` | Open; authenticated-identity sizing is not a withdrawal proof |

**A9 fidelity finding:** a checked executable toy pair has quiet endpoints but
different child support after a one-sided generated retirement. Both independent
canonical capitals are not constructed, so this is **not a complete O18
counterexample**. A research-side `GeneratedOrchestrationMatched` hypothesis is
pending owner override, not implemented or assumed. See the
[R177 audit](research-tests/O6-R177-GRIND-SHIFT-AUDIT.md) and
[P2 stop/repair evidence](research-tests/O6-R177-P2-STOP-AUDIT.md).

### R178 research milestone

| Paper / research obligation | Idris correspondence | Status |
|---|---|---|
| Thm73 support comparison, explicit A9 + original uniqueness | `CP5AcceptedSupportTruthSpike.acceptedSupportedTruthForward/Backward` | proved, conditional |
| O18 canonical support-order matching | `CP5ConfluenceCrossTraceSpike.canonicalSupportOrdersMatchSpike` | proved, conditional |
| Revised root placement (A8) | `CP5AvailabilityAwarePlacement.AvailabilityAwareCanonicalInputPlacement` | checked replacement type; R174 scalar shape proved; integration open |

Five research holes remain. A8/A9 are delegated supervisor decisions pending
owner override; production stays frozen. See the [R178 audit](research-tests/O6-R178-GRIND-SHIFT-AUDIT.md) for exact scope and remaining owner decisions.

R178 validation: seeded **207/207 production package**, **30 fresh positive +10
exact-diagnostic negative** research checks passed. Optional broad legacy R11:
**incomplete** after a supervisor-approved no-verdict cost stop; no success claim.

### R179 research milestone — identity capital, not confluence

| Paper / research obligation | Idris correspondence | Status |
|---|---|---|
| Thm73 / O19 dependency countershape | `R179O19DependencyCountershape.r179EarlyConsumerBeginUnavailable`; `R179O19ObservedExecution.r179ObservedProviderEdges` | partial: authentic early consumer rejection and independently checked provider edges/WF; full current safety/bundle/blocks NOT inhabited |
| Thm73 / O21 original current-birth identity | `CP5O21EndpointIdentitySpike.acceptedLeftEndpointIdentityCapital`, `acceptedRightEndpointIdentityCapital`, `o21OriginalEndpointIdentityCapital` | proved, conditional: exact accepted current generation equals every same-name ORIGINAL birth; strict later birth excluded |
| Thm73 / O20 replay-to-right convergence | archived `R179O20FourClauseProbe` | type-only sizing of four fixed-bijection bridge clauses; no proof body |

All five existing holes and theorem surfaces are unchanged. O21 withdrawal is
unproved; A9 is threaded but not needed by the narrower identity proof. O19
safety revision remains gated on a full negative, not inferred from its partial
operational core. See the [R179 audit](research-tests/O6-R179-GRIND-SHIFT-AUDIT.md).

R179 continuation (D/E, after the first handoff gate was deferred):

| Paper / research obligation | Idris correspondence | Status |
|---|---|---|
| Thm73 / O20 generated birth clause | `CP5O20SupportedBirthBridgeSpike.supportedReplayedBirthBridge` | proved on originally supported children: actual fixed-name/parent/component right canonical occurrence and exact accepted generation triangle; A9 genuinely used |
| Thm73 / canonical birth-stamp coherence | `CP5O20SupportedBirthBridgeSpike.canonicalGeneratedBirthStampUnique` | proved from original uniqueness and authentic canonical accounting |
| Thm73 / O17 actual pair location | `CP5RankedTraceSelectionSpike.findActualRankDescent`, `locatedRankDescentAligned` | proved checked-pair/decomposition/rank/alignment output; concrete barrier fixture checked; worklist integration and orientation applicability open |

D does not cover unsupported children or ambient/table/control convergence. E
is an erased proof-producing actual-trace selector, not an operational diamond
or complete sorting loop. The same five theorem holes remain untouched.

### R179 F/G continuation (after separately ratified D/E)

| Paper obligation | Idris correspondence | Status |
|---|---|---|
| Thm73/O20 canonical endpoint support | `CP5O20SupportedEndpointCapitalSpike.canonicalSupportedEndpointView` | Proved conditional producer: actual canonical lookup/support/Active/nonretired/view-domain, from own capital and original support |
| Thm73/O20 committed view | `supportedCanonicalCommittedView` | Proved exact Active payload and stable-provider/resolvable-coeffect domain at its own endpoint; not cross-view equality |
| Thm73/O20 one-sided effects/controls | `originalThroughCanonicalReplayEffects`, `originalSupportedThroughCanonicalReplayControls` | Proved original→own canonical→actual replay transport; **not** replay→right canonical convergence |
| Thm73/O17 positive early applicability | `CP5RankedEarlyApplicabilitySpike.selectCanonicalObservedEarlyPair` | Proved guarded producer using exact existing rank observer, same-pair orientation and actual checked early right execution with exact tag; no existence/completeness/diamond theorem |
| Thm73/O17 concrete early execution | `R179RankedTraceSelectionPositive.r179CanonicalObservedEarlyChecks` | Proved real count4 selection and early Begin1; no concrete claim about the opaque combined orientation consumer |

The only old-spike changes are two authorized **visibility keywords** in
CanonicalSort: `canonicalWorkActionRank` becomes `public export` for proof
reduction; `canonicalWorkInspectOrientation` becomes `export`. Bodies/signatures,
all other old-spike bytes, production and the five protected holes remain exact.
O20 needs a cross-canonical matched-episode execution invariant producing actual
renamed ambient/table equality, resolved-input agreement and accumulated-undo
relation. F does not obtain these from metadata or assume them as new inputs.

### R180 observed-value / paired-cut milestone (research only)

| Paper frontier | Idris correspondence | Checked status |
|---|---|---|
| Thm73/O19 provider-consumer execution | `R180O19ObservedCompletion.r180FinishedProviderResolution`, `r180ConsumerBeginOutputDomains`, `r180ObservedLifecycleSuffix` | Proved actual provider resolution, consumer Begin/Finish, all Begin view domains, five checked lifecycle edges from the registered root source, and final WF. **Not** a full empty-origin/current-safety counterexample |
| Thm73/O20 internal resolution/Advance/undo | `CP5O20EpisodeSynchronizationSpike.synchronizationResolutionFromObservedHeads`, `synchronizationLocalSource`, `synchronizationStepOutcome`, `synchronizationPushedUndo` | Proved internal invariant consumers using producer-owned observed values; not proofs that nonempty paired prefixes satisfy the invariant |
| Thm73/O20 actual paired-prefix invariant | `SupportedCanonicalEpisodeSynchronization`, `synchronizationOperationalOrigin` in the same module | Precise fixed-accepted-bijection/actual-cut type; **zero-prefix instance proved** for the actual operational-left/right-canonical traces. Nonempty Begin/Advance/Finish induction remains open |
| Thm73/O20 one-sided endpoint capital | `synchronizationSupportedCanonicalPackets` | Produces R179 supported view packets at both actual canonical endpoints using accepted support transport; no cross-endpoint view or undo equality |

A14/14 and B15/15 micro-unit budgets are exhausted. No old safety revision,
O19/O20 hole body, new hole, proof escape, or production change. In particular,
unsupported children are **not** the only O20 remainder. Exact compiler attempts,
ratified stops, remaining clauses and seeded-validation scope are in the
[R180 audit](research-tests/O6-R180-GRIND-SHIFT-AUDIT.md).

### R181 actual-lifecycle / paired-registration milestone (research only)

| Paper frontier | Idris correspondence | Checked status |
|---|---|---|
| Thm73/O19 current-safety negative prerequisites | `R181O19SafetyCompletion.r181WholeTrace`, `r181TraceAligned`, `r181TraceStructure`, `r181WholeTotal` | Proved actual seven-edge empty-origin trace, designated alignment, protocol/discipline, all-boundary totality and SAME-source early consumer rejection; quiet/noFailure/both Active endpoint. **Full current-safety inhabitant still absent** |
| Thm73/O19 actual installed cuts | `CP5ObservedInstalledLifecycleSpike.InstalledCutObservation`, `inspectInstalledCutObserved`, `installedFromCutObservation`, `inspectInstalledCutCorrect`; `R181O19SafetyCompletion.r181LifecycleCutObservations` | Executable actual-payload observer and soundness/completeness proved; all five provider/consumer Begin/Iter/Finish cut observations produced. InstalledTrace/blocks/independence/bundle assembly remains |
| Thm73/O20 paired-prefix successor | `CP5O20PairedPrefixProducerSpike.synchronizationRegistrationSuccessor` | Proved matched-registration successor at BOTH actual prefix occurrences under the fixed accepted bijection; **not** canonical pair selection or complete Begin/Advance/Finish induction |
| Thm73/O20 deterministic runtime/undo | `pairedCommittedResolution`, `pairedRuntimeReplacementEffects`, `pairedSuccessfulOutcome` in that module | Actual resolver/runtime projection and deterministic successful-state/pointwise pushed-undo consumers proved; full producer/unsupported-child obligations remain |
| Thm73/O21 withdrawals | [R181 obligations](research-tests/O6-R181-O21-WITHDRAWAL-OBLIGATIONS.md) | Analysis and one disposable type-only probe; **no branch proof**, original O21 hole unchanged |

A16/16, B13/15 with ratified B12 stop, C1/3 checks. Five holes unchanged,
production frozen, no safety revision or O19/O20 bodies. One failed commit was
immediately reverted and one premature compiler invocation violated the strict
workflow; both are explicitly preserved for review in the
[R181 audit](research-tests/O6-R181-GRIND-SHIFT-AUDIT.md), not silently excused.

### R181 authorized D/E continuation (supersedes the prefix status above)

| Paper frontier | Idris correspondence | Checked status |
|---|---|---|
| Thm73/O20 actual matched Begin inputs | `CP5O20PairedPrefixProducerSpike.pairedNamedTableOwnerObserved`, `pairedNamedTableOwnersUnique`, `pairedActualProviderHeads`, `pairedActualResolvedViews` | Named-table cure proved; matched heads and complete ViewRelatedBy for actual successful resolveView outputs DERIVED from paired runtime tables/right pairwise provisions, not assumed. Full canonical prefix selection/step propagation remains open |
| Thm73/O19 actual located episodes | `R181O19LocatedBlocks.r181BlockBodiesInstalled`, `r181ProviderLocatedBlock`, `r181ConsumerLocatedBlock`, `r181ProviderBeforeConsumer`, `r181BlockLifecycleCoverage` | Both full InstalledTrace bodies and actual three-edge/two-edge LocatedOpenEpisodeBlocks proved in the SAME count7 trace, including all fields, zero-gap order and lifecycle coverage. Numeric disjointness/decomposition, uniqueness, independence and full current-safety assembly still remain |

D6/6 PASS1; E8/8 with one corrected import/qualification failure. No old spike,
safety surface, O19/O20 body, O21 branch or production change. Five holes remain.
The original disclosed protocol exception remains an independent-review concern.

### R181 authorized F continuation (supersedes D/E prefix)

| Paper frontier | Idris correspondence | Checked status |
|---|---|---|
| Thm73/O19 authoritative block decomposition | `R181O19BundlePrerequisites.r181BlocksByActor`, `r181BlocksFollowOrder`, `r181BlockRangesApart`, `r181ActorBlockDecomposition` | Complete actual3x2 decomposition proved: SAME selector, strict order, disjoint global ranges2/3/4 versus5/6 and full lifecycle coverage |
| Thm73 original raw uniqueness | `R181O19UniquenessAndBundle.r181ActualBirthPosition`, `r181OriginalUniqueInsertions` | Strong UniqueRawNameInsertions proved for all located insertions of the authentic seven-edge trace |
| Thm73/O19 replay prerequisites | `r181ReachedAndProvenance`, `r181ReplayBundleFromIndependence` | Actual reachability/provenance proved; CONDITIONAL bundle constructor derives all14 other fields. **TraceIndependent remains an explicit uninhabited input**, not a full bundle/current safety/negative |

F8/8 completed;49 retained new declarations across six research Idris files.
Remaining O19 work: actual component-specific independence, both NoGeneratedChild
body proofs and final order-swap/safety assembly. No revision or body permission.
Five inherited holes and all production/original spike files remain frozen.
The earlier reverted workflow violation remains unexcused, requiring parent-owned review.

### R181 final G resource stop (supersedes F prefix)

| Paper frontier | Idris correspondence | Checked status |
|---|---|---|
| Thm73/O19 independence prerequisite | `R181O19Independence.r181ConsumerLookupAfterBegin` | Actual consumer Begin lookup proved through checked foreign-provider frames; **NOT TraceIndependent** |
| Thm73/O19 actual stage classification | G2 declaration wholly removed | STOP2/3 under explicit supervisor resource override:566.615s manual stop,102.840s48GiB guard; both interrupted/no verdict. Third attempt unused |

50 retained declarations in seven research Idris files. Real generated-monoid
commutation and iterator-outcome stability remain unproved; F8 is still conditional.
No negative/safety revision/body permission. Full safety assembly is next shift.
The original B11/B12-1 workflow violation remains unexcused and independently reviewable.

**Owner decision (2026-09-07 16:50UTC), next shift only:** exception to R146's
countershape-first doctrine. The partial negative is accepted as sufficient to
revise AdjacentActorSwapSafety with R146(iii) support incomparability /
both-direction applicability, WITHOUT waiting for TraceIndependent. Owner's
reason: "failure mechanism fully certified; missing field unrelated to the
mechanism". Independence remains unproved capital, not a revision gate. No
current-shift surface change, full-negative claim or O19 body permission follows.
The earlier workflow violation remains unexcused.

### R182 O19 surface boundary

| Paper / research obligation | Idris correspondence | Status |
|---|---|---|
| Thm73 adjacent independent episodes, first-step boundary | `CP5ConfluenceCrossTraceSpike.AdjacentActorSwapSafety.safetyRightOpeningEarly` | Strengthened research predicate; O19 body still stated |
| Provider-before-dependent pair must not transpose | `R182O19RevisedSafetyNegative.r182DependentPairRejected` | Proved on actual R181 count7 trace; no independence assumption needed for rejection |
| Independent adjacent pair admitted in both orders | `R182O19RevisedSafetyPositive.r182IndependentSafety` / `r182IndependentTrace` | Proved concrete full safety and both actual six-edge orders; empty-key/Unit positive |

The owner-authorized change corrects our weaker predicate, not the paper or
Cordis. The five-hole census is unchanged; Unit B requires a separate gate.

R182's same owner-authorized revision series also requires **actual empty gap**
(`safetyBlocksAdjacent`), not just BlockBefore. The nine-edge intervening-Insert2
fixture has an inhabited full bundle and checked early opening; its clause-
level rejection explicitly takes the selected-gap observation. It is not a
full old-safety countermodel. The full A14 adjacent positive continues to pass.

| Thm73 research construction | Correspondence | Status |
|---|---|---|
| Exact A/A operational adjacent replay | `CP5O19AdjacentReplayProducerSpike.o19AdvanceActivationPair` | Proved lower-level producer; actual diamond/sealed result/unique transport |
| Actual first Cartesian crossing of admitted pair | `R182O19ActualCrossingPositive.r182ActualFirstCrossing` | Proved, no inputs; one of four nodes, NOT O19 closure |

### R182 status — four actual crossings, O19 still open

The first-node checkpoint above has advanced: the input-free
`R182O19AllFourCrossingsPositive.r182ActualAllFourCrossings` produces ALL FOUR
actual Cartesian crossings on A14's independent six-edge source. It retains
four sealed results, all reached bundles, the complete nonempty source-to-final
chain and transported original uniqueness. This is not an arbitrary-context
whole-block producer, not count7/ServiceA independence, and not Thm73 closure.

| Paper / research obligation | Idris correspondence | Status |
|---|---|---|
| Thm73/O19: actual-cut authentication | `CP5O19AdjacentReplayProducerSpike.o19AlignedDestination`, `o19MovedPairDestination` | Proved from aligned checked determinism, not arbitrary view equality |
| Thm73/O19: owned suffix observation/composition | `CP5O19ReplayObservationSpike.o19TwoActionTraceObserved`, `o19ComposeProduced` | Proved; actual trace/alignment, sealed fold and same reached package |
| Thm73/O19: complete concrete Cartesian execution | `R182O19AllFourCrossingsPositive.r182ActualAllFourCrossings` | Proved, no inputs; four actual node results plus full nonempty chain |
| Thm73/O19: structural iteration measure | `CP5O19ReplayObservationSpike.o19AppendFiniteCount`, `o19AppendNonEmptyCount` | Proved generic count addition; no concrete four-count certificate claimed |
| Thm73/O19: generic whole-block swap | `CP5ConfluenceCrossTraceSpike.operationalAdjacentBlockSwapSpike` | Stated/unchanged hole; universal loop, all orientations, target ranges and origin plan remain open |

See `research-tests/O6-R182-GRIND-SHIFT-AUDIT.md` for every charged failure,
per-commit fresh check, the resolved 48GiB existential-elimination boundary and
precise R183 prerequisites. The census remains **5 = 1/3/0/0/1**; production,
CP3, LocalDiamond, O17/O20/O21 and frozen suffix theorem boundaries are unchanged.

### Latest R183 status — arbitrary Begin row, not O19 closure

| Paper / research obligation | Idris correspondence | Status |
|---|---|---|
| Thm73/O19: intermediate Begin guards | `CP5O19OpeningPropagationSpike.o19OpeningAlongForeignActivations` | Proved: arbitrary aligned foreign-activation segment, all guards derived from ONE initial guard |
| Thm73/O19: arbitrary A/A first row | `CP5O19ActivationRowSpike.o19BubbleBeginRow`, `O19ActivationRow.rowNodeCount` | Proved: actual crossings, reached bundle/uniqueness/derivation and exact row count; not the full Cartesian loop or source-origin plan |
| Thm73/O19: actual generic-row instance | `R183O19GenericBeginRowPositive.r183ActualGenericBeginRow` | Proved, no inputs: both first-row crossings/count2 on R182's admitted2×2 source |
| Thm73/O19: early effect domain | `CP5O19CommutedDomainSpike.o19CommutingFramesEarlyRun`; `CP5O19ActualCommutedDomainSpike.o19ActualPairMapCommutes` | Generic partial-effect result kernel and actual commutation sublemma proved; checked controls/tags and captured-map rebasing are NOT inferred |
| Thm73/O20: actual paired selection | `CP5O20CanonicalPairSelectionSpike.selectSupportedCanonicalBlockPair`, `canonicalPairCutsWellFormed` | Proved conditional on genuine operational capital: both authoritative selected blocks and actual cut WF, fixed accepted bijection |
| Thm73/O20: selected-cut view inputs | `canonicalPairSelectedViews` in the same module | Proved internal consumer of paired effect agreement and actual successful same-dependency-list resolutions; complete prefix synchronization is open |

R183 used all30 A prerequisite slots (29 retained surfaces; A25 exhausted3
checks and was wholly discarded), one disposable O20 probe (2 expected
rejections exposing the pre-block-cut and empty-gap obligations), and all8 C
slots. O19's body was **not attempted**: arbitrary later rows, all orientations,
whole source-origin/coverage/count and installed target blocks remain open.
No O20/O17/O21 body or production surface changed. The only LocalDiamond
changes are the separately approved visibility of `RawActivationMove` and
`beginRawAfterForeignActivation`; stripping those two keywords reconstructs
973a81a. Census remains **5 = 1/3/0/0/1**.

See the [R183 audit](research-tests/O6-R183-GRIND-SHIFT-AUDIT.md),
[exact compiler ledger](research-tests/O6-R183-COMPILER-LEDGER.json), and
[archived source/diagnostic evidence](research-tests/O6-R183-COMPILER-EVIDENCE.tar.gz).

### Latest R184 status — guarded candidate selection; O19 remains open

| Paper / research obligation | Idris correspondence | Status |
|---|---|---|
| Thm73/O19: actual early partial-effect result | `CP5O19ActualCommutedDomainSpike.o19ActualPairEarlyPartialRun` | Proved by composing R183 kernel/commutation/frame projections; not checked control/tag applicability or captured-map rebasing |
| Thm73/O19: insertion resolver observation | `CP5O19InsertObservationSpike.o19ResolutionAfterCheckedInsert` | Proved: actual value and exact before/after resolver equations; insertion-target/Begin transport stopped after two exhausted units |
| Thm73/O20: fully guarded candidate search | `CP5O20SafeBlockSelectionSpike.o20SelectSafeAdjacentBlocks` | Total positive finite selector: actual empty gap, exact pre-left-cut right Begin, both derived child exclusions and original uniqueness; not target-directed canonical descent |
| Thm73/O20: actual paired Begin observations | `CP5O20BeginObservationSpike.o20ObserveSelectedBegins` | Proved: both authoritative actual components and successful resolver observations; common dependency-list transport remains open |
| Thm73/O20: paired Begin effect successor | `CP5O20BeginObservationSpike.o20SelectedBeginEffects` | Proved internal successor from pre-cut effects through actual Begins; whole-prefix effect/control synchronization remains open |

R184 retained24 declarations (A4, B12, C8). A stopped after ratified A2/A6
3/3 exhaustion in the insertion-target seam; both attempts were fully reverted.
O19 prerequisite groups(i)–(vi) remain incomplete and its body was not attempted.
Census stays **5 = 1/3/0/0/1**; all five hole declarations, LocalDiamond,
production and CP3 are byte-unchanged from their frozen baselines.
See the [R184 audit](research-tests/O6-R184-GRIND-SHIFT-AUDIT.md) for exact
remaining obligations, per-commit checks and bounded failure evidence.

### R180–R191 research milestone — O19 closed, O20 still partial

**Current research census: 4 = 1/2/0/0/1** (CanonicalSort/CrossTrace/
DeletionChain/LocalDiamond/RenamingComposition). O19 closed in R189; both O20
bodies remain open and byte-unchanged in R191. The historical milestones above
are retained, not current closure claims. Production remains frozen.

| Paper / research obligation | Idris correspondence | Current status |
| --- | --- | --- |
| Thm73 / O19 actual adjacent block swap | `CP5ConfluenceCrossTraceSpike.operationalAdjacentBlockSwapSpike` | Proved at the accepted revised safety boundary (R189); unchanged in R191 |
| Thm73 / O20 accepted common reference and search | `CP5O20SupportedReferenceSpike.o20AcceptedSupportedReference`; `CP5O20ReferenceDescentSpike.o20SearchAcceptedReference` | Proved from accepted capital; stopped order is not yet proved the goal |
| Thm73 / O20 finite inversion and physical child safety | `CP5O20FiniteInversionSpike.o20StoppedInversionAvailable`; `CP5O20InversionChildSafetySpike.o20ReachedInversionChildSafety` | Proved; physical early Begin, zero gap and exact selection wiring remain |
| Thm73 / general actual paired Begin | `CP5O20SharedBeginAdapterSpike.o20PairedActualBeginCut` | Proved from real steps and the pre-cut invariant, without a shared-component oracle |
| Thm73 / actual paired Advance/Finish/gap induction | `CP5O20PairedExecutionSpike.o20PairedExecutionCut`, `o20PairedExecutionTraces` | Proved for the native-edge paired family; canonical extraction and omitted-case completeness remain |
| Thm73 / unsupported original-birth disposition | `CP5O20CanonicalBirthDispositionSpike.o20CanonicalOriginMatchOrClosing` | Proved weaker result: authentic closing or a matched right-original birth; not the full current-name/right-canonical triangle |

R191 retains 94 new checked declarations and an eleven-edge paired integration
fixture. **A8 is O17-only initial placement**: accepted O20 inputs already supply
root-first placement. **A10 is an owner-pending child-orchestration grammar/gap
candidate**, not a fully inhabited accepted counterexample. No selector or
convergence closure is claimed.

See the [R191 ownership/design map](research-tests/O6-R191-O20-DESIGN.md),
[verification](research-tests/O6-R191-VERIFICATION.md) and
[append-only audit](research-tests/O6-R191-GRIND-SHIFT-AUDIT.md).


## R193 checked partial research milestone (115 retained)

Production remains byte-frozen at `34b21c9`; this is **not** a completion of
Theorem73. Main-lane results and exact qualifications are in
[`O6-R193-GRIND-SHIFT-AUDIT.md`](research-tests/O6-R193-GRIND-SHIFT-AUDIT.md).

| Paper correspondence | Idris research declaration | Status |
|---|---|---|
| Thm73 canonical endpoint transport, auxiliary | `CP5O20HistoryNameTransportSpike.o20HistoryEndpointPartition` | Proved: genuine vestigial branch OR historical/current-name agreement; not unconditional rebasing |
| Thm73 canonical action analysis, auxiliary | `CP5O20CanonicalActionCompletenessSpike.o20WholeCanonicalRoles`; `CP5O20SingleRoleAdvanceExtractionSpike.o20IterNativeValues`, `o20FinishOneNativeValues` | Proved unilateral role completeness and native single-role extraction; arbitrary paired alignment remains open |
| Thm73 paired execution, auxiliary | `CP5O20HistoryExecutionSpike.o20HistoryMatchedInsertCut`, `o20HistoryObservedAdvanceCut` | Proved local preservation of an input history cut; insertion stamp matching and native callback observations still explicit |
| Thm73 operational selection, auxiliary | `CP5O20SafeBlockSelectionSpike.o20EnumerateSwap`, `CP5O20SelectionCompletenessSpike.o20SelectEnumeratedComplete` | Proved actual enumeration and conditional whole-selector success; four own-cut semantic safety clauses not generally produced |
| Thm73 operational selection, auxiliary | `CP5O20BlockResolverFrameSpike.o20IncomparableInstalledEarlierBegin` | Proved whole-block owner/resolver transport for frozen `ActorLifecycleOnly`; two reference-component attachments, child exclusion and exact zero gap remain explicit |
| Thm73 protected convergence body | `CP5ConfluenceCrossTraceSpike.canonicalSchedulesConvergeSpike` | Open; no body attempt or widened statement |

A genuine eight-edge history now witnesses **physically present vestigial**
child1 being mapped to absent2 by accepted current renaming while historical
birth transport selects1. This supplies full same-inputs history data, **not**
independent canonical schedules, and is not a protected-convergence
counterexample. A second regression uses actual Begin2/child3 Insert/Finish2/
Begin1 steps with a nonempty `[ServiceA]` resolver: generic theorems produce an
earlier Begin1 and whole-block resolver equality. Its provider-backed initial
cut is physical host data, not an authenticated original/canonical history.

The 115 main declarations (A30/D10/E75) were individually checked and committed;
source is frozen at `ad77399f`. Original final LocalDiamond check V2 hit the
48GiB guard. A separately authenticated, supervisor-approved unchanged-source
52GiB retry passed (sampled 48.14221GiB); every other check retains 48GiB.
Original failed receipts are retained, not relabelled.

All **52 effective final checks passed** (45 positives, 7 expected negatives),
including all 13 changed Idris targets, package and all five spikes. This is
seeded validation, not a cold rebuild. See the [R193 audit](research-tests/O6-R193-GRIND-SHIFT-AUDIT.md)
[independent verification](research-tests/O6-R193-VERIFICATION.md),
and [lane2 integration boundary](research-tests/O6-R193-LANE2-INTEGRATION.md).
Lane2 L2R1 reports 35 checked declarations and 15 final checks at its pinned
artifact commit; L2R2 remains separately pending, and no source merge occurred.

## R194 checked partial research milestone (46 retained)

Source freeze `408bd21e`; production is still byte-frozen at `34b21c9`.
This advances Theorem73 auxiliaries, **not** Theorem73 or its selector body.

| Paper correspondence | Idris research declaration | Status |
|---|---|---|
| Thm73 replayed registration coordinates, auxiliary | `CP5O20CanonicalOrdinalAttachmentSpike.o20ReplayOrdinalBijection`, `o20SupportedReplayedOrdinalAttachment` | Proved canonical-coordinate bijection and actual supported-birth attachment; whole pairing open |
| Thm73 paired execution, auxiliary | `CP5O20ActualHistoryAdvanceSpike.o20HistoryCheckedIterCut` | Proved local successor from two actual checked Iter edges and an input cut |
| Thm73 transposition applicability, auxiliary | `CP5O20OwnCutSafetySpike.o20BlockEndReferenceComponent`, `o20BlockOpeningReferenceComponent` | Proved both formerly missing physical endpoint/reference attachments |
| Thm73 operational selection, auxiliary | `CP5O20OwnCutSafetySpike.o20ReachedInversionOwnCutSafe` | Proved native own-cut candidate success, conditional only on literal ZeroGapPending beyond native capital |
| Thm73 stopped order, auxiliary | `CP5O20OwnCutSafetySpike.o20StoppedOrderEqualsGoalZeroGap` | Proved conditional actual stoppedOrder=goalOrder; native inversion gaps must each have zero transitions |
| Thm73 protected convergence | `CP5ConfluenceCrossTraceSpike.canonicalSchedulesConvergeSpike` | Open; whole pairing/all-name rebasing/vestigial remainder and D5 bridge producer remain missing |

A30/B16 caps respected. No new proof hole or unsafe escape. No A12-variant,
root-relocation, unconditional zero-gap or sibling selector-body claim.
All **59 final checks passed** (52 positives/7 expected negatives), including
all7 changed targets, all5 protected spikes, seeded package and inherited main
fixtures. LocalDiamond passed unchanged under the standing52GiB limit; sampled
peak48.12422GiB. The frozen census remains **4=1/2/0/0/1**, with207/207 seeds.
Ten evidence-contract regressions and all independent automated audits PASS.
The owner ratified the checked partial at52e1d308; independent reviewer pending. See the
[R194 verification and evidence](research-tests/O6-R194-VERIFICATION.md),
[audit](research-tests/O6-R194-GRIND-SHIFT-AUDIT.md) and
[findings qualifications](research-tests/O6-R194-FINDINGS.md).

### R195 checked PARTIAL milestone —65/65 final validation

42 new research declarations, A26/B16; no convergence-body attempt. Supporting
Theorem73 correspondence, not additional closed paper theorems:

| Paper boundary | Idris declaration | Status |
| --- | --- | --- |
| Thm73 root replay ordinals | `CP5O20RootOrdinalBoundarySpike.o20ComposeRootReplayOrdinals` / `o20RootOrdinalsAttached` | proved composition / conditional attachment; accepted producer law open |
| Thm73 historical births | `CP5O20GenerationOnlyHistorySpike.o20WholeOriginalGenerationHistory` / `o20HistoryReplayAttachment` | proved original coverage/retention; whole paired alignment open |
| Thm73 endpoint rebasing | `R195EndpointRebaseBoundaryPositive.r195OriginalEndpointRebaseObstruction` | proved ORIGINAL-scope obstruction, not a canonical counterexample |
| Thm73 vestigial remainder | `CP5O20EndpointRebaseBoundarySpike.o20DisagreementVestigial` | proved original packet; canonical remainder/bridge open |

[Audit](research-tests/O6-R195-GRIND-SHIFT-AUDIT.md),
[findings](research-tests/O6-R195-FINDINGS.md),
[receipts](research-tests/O6-R195-MICRO-UNITS.md), and
[R196 root-contract plan](research-tests/O6-R195-ROOT-CONTRACT-MANIFEST.md).
Production, all four hole statements, O19/LocalDiamond and A11 remain frozen.

Final validation:65/65 expected results (58positive/7named negative),207/207
seeded package, all42 source receipts authenticated, census4 unchanged.
[Verification](research-tests/O6-R195-VERIFICATION.md). Whole pairing, exact
canonical all-name rebasing and convergence remain open; independent review
is parent-owned and pending.

Supervisor final gate RATIFIEDd7b2fc98 as checked PARTIAL; artifact-only gate
note/clean close authorized. Independent reviewer remains parent-owned/pending.


### R196 research milestone — actual root laws (overall checked PARTIAL)

The producer contracts and their actual canonical/operational root-law consumers
are checked. Production remains unchanged; the whole paired fold and endpoint
bridge remain open (four inherited holes).

| Paper correspondence | Idris declaration | Status |
|---|---|---|
| Thm73 auxiliary: adjacent root ordinals | `CP5ConfluenceLocalDiamondSpike.operationalRootOrdinalPreserved` / `adjacentOriginRootOrdinal` | proved, producer-filled |
| Thm73 auxiliary: deletion root ordinals | `CP5ConfluenceDeletionChainSpike.deletionProducerRootOrdinalPreserved` / `deletionBuiltRootOrdinalPreserved` | proved, producer-filled |
| Thm73 auxiliary: exact canonical root law | `CP5O20RootReplayLawProducerSpike.o20CanonicalRootReplayOrdinals` | proved |
| Thm73 auxiliary: exact replayed-left composition | `CP5O20RootReplayLawProducerSpike.o20PermutedCanonicalRootReplayOrdinals` | proved |
| Thm73 whole pairing / canonical endpoint bridge | existing protected obligations | open; not claimed by root laws |

Evidence:13 guarded source commits; B133/133 and second-window127/127 expected
validation outcomes, two seeded207/207 package checks,18 evidence-contract tests.
All276 raw invocations retained, including3 rejected snapshots; no resource stop.
See `research-tests/O6-R196-GRIND-SHIFT-AUDIT.md`, refreshed cost inventory and
per-module table.111 excluded fixture/legacy paths are explicitly not re-checked.


## R197 — source-frozen PARTIAL history-fold / observed-provider milestone

R197 adds **33 checked declarations in seven new research modules**. It does
**not** prove universal canonical pairing or Theorem73. Production and all
protected theorem/module surfaces remain unchanged; fresh census is
**4 = 1/2/0/0/1**. Status below supersedes older shift status, not prior evidence.

| Paper/research obligation | Idris correspondence | Status |
|---|---|---|
| Thm73 support: original matched root + exact canonical/replayed ordinal | `CP5O20RootStageAttachmentSpike.o20CanonicalRootOrdinalAttachment`, `o20PermutedCanonicalRootOrdinalAttachment` | proved from actual root correspondence, original uniqueness and R196 laws; no supplied opposite birth |
| Thm73 support: finite native history preservation | `CP5O20StampedHistoryFoldSpike.o20StampedStageCut`, `o20StampedHistoryCut` | proved **conditional on a supplied stage synchronization; not universal pairing** |
| Thm73 support: accepted canonical endpoint/scanner synchronization | `CP5O20CanonicalSynchronizationGoalSpike.o20CanonicalSynchronizationGoal` | precise erased TYPE FUNCTION only; no inhabitant/postulate; reconstructed trace equality is stronger and absent |
| Thm73 support: expected-map all-name canonical/replayed endpoint cut and D5 bridge | existing consumers only | unproduced; original vestigial packages do not supply the canonical/replayed `MaybeFiber` controls |
| Native provider head observation, before/after retirement | `CP5ProviderHeadObservedSpike.providerHeadObserved` | executable total producer; own native guard equation + both native head equations |
| Generic observed packet → before/after provider equality | attempted `providerHeadRetirementFromObserved` | **not retained/proved**; D5 STOP3/3, full revert, exact hidden-if constraint archived |

Fixtures cover an actual eleven-edge R191 stamped run from an empty origin,
retained R193/R195 present-vestigial history through literal zero-edge epsilon,
and two-binding active/inactive provider heads. The R178 unequal role words
are **excluded by accepted E9**, not a convergence counterexample.

B stops at the owner-approved eligibility boundary; C has **zero attempts**.
No unilateral native edge is erased as “stuttering”. Final validation is
**pending at this source-freeze entry**: immutable plan143 source targets
(ALL136 inherited R196 current targets +7 new) +1 seeded package build.
See `research-tests/O6-R197-GRIND-SHIFT-AUDIT.md` and D5 STOP audit.


## R197 — final validation complete; checked PARTIAL

Final **144/144** planned invocations have authenticated expected outcomes:
143 source checks (136 inherited R196 current targets +7 new) and the seeded
package build, including7 exact expected-negative checks. No resource stop,
source mutation or extra Building line. The full189-invocation ledger retains
11 rejected micro-attempts;178 expected PASS,33 source receipts.18 adversarial
evidence tests and independent record/receipt/lock/frozen audits pass.

A remains **conditional on a supplied stage synchronization; not universal
pairing**. B's expected-map all-name rebasing/bridge is unproduced; C0. D's
observed native provider producer and two-binding fixtures are proved, but
optional generic consumer D5 stopped3/3 and is fully reverted. Census is still
**4=1/2/0/0/1**; production/frozen surfaces unchanged. No cold build or fresh
certification of the111 excluded inventory paths is claimed.

The detached validation completed at08:15:37Z on2026-09-09. Provider usage-limit
interruption delayed E3 publication/final gate; the supervisor explicitly
resumed **compiler-free artifacts only**, explicitly closing further proof work.
See `research-tests/O6-R197-VERIFICATION.md` and the committed R197 evidence.


## R197 owner gate

Owner ACCEPTED checked PARTIAL at3a42d1f2 and authorized this E4 artifact-only
note/clean close; E3 was pushed by the supervisor. Exact ruling is preserved
in `research-tests/O6-R197-OWNER-FINAL-GATE.md`. A remains conditional, B's two
named producers/bridge OPEN, C0/ineligible, D5 generic consumer STOP3/3/reverted.
144/144 expected validation outcomes and unchanged4=1/2/0/0/1 census stand.
Independent human review is parent-owned and begins after E4; it is not
claimed complete. No further source/native work, clock extension or archive
rewrite. The revival proof window was closed by ruling, not a proved missed
UTC deadline. E4 closes this authorized shift cleanly.

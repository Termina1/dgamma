module DGamma.CP5ConfluenceCanonicalSortSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4Support
import DGamma.CP4SupportSolution
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import Data.List.Elem
import Decidable.Equality

%default total

||| An open episode before sorting: its installed interval may contain arbitrary
||| foreign interleavings all the way to the final Active endpoint.
public export
record LocatedInterleavedOpenEpisode
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState) where
  constructor MkLocatedInterleavedOpenEpisode
  openPreStart : SystemState name key value world error
  openStart : SystemState name key value world error
  openPrefix : Transitions initial openPreStart
  openBegin : BeginStep nameEq keyEq selected openPreStart openStart
  openInside : Transitions openStart finalState
  openInstalled : InstalledTrace name key world error value nameEq keyEq selected
    openInside
  openNoEarlierLifecycle : NoLifecycleBy selected openPrefix
  0 openActiveAtFinal : supportedActiveAt @{nameEq} selected finalState = True
  0 openDecomposition : appendTransitions openPrefix
    (MoreTransitions (beginTransition openBegin) openInside) = global

||| Structural consequence after every closing episode is deleted.  Uniqueness
||| is occurrence-indexed by the begin ordinal (`transitionCount openPrefix`),
||| avoiding the old prose-only claim of “exactly one”.
public export
record ClosingFreeTraceShape
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkClosingFreeTraceShape
  supportedOpenEpisode : (selected : name) ->
    isSupported @{nameEq} @{keyEq} selected finalState = True ->
    LocatedInterleavedOpenEpisode name key world error value nameEq keyEq
      selected trace
  0 supportedOpenEpisodeUnique : (selected : name) ->
    (supported : isSupported @{nameEq} @{keyEq} selected finalState = True) ->
    (other : LocatedInterleavedOpenEpisode name key world error value nameEq keyEq
      selected trace) ->
    transitionCount (openPrefix (supportedOpenEpisode selected supported)) =
      transitionCount (openPrefix other)
  unsupportedTakesNoLifecycle : (selected : name) ->
    isSupported @{nameEq} @{keyEq} selected finalState = False ->
    NoLifecycleBy selected trace

||| Finite topological capital for the exact Equation-62 support relation.
public export
record SupportOrderingCapital
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (state : SystemState name key value world error) where
  constructor MkSupportOrderingCapital
  orderedSupportNames : List name
  orderedSupportLinearization : LinearizesSupport name key world error value
    nameEq keyEq state orderedSupportNames

||| Minimal original-endpoint/reduced-endpoint bridge.  It deliberately does
||| not transport arbitrary `SupportPath`s: accepted endpoint withdrawal permits
||| an unsupported retired child to be present originally and absent after
||| reduction, and such a child can still terminate a raw parent path.  Consumers
||| receive only support-set equality and the two complete schedule facts they
||| actually need.
public export
record CanonicalSupportTransport
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (originalFinal, reducedFinal : SystemState name key value world error)
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal reducedFinal) where
  constructor MkCanonicalSupportTransport
  0 supportTruthPreserved : (n : name) ->
    isSupported @{nameEq} @{keyEq} n originalFinal =
      isSupported @{nameEq} @{keyEq} n reducedFinal
  linearizationToOriginal : (order : List name) ->
    LinearizesSupport name key world error value nameEq keyEq reducedFinal order ->
    LinearizesSupport name key world error value nameEq keyEq originalFinal order
  inputPlacementToOriginal : (order : List name) ->
    {initial, canonicalFinal : SystemState name key value world error} ->
    (canonical : Transitions initial canonicalFinal) ->
    CanonicalInputPlacement name key world error value nameEq keyEq reducedFinal
      order canonical ->
    CanonicalInputPlacement name key world error value nameEq keyEq originalFinal
      order canonical

||| Sorting result with every recursive invariant, replay generator/stage
||| correspondence, external-input witness, and registration-accounting field
||| required by one-trace schedule assembly.
public export
record SortedClosingFreeTrace
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    originalFinal) where
  constructor MkSortedClosingFreeTrace
  sortedFinal : SystemState name key value world error
  sortedTrace : Transitions initial sortedFinal
  sortingReplayCorrespondence : RelationalReplayCorrespondence name key world
    error value original sortedTrace
  sortingOccurrenceCorrespondence : ActionRegistrationReplayCorrespondence name
    key world error value original sortedTrace
  sortedPremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sortedTrace
  sortedSameInputs : SameExternalOrchestration nameEq original sortedTrace
  sortedBlock : (n : name) -> Elem n (orderedSupportNames ordering) ->
    LocatedOpenEpisodeBlock name key world error value nameEq keyEq n sortedTrace
  sortedBlocksFollowOrder : (earlier, later : name) ->
    (earlierIn : Elem earlier (orderedSupportNames ordering)) ->
    (laterIn : Elem later (orderedSupportNames ordering)) ->
    BeforeIn earlier later (orderedSupportNames ordering) ->
    BlockBefore name key world error value nameEq keyEq sortedTrace earlier later
      (sortedBlock earlier earlierIn) (sortedBlock later laterIn)
  sortedLifecycleCoverage : LifecycleActorsCovered
    (orderedSupportNames ordering) sortedTrace
  sortedInputPlacement : CanonicalInputPlacement name key world error value
    nameEq keyEq originalFinal (orderedSupportNames ordering) sortedTrace
  sortedEndpoint : CanonicalEndpointRelation name key world error value nameEq
    keyEq originalFinal sortedFinal
  0 sortedWithdrawsNoNames : endpointWithdrawnNames sortedEndpoint = []
  0 sortedWithdrawsNoGenerations :
    endpointWithdrawnGenerations sortedEndpoint = []
  sortedRegistrationTree : CanonicalRegistrationCorrespondence original
    sortedTrace (endpointWithdrawnGenerations sortedEndpoint)

||| Derive the unique closing-free shape from the exact recursive bundle.
public export
0 closingFreeTraceShapeSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  NoClosingEpisodes name key world error value nameEq keyEq trace ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq trace ->
  ClosingFreeTraceShape name key world error value nameEq keyEq trace
closingFreeTraceShapeSpike = ?closingFreeTraceShapeSpike_rhs

||| Construct the finite linearization from re-established Lemma-68 capital.
public export
0 supportOrderingSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq trace ->
  SupportOrderingCapital name key world error value nameEq keyEq finalState
supportOrderingSpike = ?supportOrderingSpike_rhs

||| Bubble actor blocks by repeated `AdjacentSwapResult`s.  The output itself is
||| the sorting-specific recursive transport package, rather than only final
||| schedule-shaped data.
public export
0 sortClosingFreeTraceSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq trace ->
  ClosingFreeTraceShape name key world error value nameEq keyEq trace ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    finalState) ->
  SortedClosingFreeTrace name key world error value protocol nameEq keyEq trace
    ordering
sortClosingFreeTraceSpike = ?sortClosingFreeTraceSpike_rhs

||| Prove all support/parent/input-placement transport from the cumulative
||| endpoint relation and exact generated-registration accounting.
public export
0 canonicalSupportTransportSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal, reducedFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (reduced : Transitions initial reducedFinal) ->
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal reducedFinal) ->
  CanonicalRegistrationCorrespondence original reduced
    (endpointWithdrawnGenerations endpoint) ->
  CanonicalSupportTransport name key world error value nameEq keyEq originalFinal
    reducedFinal endpoint
canonicalSupportTransportSpike = ?canonicalSupportTransportSpike_rhs

||| Research-only authenticity companion for the immutable CP3 registration
||| tree.  It states exact occurrence equality, not merely equal birth ordinals:
||| the tree map must be the origin chosen by the deletion/sorting action replay.
||| Its indices make the proof unusable after replacing either the tree or the
||| occurrence correspondence.
public export
record AuthenticatedCanonicalRegistrationMap
  (name, key, world, error : Type) (value : key -> Type)
  {initial, originalFinal, canonicalFinal :
    SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (canonical : Transitions initial canonicalFinal)
  (withdrawn : List (RegistrationGeneration name))
  (tree : CanonicalRegistrationCorrespondence original canonical withdrawn)
  (occurrences : ActionRegistrationReplayCorrespondence name key world error value
    original canonical) where
  constructor MkAuthenticatedCanonicalRegistrationMap
  0 canonicalOriginIsReplayOrigin :
    {child, parent : name} ->
    {component : Component key value world error} ->
    (occurrence : LocatedGeneratedRegistration child parent component canonical) ->
    canonicalToOriginal tree occurrence =
      replayGeneratedRegistrationOrigin occurrences occurrence

||| The exact occurrence correspondence constructed by deletion followed by
||| sorting.  There is no caller-selected intermediate map at this boundary.
public export
0 deletionSortingOccurrenceCorrespondence :
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  {ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)} ->
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) ->
  ActionRegistrationReplayCorrespondence name key world error value original
    (sortedTrace sorted)
deletionSortingOccurrenceCorrespondence reduction sorted =
  composeActionRegistrationReplayCorrespondence
    (reductionOccurrenceCorrespondence reduction)
    (sortingOccurrenceCorrespondence sorted)

||| Full external/generated orchestration accounting through deletion followed
||| by sorting.  The registration map is authenticated against the exact
||| composed occurrence replay produced by those same indexed fold outputs.
public export
record OneTraceOrchestrationAccounting
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original)
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction))
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) where
  constructor MkOneTraceOrchestrationAccounting
  accountedEndpoint : CanonicalEndpointRelation name key world error value
    nameEq keyEq originalFinal (sortedFinal sorted)
  0 accountedWithdrawnExact : endpointWithdrawnGenerations accountedEndpoint =
    endpointWithdrawnGenerations (cumulativeEndpoint reduction)
  accountedExternalInputs : SameExternalOrchestration nameEq original
    (sortedTrace sorted)
  accountedGeneratedRegistrations : CanonicalRegistrationCorrespondence original
    (sortedTrace sorted) (endpointWithdrawnGenerations accountedEndpoint)
  accountedRegistrationAuthentication : AuthenticatedCanonicalRegistrationMap
    name key world error value original (sortedTrace sorted)
    (endpointWithdrawnGenerations accountedEndpoint)
    accountedGeneratedRegistrations
    (deletionSortingOccurrenceCorrespondence reduction sorted)

public export
0 deletionSortingOrchestrationAccountingSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)) ->
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) ->
  OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
    original reduction ordering sorted
deletionSortingOrchestrationAccountingSpike =
  ?deletionSortingOrchestrationAccountingSpike_rhs

||| Exact enriched one-trace output.  The public schedule, replay
||| correspondence, complete canonical premise bundle, both independence
||| witnesses, and typed deleted-generation history share the schedule's hidden
||| canonical trace by construction.
public export
record IndependentCanonicalSchedule
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal) where
  constructor MkIndependentCanonicalSchedule
  canonicalSchedule : CanonicalSchedule name key world error value protocol
    nameEq keyEq original
  originalTraceIndependent : TraceIndependent name key world error value keyEq
    original
  canonicalReplayCorrespondence : RelationalReplayCorrespondence name key world
    error value original (canonicalTrace canonicalSchedule)
  canonicalOccurrenceCorrespondence : ActionRegistrationReplayCorrespondence name
    key world error value original (canonicalTrace canonicalSchedule)
  canonicalRegistrationAuthentication : AuthenticatedCanonicalRegistrationMap
    name key world error value original (canonicalTrace canonicalSchedule)
    (endpointWithdrawnGenerations (canonicalEndpoint canonicalSchedule))
    (canonicalRegistrationTree canonicalSchedule)
    canonicalOccurrenceCorrespondence
  canonicalReplayPremises : ReplayInvariantBundle name key world error value
    protocol nameEq keyEq (canonicalTrace canonicalSchedule)
  canonicalTraceIndependent : TraceIndependent name key world error value keyEq
    (canonicalTrace canonicalSchedule)
  canonicalWithdrawnClassified :
    (generation : RegistrationGeneration name) ->
    Elem generation
      (endpointWithdrawnGenerations (canonicalEndpoint canonicalSchedule)) ->
    DeletedGenerationClassification name key world error value nameEq original
      generation

||| Positive simultaneous-package constructor.  Unlike the rejected opaque
||| schedule-then-wrapper attempt, this builds `MkCanonicalSchedule` and the
||| composed replay correspondence in one definition, so its hidden final/trace
||| is definitionally the sorting result.  Only the genuinely hard cumulative
||| deleted-generation classifier remains an explicit input.
public export
0 assembleIndependentCanonicalSchedule :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq original) ->
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)) ->
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) ->
  (supportTransport : CanonicalSupportTransport name key world error value
    nameEq keyEq originalFinal (reducedFinal reduction)
      (cumulativeEndpoint reduction)) ->
  (accounting : OneTraceOrchestrationAccounting name key world error value
    protocol nameEq keyEq original reduction ordering sorted) ->
  ((generation : RegistrationGeneration name) ->
    Elem generation (endpointWithdrawnGenerations
      (accountedEndpoint accounting)) ->
    DeletedGenerationClassification name key world error value nameEq original
      generation) ->
  IndependentCanonicalSchedule name key world error value protocol nameEq keyEq
    original
assembleIndependentCanonicalSchedule nameEq keyEq protocol original premises
  reduction ordering sorted supportTransport accounting classified =
    MkIndependentCanonicalSchedule
      (MkCanonicalSchedule
        (sortedFinal sorted)
        (sortedTrace sorted)
        (accountedExternalInputs accounting)
        (replayDiscipline (chainReplayCapital premises))
        (replayDiscipline (sortedPremises sorted))
        (orderedSupportNames ordering)
        (linearizationToOriginal supportTransport (orderedSupportNames ordering)
          (orderedSupportLinearization ordering))
        (sortedBlock sorted)
        (sortedBlocksFollowOrder sorted)
        (sortedLifecycleCoverage sorted)
        (inputPlacementToOriginal supportTransport (orderedSupportNames ordering)
          (sortedTrace sorted) (sortedInputPlacement sorted))
        (accountedEndpoint accounting)
        (accountedGeneratedRegistrations accounting))
      (replayIndependent (chainReplayCapital premises))
      (composeRelationalReplayCorrespondence
        (reductionReplayCorrespondence reduction)
        (sortingReplayCorrespondence sorted))
      (deletionSortingOccurrenceCorrespondence reduction sorted)
      (accountedRegistrationAuthentication accounting)
      (sortedPremises sorted)
      (replayIndependent (sortedPremises sorted))
      classified

||| The hard producer derives the typed cumulative classification from the
||| deletion history and returns the simultaneous package above.  Consumers no
||| longer receive an opaque schedule detached from replay indices.
public export
0 independentCanonicalScheduleSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  CanonicalizationPremises name key world error value protocol nameEq keyEq original ->
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)) ->
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) ->
  CanonicalSupportTransport name key world error value nameEq keyEq originalFinal
    (reducedFinal reduction) (cumulativeEndpoint reduction) ->
  OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
    original reduction ordering sorted ->
  IndependentCanonicalSchedule name key world error value protocol nameEq keyEq
    original
independentCanonicalScheduleSpike = ?independentCanonicalScheduleSpike_rhs

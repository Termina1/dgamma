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

||| Mandatory original-endpoint/reduced-endpoint bridge.  `CanonicalSchedule`
||| indexes support order and input placement at the original endpoint, while
||| sorting naturally constructs them at the closing-free endpoint.  Every
||| executable support/parent fact used by those records is transported here.
public export
record CanonicalSupportTransport
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (originalFinal, reducedFinal : SystemState name key value world error)
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal reducedFinal) where
  constructor MkCanonicalSupportTransport
  0 withdrawnOriginalUnsupported : (n : name) ->
    Elem n (endpointWithdrawnNames endpoint) ->
    isSupported @{nameEq} @{keyEq} n originalFinal = False
  0 supportTruthPreserved : (n : name) ->
    isSupported @{nameEq} @{keyEq} n originalFinal =
      isSupported @{nameEq} @{keyEq} n reducedFinal
  supportPathToReduced : (lower, upper : name) ->
    SupportPath nameEq originalFinal lower upper ->
    SupportPath nameEq reducedFinal lower upper
  supportPathToOriginal : (lower, upper : name) ->
    SupportPath nameEq reducedFinal lower upper ->
    SupportPath nameEq originalFinal lower upper
  parentLookupToReduced : (n : name) ->
    isSupported @{nameEq} @{keyEq} n originalFinal = True ->
    (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} n (registry originalFinal) = Just fiber ->
    (reducedFiber : Fiber name key value world error **
      (lookupFiber @{nameEq} n (registry reducedFinal) = Just reducedFiber,
       fiberParent reducedFiber = fiberParent fiber))
  parentLookupToOriginal : (n : name) ->
    isSupported @{nameEq} @{keyEq} n reducedFinal = True ->
    (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} n (registry reducedFinal) = Just fiber ->
    (originalFiber : Fiber name key value world error **
      (lookupFiber @{nameEq} n (registry originalFinal) = Just originalFiber,
       fiberParent originalFiber = fiberParent fiber))
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

||| Full external/generated orchestration accounting through deletion followed
||| by sorting.  The generated field accounts for every retained birth and
||| every exact deleted generation; the endpoint's withdrawn list is its index.
public export
record OneTraceOrchestrationAccounting
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal, canonicalFinal :
    SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (canonical : Transitions initial canonicalFinal) where
  constructor MkOneTraceOrchestrationAccounting
  accountedEndpoint : CanonicalEndpointRelation name key world error value
    nameEq keyEq originalFinal canonicalFinal
  accountedExternalInputs : SameExternalOrchestration nameEq original canonical
  accountedGeneratedRegistrations : CanonicalRegistrationCorrespondence original
    canonical (endpointWithdrawnGenerations accountedEndpoint)

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
  OneTraceOrchestrationAccounting name key world error value nameEq keyEq original
    (sortedTrace sorted)
deletionSortingOrchestrationAccountingSpike =
  ?deletionSortingOrchestrationAccountingSpike_rhs

||| Exact one-trace constructor spike.  Every input is produced by deletion,
||| support transport, sorting, or the accounting composition immediately
||| above, and the output is the immutable accepted `CanonicalSchedule original`
||| indexed at `originalFinal`.
public export
0 oneTraceCanonicalScheduleSpike :
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
  OneTraceOrchestrationAccounting name key world error value nameEq keyEq original
    (sortedTrace sorted) ->
  CanonicalSchedule name key world error value protocol nameEq keyEq original
oneTraceCanonicalScheduleSpike = ?oneTraceCanonicalScheduleSpike_rhs

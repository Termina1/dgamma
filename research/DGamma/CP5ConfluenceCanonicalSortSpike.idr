module DGamma.CP5ConfluenceCanonicalSortSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4Support
import DGamma.CP4SupportSolution
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

||| Structural consequence needed after all closing episodes are deleted.
||| Every supported endpoint actor has exactly one interleaved open episode;
||| every unsupported actor has no lifecycle occurrence at all.
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
  unsupportedTakesNoLifecycle : (selected : name) ->
    isSupported @{nameEq} @{keyEq} selected finalState = False ->
    NoLifecycleBy selected trace

||| Finite topological capital for the exact Equation-62 support relation.  The
||| likely implementation sorts current registry names by protocol rank and
||| uses CP4Support's strict rank increase along every SupportPath.
public export
record SupportOrderingCapital
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (state : SystemState name key value world error) where
  constructor MkSupportOrderingCapital
  orderedSupportNames : List name
  orderedSupportLinearization : LinearizesSupport name key world error value
    nameEq keyEq state orderedSupportNames

||| Sorting-only result.  No generation is deleted here; registrations and the
||| endpoint are related with empty withdrawal lists.  Composing this value with
||| `ClosingFreeReduction` is a separate deletion-chain composition obligation.
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
  sortedSameInputs : SameExternalOrchestration nameEq original sortedTrace
  sortedDiscipline : RegistrationDiscipline protocol nameEq sortedTrace
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
    sortedTrace []

||| Spike A: derive the unique open-episode shape after Path A has removed every
||| close.  The risk is extracting a located L-Begin/installed suffix from
||| endpoint activity without an existing executable located-episode scanner.
public export
0 closingFreeTraceShapeSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  ((selected : name) ->
    LocatedClosedEpisode name key world error value nameEq keyEq selected trace ->
    Void) ->
  quiet @{nameEq} @{keyEq} finalState = True ->
  noFailedFibers finalState = True ->
  SupportMatchesActive nameEq keyEq finalState ->
  ClosingFreeTraceShape name key world error value nameEq keyEq trace
closingFreeTraceShapeSpike = ?closingFreeTraceShapeSpike_rhs

||| Spike B: construct the finite linearization required by CanonicalSchedule.
||| Lemma 68 gives well-foundedness, but no current module turns the finite
||| registry into the required duplicate-free topological list.
public export
0 supportOrderingSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (state : SystemState name key value world error) ->
  (reached : ReachedFromEmpty name key world error value nameEq keyEq state) ->
  RegistrationProvenance protocol nameEq (reachTrace reached) ->
  RegistryProtocolRanked protocol nameEq state ->
  RegistryParentRanksIncrease protocol nameEq state ->
  SupportOrderingCapital name key world error value nameEq keyEq state
supportOrderingSpike = ?supportOrderingSpike_rhs

||| Spike C: bubble each selected actor's L-Begin/L-Iter/L-Finish steps and its
||| yielded child O-Inserts into one contiguous block, following the support
||| order.  This consumes the local diamonds but must also replay the untouched
||| suffix relationally because accumulator/table functions prevent raw state
||| equality.
public export
0 sortClosingFreeTraceSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  RegistrationDiscipline protocol nameEq trace ->
  registryWellFormed @{nameEq} @{keyEq} initial = True ->
  TraceIndependent name key world error value keyEq trace ->
  ClosingFreeTraceShape name key world error value nameEq keyEq trace ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    finalState) ->
  SortedClosingFreeTrace name key world error value protocol nameEq keyEq trace
    ordering
sortClosingFreeTraceSpike = ?sortClosingFreeTraceSpike_rhs

module DGamma.CP5O19BodyMetadataSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5O20BeginObservationSpike
import DGamma.CP5O19ActivationResolutionSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19SourceShapeSpike
import DGamma.CP5UniqueRawNameInsertions
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Original insertion uniqueness identifies the immutable metadata at any
||| TWO actual cuts of the SAME source. Both birth locations are derived by
||| the existing checked-update induction, not supplied as metadata oracles.
export
0 o19SourceCutMetadata :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, first, second, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) ->
  (firstEarlier : Transitions initial first) -> (firstLater : Transitions first finalState) ->
  (appendTransitions firstEarlier firstLater = source) ->
  (secondEarlier : Transitions initial second) -> (secondLater : Transitions second finalState) ->
  (appendTransitions secondEarlier secondLater = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  (actor : name) -> (firstFiber, secondFiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry first) = Just firstFiber) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry second) = Just secondFiber) ->
  ((fiberParent firstFiber, fiberComponent firstFiber) = (fiberParent secondFiber, fiberComponent secondFiber))
o19SourceCutMetadata {name} {key} {world} {error} {value} nameEq keyEq protocol source
  firstEarlier firstLater firstExact secondEarlier secondLater secondExact premises unique actor firstFiber secondFiber firstFound secondFound =
    uniqueRawBirthMetadata name key world error value nameEq keyEq source unique actor
      (fiberParent firstFiber) (fiberParent secondFiber) (fiberComponent firstFiber) (fiberComponent secondFiber)
      (rawMetadataBirthAtPrefix name key world error value nameEq keyEq source firstEarlier firstLater firstExact
        (fst (alignedAppendSplit firstEarlier firstLater
          (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym firstExact) (replayAligned premises))))
        (replayInitialEmpty premises) actor firstFiber firstFound)
      (rawMetadataBirthAtPrefix name key world error value nameEq keyEq source secondEarlier secondLater secondExact
        (fst (alignedAppendSplit secondEarlier secondLater
          (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym secondExact) (replayAligned premises))))
        (replayInitialEmpty premises) actor secondFiber secondFound)

||| Carry actual pre-left resolved-list exclusion to independently located
||| left/right body cuts. Only source lookups are inputs; both component
||| equalities come from original birth uniqueness and actual source alignment.
export
0 o19NondependencyAcrossCuts :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, base, leftCut, rightCut, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) ->
  (baseEarlier : Transitions initial base) -> (baseLater : Transitions base finalState) ->
  (appendTransitions baseEarlier baseLater = source) ->
  (leftEarlier : Transitions initial leftCut) -> (leftLater : Transitions leftCut finalState) ->
  (appendTransitions leftEarlier leftLater = source) ->
  (rightEarlier : Transitions initial rightCut) -> (rightLater : Transitions rightCut finalState) ->
  (appendTransitions rightEarlier rightLater = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  (leftActor, rightActor : name) ->
  (leftBase, rightBase, leftNow, rightNow : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} leftActor (registry base) = Just leftBase) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} rightActor (registry base) = Just rightBase) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} leftActor (registry leftCut) = Just leftNow) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} rightActor (registry rightCut) = Just rightNow) ->
  (isActive (fiberLifecycle leftBase) = False) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} base = True) ->
  (view : View name (dependencies (componentDependencies (fiberComponent rightBase)))) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies (fiberComponent rightBase))) (registry base) = Just view) ->
  ((wanted : key) -> Elem wanted (dependencies (componentDependencies (fiberComponent rightNow))) ->
    Not (Elem wanted (dependencies (componentProvisions (fiberComponent leftNow)))))
o19NondependencyAcrossCuts {base} nameEq keyEq protocol source
  baseEarlier baseLater baseExact leftEarlier leftLater leftExact rightEarlier rightLater rightExact
  premises unique leftActor rightActor leftBase rightBase leftNow rightNow leftBaseFound rightBaseFound leftFound rightFound
  inactive wellFormed view resolved =
    replace {p = \component => (wanted : key) -> Elem wanted (dependencies (componentDependencies component)) ->
      Not (Elem wanted (dependencies (componentProvisions (fiberComponent leftNow))))}
      (cong snd (o19SourceCutMetadata nameEq keyEq protocol source baseEarlier baseLater baseExact
        rightEarlier rightLater rightExact premises unique rightActor rightBase rightNow rightBaseFound rightFound))
      (replace {p = \component => (wanted : key) -> Elem wanted (dependencies (componentDependencies (fiberComponent rightBase))) ->
        Not (Elem wanted (dependencies (componentProvisions component)))}
        (cong snd (o19SourceCutMetadata nameEq keyEq protocol source baseEarlier baseLater baseExact
          leftEarlier leftLater leftExact premises unique leftActor leftBase leftNow leftBaseFound leftFound))
        (o19ResolvedDependenciesExcluded nameEq keyEq base leftActor leftBase leftBaseFound inactive wellFormed
          (dependencies (componentDependencies (fiberComponent rightBase))) view resolved))

||| Explicit actual Begin observations specialize the cut transport, deriving
||| their inactive fiber and successful resolver rather than requesting them.
export
0 o19ObservedOpeningExclusionAtCuts :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, base, leftOpened, rightOpened, leftCut, rightCut, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) ->
  (baseEarlier : Transitions initial base) -> (baseLater : Transitions base finalState) ->
  (appendTransitions baseEarlier baseLater = source) ->
  (leftEarlier : Transitions initial leftCut) -> (leftLater : Transitions leftCut finalState) ->
  (appendTransitions leftEarlier leftLater = source) ->
  (rightEarlier : Transitions initial rightCut) -> (rightLater : Transitions rightCut finalState) ->
  (appendTransitions rightEarlier rightLater = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  (leftActor, rightActor : name) ->
  (leftSeen : O20BeginObservation name key world error value nameEq keyEq leftActor base leftOpened) ->
  (rightSeen : O20BeginObservation name key world error value nameEq keyEq rightActor base rightOpened) ->
  (leftNow, rightNow : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} leftActor (registry leftCut) = Just leftNow) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} rightActor (registry rightCut) = Just rightNow) ->
  ((wanted : key) -> Elem wanted (dependencies (componentDependencies (fiberComponent rightNow))) ->
    Not (Elem wanted (dependencies (componentProvisions (fiberComponent leftNow)))))
o19ObservedOpeningExclusionAtCuts {name} {key} {value} {world} {error} nameEq keyEq protocol source
  baseEarlier baseLater baseExact leftEarlier leftLater leftExact rightEarlier rightLater rightExact premises unique leftActor rightActor
  leftSeen rightSeen leftNow rightNow leftFound rightFound =
    o19NondependencyAcrossCuts nameEq keyEq protocol source baseEarlier baseLater baseExact
      leftEarlier leftLater leftExact rightEarlier rightLater rightExact premises unique leftActor rightActor
      (MkFiber (beginObservedComponent leftSeen) (beginObservedParent leftSeen) False (beginObservedTable leftSeen) (Inactive Nothing))
      (MkFiber (beginObservedComponent rightSeen) (beginObservedParent rightSeen) False (beginObservedTable rightSeen) (Inactive Nothing))
      leftNow rightNow (beginObservedFound leftSeen) (beginObservedFound rightSeen) leftFound rightFound Refl
      (alignedTraceWellFormedEnd nameEq keyEq baseEarlier
        (fst (alignedAppendSplit baseEarlier baseLater
          (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym baseExact) (replayAligned premises))))
        (replayInitialWellFormed premises))
      (beginObservedView rightSeen) (beginObservedResolved rightSeen)

||| SANCTIONED-INPUT source exclusion at arbitrary actual cuts, including
||| every cut inside either block. Both Begin observations and every static
||| component equation are produced here; no footprint premise remains.
export
0 o19SanctionedCutNondependency :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} ->
  (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, leftCut, rightCut, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  (leftEarlier : Transitions initial leftCut) -> (leftLater : Transitions leftCut finalState) ->
  (appendTransitions leftEarlier leftLater = source) ->
  (rightEarlier : Transitions initial rightCut) -> (rightLater : Transitions rightCut finalState) ->
  (appendTransitions rightEarlier rightLater = source) ->
  (leftNow, rightNow : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actorLeft swap) (registry leftCut) = Just leftNow) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actorRight swap) (registry rightCut) = Just rightNow) ->
  ((wanted : key) -> Elem wanted (dependencies (componentDependencies (fiberComponent rightNow))) ->
    Not (Elem wanted (dependencies (componentProvisions (fiberComponent leftNow)))))
o19SanctionedCutNondependency nameEq keyEq protocol swap source blocks premises safety unique
  leftEarlier leftLater leftExact rightEarlier rightLater rightExact leftNow rightNow leftFound rightFound =
    o19ObservedOpeningExclusionAtCuts nameEq keyEq protocol source
      (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
      (MoreTransitions (beginTransition (blockOpening (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))
        (appendTransitions (blockBody (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
          (traceAfterBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))))
      (blockDecomposition (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
      leftEarlier leftLater leftExact rightEarlier rightLater rightExact premises unique (actorLeft swap) (actorRight swap)
      (o20ObserveActualBegin nameEq keyEq (actorLeft swap)
        (blockPreStart (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
        (blockStart (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
        (blockOpening (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))
      (o20ObserveActualBegin nameEq keyEq (actorRight swap)
        (blockPreStart (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
        (earlyApplicationFinal (safetyRightOpeningEarly safety))
        (MkBeginStep (earlyApplicationChecked (safetyRightOpeningEarly safety))))
      leftNow rightNow leftFound rightFound

||| Consume the EXPLICIT owner-survival package once and discharge E11's
||| static dependency premise at the ACTUAL checked pair. The next producer
||| supplies this package from the source bundle, not from a caller oracle.
export
0 o19SanctionedAdvanceObservedOwner :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} ->
  (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  (earlier : Transitions initial first) -> (later : Transitions last finalState) ->
  (leftAction : Action name key value world error) -> (leftTag, rightTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first = Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance (actorRight swap)) middle = Just (rightTag, last)) ->
  (appendTransitions earlier
    (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq leftAction leftTag leftChecked)
      (MoreTransitions (Fired {before = middle} {afterState = last} nameEq keyEq (LAdvance (actorRight swap)) rightTag rightChecked) later)) = source) ->
  (actionOwner leftAction = actorLeft swap) ->
  Either (rightTag = LIterTag) (rightTag = LFinishTag) ->
  ((fiber : Fiber name key value world error **
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner leftAction) (registry first) = Just fiber)),
   (isJust (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner leftAction) (registry middle)) = True)) ->
  CheckedEarlyApplication name key world error value nameEq keyEq first (LAdvance (actorRight swap)) rightTag
o19SanctionedAdvanceObservedOwner {name} {key} {value} {world} {error} {first} {middle} {last}
  nameEq keyEq protocol swap source blocks premises safety unique earlier later leftAction leftTag rightTag leftChecked rightChecked
  decomposition leftOwner rightPaper ((leftFiber ** leftFound), leftSurvives) =
    o19AdvanceBeforeNondependentPair nameEq keyEq (actorRight swap) first middle last leftAction leftTag rightTag leftChecked rightChecked
      rightPaper (\same => actorDistinct swap (trans (sym leftOwner) same))
      (snd (snd (o19SourcePairFacts nameEq keyEq protocol source earlier
        (Fired nameEq keyEq leftAction leftTag leftChecked) (Fired nameEq keyEq (LAdvance (actorRight swap)) rightTag rightChecked)
        later decomposition premises))) leftFiber leftFound leftSurvives
      (\rightFiber, rightFound => o19SanctionedCutNondependency nameEq keyEq protocol swap source blocks premises safety unique
        earlier (MoreTransitions (Fired nameEq keyEq leftAction leftTag leftChecked)
          (MoreTransitions (Fired nameEq keyEq (LAdvance (actorRight swap)) rightTag rightChecked) later)) decomposition
        (appendTransitions earlier (MoreTransitions (Fired nameEq keyEq leftAction leftTag leftChecked) NoTransitions))
        (MoreTransitions (Fired nameEq keyEq (LAdvance (actorRight swap)) rightTag rightChecked) later)
        (trans (appendTransitionsAssociative earlier (MoreTransitions (Fired nameEq keyEq leftAction leftTag leftChecked) NoTransitions)
          (MoreTransitions (Fired nameEq keyEq (LAdvance (actorRight swap)) rightTag rightChecked) later)) decomposition)
        leftFiber rightFiber
        (trans (cong (\actor => lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry first)) (sym leftOwner)) leftFound)
        rightFound)
      (fst (snd (o19SourcePairFacts nameEq keyEq protocol source earlier
        (Fired nameEq keyEq leftAction leftTag leftChecked) (Fired nameEq keyEq (LAdvance (actorRight swap)) rightTag rightChecked)
        later decomposition premises)))

||| Complete sanctioned-input A/A backwards Iter/Finish guard at an actual
||| pair of the source: F4 produces owner survival, A4 produces the EXACT
||| current static exclusion, and E11 derives callback/domain/control success.
export
0 o19SanctionedAdvanceBeforePair :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} ->
  (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  (earlier : Transitions initial first) -> (later : Transitions last finalState) ->
  (leftAction : Action name key value world error) -> (leftTag, rightTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first = Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance (actorRight swap)) middle = Just (rightTag, last)) ->
  (appendTransitions earlier
    (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq leftAction leftTag leftChecked)
      (MoreTransitions (Fired {before = middle} {afterState = last} nameEq keyEq (LAdvance (actorRight swap)) rightTag rightChecked) later)) = source) ->
  (actionOwner leftAction = actorLeft swap) ->
  Either (rightTag = LIterTag) (rightTag = LFinishTag) ->
  PaperActivationStep (Fired {before = first} {afterState = middle} nameEq keyEq leftAction leftTag leftChecked) ->
  CheckedEarlyApplication name key world error value nameEq keyEq first (LAdvance (actorRight swap)) rightTag
o19SanctionedAdvanceBeforePair nameEq keyEq protocol swap source blocks premises safety unique
  earlier later leftAction leftTag rightTag leftChecked rightChecked decomposition leftOwner rightPaper leftActivation =
    o19SanctionedAdvanceObservedOwner nameEq keyEq protocol swap source blocks premises safety unique
      earlier later leftAction leftTag rightTag leftChecked rightChecked decomposition leftOwner rightPaper
      (o19SourcePairOwner nameEq keyEq protocol source earlier
        (Fired nameEq keyEq leftAction leftTag leftChecked)
        (Fired nameEq keyEq (LAdvance (actorRight swap)) rightTag rightChecked)
        later decomposition premises leftActivation)

||| E12 specialized to the exact sanctioned source cuts, consuming explicit
||| owner and later Begin observations once. The caller below derives both.
export
0 o19SanctionedBeginObservedOwner :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} ->
  (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  (earlier : Transitions initial first) -> (later : Transitions last finalState) ->
  (leftAction : Action name key value world error) -> (leftTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first = Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq} (LBegin (actorRight swap)) middle = Just (LBeginTag, last)) ->
  (appendTransitions earlier
    (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq leftAction leftTag leftChecked)
      (MoreTransitions (Fired {before = middle} {afterState = last} nameEq keyEq (LBegin (actorRight swap)) LBeginTag rightChecked) later)) = source) ->
  (actionOwner leftAction = actorLeft swap) ->
  ((fiber : Fiber name key value world error **
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner leftAction) (registry first) = Just fiber)),
   (isJust (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner leftAction) (registry middle)) = True)) ->
  (opening : O20BeginObservation name key world error value nameEq keyEq (actorRight swap) middle last) ->
  CheckedEarlyApplication name key world error value nameEq keyEq first (LBegin (actorRight swap)) LBeginTag
o19SanctionedBeginObservedOwner {name} {key} {value} {world} {error} {first} {middle} {last}
  nameEq keyEq protocol swap source blocks premises safety unique earlier later leftAction leftTag leftChecked rightChecked
  decomposition leftOwner ((leftFiber ** leftFound), leftSurvives) opening =
    o19BeginBeforeNondependentPair nameEq keyEq (actorRight swap) first middle last leftAction leftTag leftChecked
      leftFiber leftFound leftSurvives (\same => actorDistinct swap (trans (sym leftOwner) (sym same))) opening
      (o19SanctionedCutNondependency nameEq keyEq protocol swap source blocks premises safety unique
        earlier (MoreTransitions (Fired nameEq keyEq leftAction leftTag leftChecked)
          (MoreTransitions (Fired nameEq keyEq (LBegin (actorRight swap)) LBeginTag rightChecked) later)) decomposition
        (appendTransitions earlier (MoreTransitions (Fired nameEq keyEq leftAction leftTag leftChecked) NoTransitions))
        (MoreTransitions (Fired nameEq keyEq (LBegin (actorRight swap)) LBeginTag rightChecked) later)
        (trans (appendTransitionsAssociative earlier (MoreTransitions (Fired nameEq keyEq leftAction leftTag leftChecked) NoTransitions)
          (MoreTransitions (Fired nameEq keyEq (LBegin (actorRight swap)) LBeginTag rightChecked) later)) decomposition)
        leftFiber
        (MkFiber (beginObservedComponent opening) (beginObservedParent opening) False (beginObservedTable opening) (Inactive Nothing))
        (trans (cong (\actor => lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry first)) (sym leftOwner)) leftFound)
        (beginObservedFound opening))
      (fst (snd (o19SourcePairFacts nameEq keyEq protocol source earlier
        (Fired nameEq keyEq leftAction leftTag leftChecked) (Fired nameEq keyEq (LBegin (actorRight swap)) LBeginTag rightChecked)
        later decomposition premises)))

||| Complete sanctioned-input A/A backwards Begin guard. Owner survival,
||| current Begin observation and static nondependency are all produced from
||| the exact checked source pair and original safety; no early-cut oracle.
export
0 o19SanctionedBeginBeforePair :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} ->
  (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  (earlier : Transitions initial first) -> (later : Transitions last finalState) ->
  (leftAction : Action name key value world error) -> (leftTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first = Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq} (LBegin (actorRight swap)) middle = Just (LBeginTag, last)) ->
  (appendTransitions earlier
    (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq leftAction leftTag leftChecked)
      (MoreTransitions (Fired {before = middle} {afterState = last} nameEq keyEq (LBegin (actorRight swap)) LBeginTag rightChecked) later)) = source) ->
  (actionOwner leftAction = actorLeft swap) ->
  PaperActivationStep (Fired {before = first} {afterState = middle} nameEq keyEq leftAction leftTag leftChecked) ->
  CheckedEarlyApplication name key world error value nameEq keyEq first (LBegin (actorRight swap)) LBeginTag
o19SanctionedBeginBeforePair {middle} {last} nameEq keyEq protocol swap source blocks premises safety unique
  earlier later leftAction leftTag leftChecked rightChecked decomposition leftOwner leftActivation =
    o19SanctionedBeginObservedOwner nameEq keyEq protocol swap source blocks premises safety unique
      earlier later leftAction leftTag leftChecked rightChecked decomposition leftOwner
      (o19SourcePairOwner nameEq keyEq protocol source earlier
        (Fired nameEq keyEq leftAction leftTag leftChecked)
        (Fired nameEq keyEq (LBegin (actorRight swap)) LBeginTag rightChecked)
        later decomposition premises leftActivation)
      (o20ObserveActualBegin nameEq keyEq (actorRight swap) middle last (MkBeginStep rightChecked))

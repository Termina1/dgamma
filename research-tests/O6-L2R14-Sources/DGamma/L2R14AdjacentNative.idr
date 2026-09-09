module DGamma.L2R14AdjacentNative

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R6Iteration
import DGamma.L2R10MoveCutObservation
import DGamma.L2R11LocatedCut
import DGamma.L2R12AlignedCut
import DGamma.L2R14CatalogQuery
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Two genuine dictionary-aligned native edges sharing their intermediate
||| state LITERALLY. Both physical occurrences and consecutive ordinals are
||| retained; no equality between unrelated dictionary values is presumed.
public export
record AlignedAdjacentNative
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState)
  (source : SystemState name key value world error)
  (leftAction, rightAction : Action name key value world error) (position : Nat) where
  constructor MkAlignedAdjacentNative
  leftNative : AlignedSourceAction name key world error value nameEq keyEq trace source leftAction position
  rightNative : AlignedSourceAction name key world error value nameEq keyEq trace
    (edgeTarget leftNative) rightAction (S position)

||| Lift both native edges together through one physical head. The left
||| target is constructed simultaneously, so the right source stays exact
||| without projecting a target equality from an opaque locator result.
export
0 adjacentNativeThroughHead : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (source : SystemState name key value world error) ->
  (leftAction, rightAction : Action name key value world error) -> (position : Nat) ->
  AlignedAdjacentNative name key world error value nameEq keyEq rest source leftAction rightAction position ->
  AlignedAdjacentNative name key world error value nameEq keyEq (MoreTransitions step rest)
    source leftAction rightAction (S position)
adjacentNativeThroughHead nameEq keyEq step rest source leftAction rightAction position
  (MkAlignedAdjacentNative left right) = MkAlignedAdjacentNative
    (MkAlignedSourceAction (edgeTarget left) (edgeTag left) (edgeChecked left)
      (MkLocatedActionOccurrence (actionBeforeState (edgeOccurrence left)) (actionAfterState (edgeOccurrence left))
        (MoreTransitions step (beforeActionOccurrence (edgeOccurrence left)))
        (locatedTransition (edgeOccurrence left)) (afterActionOccurrence (edgeOccurrence left))
        (locatedAction (edgeOccurrence left))
        (cong (MoreTransitions step) (actionOccurrenceDecomposition (edgeOccurrence left))))
      (cong S (edgeOrdinal left)) (edgeBefore left) (edgeAfter left))
    (alignedSourceThroughHead nameEq keyEq step rest (edgeTarget left) rightAction (S position) right)

||| Identify the native head source FROM an action-only query. Alignment
||| supplies the authentic requested dictionaries through the existing locator.
export
0 alignedNativeHead : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (aligned : AlignedTransitions name key world error value nameEq keyEq trace) ->
  (action : Action name key value world error) ->
  (0 query : head' (nativeActionWord trail) = Just action) ->
  AlignedSourceAction name key world error value nameEq keyEq trace first action 0
alignedNativeHead nameEq keyEq (AvailabilityEnd state) aligned action query = absurd query
alignedNativeHead nameEq keyEq (AvailabilityStep source (Fired ne ke head tag checked) rest later)
  aligned action query =
  locateAlignedSourceAction nameEq keyEq
    (AvailabilityStep source (Fired ne ke head tag checked) rest later) aligned 0 source action
    (cong (\selected => Just (source, selected)) (injective query))

||| Construct both adjacent native edges at the exact checked head. The
||| following source is PRODUCED as this head's target, not an extra premise.
export
0 adjacentNativeAtHead : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (headAction : Action name key value world error) -> (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} headAction first = Just (tag, middle)) ->
  (rest : Transitions middle finalState) ->
  (later : AvailabilityTrace name key world error value rest) ->
  (tailAligned : AlignedTransitions name key world error value nameEq keyEq rest) ->
  (source : SystemState name key value world error) ->
  (leftAction, rightAction : Action name key value world error) ->
  (0 query : Just (first, headAction) = Just (source, leftAction)) ->
  (0 rightQuery : head' (nativeActionWord later) = Just rightAction) ->
  AlignedAdjacentNative name key world error value nameEq keyEq
    (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq headAction tag checked) rest)
    source leftAction rightAction 0
adjacentNativeAtHead {name} {key} {world} {error} {value} {first} {middle}
  nameEq keyEq headAction tag checked rest later tailAligned source leftAction rightAction query rightQuery =
  replace {p = \pair => AlignedAdjacentNative name key world error value nameEq keyEq
    (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq headAction tag checked) rest)
    (fst pair) (snd pair) rightAction 0} (injective query)
    (MkAlignedAdjacentNative
      (MkAlignedSourceAction middle tag checked
        (MkLocatedActionOccurrence first middle NoTransitions
          (Fired {before = first} {afterState = middle} nameEq keyEq headAction tag checked) rest Refl Refl)
        Refl Refl Refl)
      (alignedSourceThroughHead nameEq keyEq
        (Fired {before = first} {afterState = middle} nameEq keyEq headAction tag checked) rest
        middle rightAction 0 (alignedNativeHead nameEq keyEq later tailAligned rightAction rightQuery)))

||| Select the native head pair or structurally lift the tail pair. Only
||| the queried physical ordinal is eliminated; action guards are unchanged.
export
0 adjacentNativeAtOrdinal : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (headAction : Action name key value world error) -> (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} headAction first = Just (tag, middle)) ->
  (rest : Transitions middle finalState) ->
  (later : AvailabilityTrace name key world error value rest) ->
  (tailAligned : AlignedTransitions name key world error value nameEq keyEq rest) ->
  (0 tailDecoder : (position : Nat) -> (source : SystemState name key value world error) ->
    (leftAction, rightAction : Action name key value world error) ->
    head' (drop position (trailSourceActions later)) = Just (source, leftAction) ->
    head' (drop (S position) (nativeActionWord later)) = Just rightAction ->
    AlignedAdjacentNative name key world error value nameEq keyEq rest source leftAction rightAction position) ->
  (position : Nat) -> (source : SystemState name key value world error) ->
  (leftAction, rightAction : Action name key value world error) ->
  (0 query : head' (drop position ((first, headAction) :: trailSourceActions later)) = Just (source, leftAction)) ->
  (0 rightQuery : head' (drop (S position) (headAction :: nativeActionWord later)) = Just rightAction) ->
  AlignedAdjacentNative name key world error value nameEq keyEq
    (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq headAction tag checked) rest)
    source leftAction rightAction position
adjacentNativeAtOrdinal nameEq keyEq headAction tag checked rest later tailAligned tailDecoder
  Z source leftAction rightAction query rightQuery =
  adjacentNativeAtHead nameEq keyEq headAction tag checked rest later tailAligned source leftAction rightAction query rightQuery
adjacentNativeAtOrdinal {first} {middle} nameEq keyEq headAction tag checked rest later tailAligned tailDecoder
  (S position) source leftAction rightAction query rightQuery =
  adjacentNativeThroughHead nameEq keyEq
    (Fired {before = first} {afterState = middle} nameEq keyEq headAction tag checked) rest
    source leftAction rightAction position (tailDecoder position source leftAction rightAction query rightQuery)

||| Eliminate only native dictionary alignment, then invoke the bounded
||| ordinal decoder. The tail continuation is the trail induction hypothesis.
export
0 adjacentNativeAtStep : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (later : AvailabilityTrace name key world error value rest) ->
  (aligned : AlignedTransitions name key world error value nameEq keyEq (MoreTransitions step rest)) ->
  (0 tailDecoder : AlignedTransitions name key world error value nameEq keyEq rest ->
    (position : Nat) -> (source : SystemState name key value world error) ->
    (leftAction, rightAction : Action name key value world error) ->
    head' (drop position (trailSourceActions later)) = Just (source, leftAction) ->
    head' (drop (S position) (nativeActionWord later)) = Just rightAction ->
    AlignedAdjacentNative name key world error value nameEq keyEq rest source leftAction rightAction position) ->
  (position : Nat) -> (source : SystemState name key value world error) ->
  (leftAction, rightAction : Action name key value world error) ->
  (0 query : head' (drop position (trailSourceActions (AvailabilityStep first step rest later))) = Just (source, leftAction)) ->
  (0 rightQuery : head' (drop (S position) (nativeActionWord (AvailabilityStep first step rest later))) = Just rightAction) ->
  AlignedAdjacentNative name key world error value nameEq keyEq (MoreTransitions step rest)
    source leftAction rightAction position
adjacentNativeAtStep nameEq keyEq _ _ later (AlignedStep headAction tag checked rest tail)
  tailDecoder position source leftAction rightAction query rightQuery =
  adjacentNativeAtOrdinal nameEq keyEq headAction tag checked rest later tail
    (\ordinal, wantedSource, left, right, leftEquation, rightEquation =>
      tailDecoder tail ordinal wantedSource left right leftEquation rightEquation)
    position source leftAction rightAction query rightQuery

||| GENERAL native adjacent-pair decoder. A source/action query on the left
||| and action-only query on the right PRODUCE their common intermediate
||| state, both checked edges and actual consecutive physical occurrences.
export
0 locateAlignedAdjacent : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (aligned : AlignedTransitions name key world error value nameEq keyEq trace) ->
  (position : Nat) -> (source : SystemState name key value world error) ->
  (leftAction, rightAction : Action name key value world error) ->
  (0 query : head' (drop position (trailSourceActions trail)) = Just (source, leftAction)) ->
  (0 rightQuery : head' (drop (S position) (nativeActionWord trail)) = Just rightAction) ->
  AlignedAdjacentNative name key world error value nameEq keyEq trace source leftAction rightAction position
locateAlignedAdjacent nameEq keyEq (AvailabilityEnd state) aligned position source leftAction rightAction query rightQuery =
  absurd (sourceQueryEmpty position (source, leftAction) query)
locateAlignedAdjacent nameEq keyEq (AvailabilityStep first step rest later) aligned
  position source leftAction rightAction query rightQuery =
  adjacentNativeAtStep nameEq keyEq step rest later aligned
    (\tail, ordinal, wantedSource, left, right, leftEquation, rightEquation =>
      locateAlignedAdjacent nameEq keyEq later tail ordinal wantedSource left right leftEquation rightEquation)
    position source leftAction rightAction query rightQuery

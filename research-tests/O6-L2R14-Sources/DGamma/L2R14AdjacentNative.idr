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

module DGamma.L2R12AlignedCut

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R10MoveCutObservation
import DGamma.L2R11LocatedCut
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Exact source/action locator WITH the authentic checked equation at the
||| explicitly named dictionaries. This avoids identifying unrelated DecEq
||| values from an unaligned Transition. Alignment is an explicit premise.
public export
record AlignedSourceAction
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState)
  (source : SystemState name key value world error)
  (action : Action name key value world error) (ordinal : Nat) where
  constructor MkAlignedSourceAction
  edgeTarget : SystemState name key value world error
  edgeTag : RuleTag
  0 edgeChecked : checkedApplyAction @{nameEq} @{keyEq} action source = Just (edgeTag, edgeTarget)
  edgeOccurrence : LocatedActionOccurrence action trace
  0 edgeOrdinal : locatedActionOrdinal edgeOccurrence = ordinal
  0 edgeBefore : actionBeforeState edgeOccurrence = source
  0 edgeAfter : actionAfterState edgeOccurrence = edgeTarget

||| Lift exact source, target, tag and dictionary equation through one head.
||| Only the native ordinal changes; no dictionary equality is guessed.
export
0 alignedSourceThroughHead : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (source : SystemState name key value world error) ->
  (action : Action name key value world error) -> (ordinal : Nat) ->
  (edge : AlignedSourceAction name key world error value nameEq keyEq rest source action ordinal) ->
  AlignedSourceAction name key world error value nameEq keyEq (MoreTransitions step rest) source action (S ordinal)
alignedSourceThroughHead nameEq keyEq step rest source action ordinal edge =
  MkAlignedSourceAction (edgeTarget edge) (edgeTag edge) (edgeChecked edge)
    (MkLocatedActionOccurrence (actionBeforeState (edgeOccurrence edge)) (actionAfterState (edgeOccurrence edge))
      (MoreTransitions step (beforeActionOccurrence (edgeOccurrence edge)))
      (locatedTransition (edgeOccurrence edge)) (afterActionOccurrence (edgeOccurrence edge))
      (locatedAction (edgeOccurrence edge))
      (cong (MoreTransitions step) (actionOccurrenceDecomposition (edgeOccurrence edge))))
    (cong S (edgeOrdinal edge)) (edgeBefore edge) (edgeAfter edge)

||| Observe only the queried ordinal at a dictionary-aligned native head.
||| Source/action pair equality transports the whole packet simultaneously.
export
0 alignedSourceAtOrdinal : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (headAction : Action name key value world error) -> (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} headAction first = Just (tag, middle)) ->
  (rest : Transitions middle finalState) ->
  (later : AvailabilityTrace name key world error value rest) ->
  (0 tailDecoder : (ordinal : Nat) -> (source : SystemState name key value world error) ->
    (action : Action name key value world error) ->
    head' (drop ordinal (trailSourceActions later)) = Just (source, action) ->
    AlignedSourceAction name key world error value nameEq keyEq rest source action ordinal) ->
  (ordinal : Nat) -> (source : SystemState name key value world error) ->
  (action : Action name key value world error) ->
  (0 query : head' (drop ordinal ((first, headAction) :: trailSourceActions later)) = Just (source, action)) ->
  AlignedSourceAction name key world error value nameEq keyEq
    (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq headAction tag checked) rest)
    source action ordinal
alignedSourceAtOrdinal {name} {key} {world} {error} {value} {first} {middle}
  nameEq keyEq headAction tag checked rest later tailDecoder Z source action query =
  replace {p = \pair => AlignedSourceAction name key world error value nameEq keyEq
    (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq headAction tag checked) rest)
    (fst pair) (snd pair) Z} (injective query)
    (MkAlignedSourceAction middle tag checked
      (MkLocatedActionOccurrence first middle NoTransitions
        (Fired {before = first} {afterState = middle} nameEq keyEq headAction tag checked) rest Refl Refl)
      Refl Refl Refl)
alignedSourceAtOrdinal {first} {middle}
  nameEq keyEq headAction tag checked rest later tailDecoder (S ordinal) source action query =
  alignedSourceThroughHead nameEq keyEq
    (Fired {before = first} {afterState = middle} nameEq keyEq headAction tag checked) rest source action ordinal
    (tailDecoder ordinal source action query)

||| Eliminate alignment separately from trail/ordinal observations. Its
||| index authenticates the exact dictionaries of the ACTUAL Fired edge.
export
0 alignedSourceAtStep : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (later : AvailabilityTrace name key world error value rest) ->
  (aligned : AlignedTransitions name key world error value nameEq keyEq (MoreTransitions step rest)) ->
  (0 tailDecoder : AlignedTransitions name key world error value nameEq keyEq rest ->
    (ordinal : Nat) -> (source : SystemState name key value world error) ->
    (action : Action name key value world error) ->
    head' (drop ordinal (trailSourceActions later)) = Just (source, action) ->
    AlignedSourceAction name key world error value nameEq keyEq rest source action ordinal) ->
  (ordinal : Nat) -> (source : SystemState name key value world error) ->
  (action : Action name key value world error) ->
  (0 query : head' (drop ordinal (trailSourceActions (AvailabilityStep first step rest later))) = Just (source, action)) ->
  AlignedSourceAction name key world error value nameEq keyEq (MoreTransitions step rest) source action ordinal
alignedSourceAtStep nameEq keyEq _ _ later
  (AlignedStep headAction tag checked rest tail) tailDecoder ordinal source action query =
  alignedSourceAtOrdinal nameEq keyEq headAction tag checked rest later
    (\position, wantedSource, wantedAction, equation => tailDecoder tail position wantedSource wantedAction equation)
    ordinal source action query

||| GENERAL source-query decoder from an authentic ALIGNED native trail.
||| Produces target, tag, checked equation at the requested dictionaries,
||| physical occurrence and both source/target identities simultaneously.
export
0 locateAlignedSourceAction : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (aligned : AlignedTransitions name key world error value nameEq keyEq trace) ->
  (ordinal : Nat) -> (source : SystemState name key value world error) ->
  (action : Action name key value world error) ->
  (0 query : head' (drop ordinal (trailSourceActions trail)) = Just (source, action)) ->
  AlignedSourceAction name key world error value nameEq keyEq trace source action ordinal
locateAlignedSourceAction nameEq keyEq (AvailabilityEnd state) aligned ordinal source action query =
  absurd (sourceQueryEmpty ordinal (source, action) query)
locateAlignedSourceAction nameEq keyEq (AvailabilityStep first step rest later) aligned ordinal source action query =
  alignedSourceAtStep nameEq keyEq step rest later aligned
    (\tail, position, wantedSource, wantedAction, equation =>
      locateAlignedSourceAction nameEq keyEq later tail position wantedSource wantedAction equation)
    ordinal source action query

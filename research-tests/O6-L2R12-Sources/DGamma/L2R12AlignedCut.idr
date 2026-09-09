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

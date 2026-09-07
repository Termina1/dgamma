module DGamma.CP5RawClosingRankSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4Support
import DGamma.CP4DeletionSelectedOwn
import DGamma.CP5UniqueRawNameInsertions
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Executable action observation; equality of ordinals is not a state cast.
public export
rawClosingActionAt :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {0 initial, finalState : SystemState name key value world error} ->
  Nat -> Transitions initial finalState -> Maybe (Action name key value world error)
rawClosingActionAt name key world error value ordinal NoTransitions = Nothing
rawClosingActionAt name key world error value Z (MoreTransitions (Fired nameEq keyEq action tag checked) rest) = Just action
rawClosingActionAt name key world error value (S ordinal) (MoreTransitions step rest) =
  rawClosingActionAt name key world error value ordinal rest

public export
0 rawClosingActionAtSplit :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {initial, before, afterState, finalState : SystemState name key value world error} ->
  (prior : Transitions initial before) -> (step : Transition before afterState) ->
  (later : Transitions afterState finalState) ->
  rawClosingActionAt name key world error value (transitionCount prior)
    (appendTransitions prior (MoreTransitions step later)) = Just (transitionAction step)
rawClosingActionAtSplit name key world error value NoTransitions
  (Fired nameEq keyEq action tag checked) later = Refl
rawClosingActionAtSplit name key world error value (MoreTransitions head tail) step later =
  rawClosingActionAtSplit name key world error value tail step later

public export
0 rawClosingActionAtLocated :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (action : Action name key value world error) ->
  (occurrence : LocatedActionOccurrence action trace) ->
  rawClosingActionAt name key world error value (locatedActionOrdinal occurrence) trace = Just action
rawClosingActionAtLocated name key world error value trace action occurrence =
  trans (cong (rawClosingActionAt name key world error value (locatedActionOrdinal occurrence))
    (sym (actionOccurrenceDecomposition occurrence)))
    (trans (rawClosingActionAtSplit name key world error value
      (beforeActionOccurrence occurrence) (locatedTransition occurrence) (afterActionOccurrence occurrence))
      (cong Just (locatedAction occurrence)))

||| Fresh raw names identify the immutable COMPONENT, not merely its rank.
public export
0 uniqueRawBirthComponents :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq trace ->
  (selected : name) -> (leftParent, rightParent : Parent name) ->
  (leftComponent, rightComponent : Component key value world error) ->
  (left : LocatedActionOccurrence (OInsert selected leftParent leftComponent) trace) ->
  (right : LocatedActionOccurrence (OInsert selected rightParent rightComponent) trace) ->
  leftComponent = rightComponent
uniqueRawBirthComponents name key world error value nameEq keyEq trace unique
  selected leftParent rightParent leftComponent rightComponent left right =
    case justInjective
      (trans (sym (rawClosingActionAtLocated name key world error value trace
        (OInsert selected leftParent leftComponent) left))
        (trans (cong (\ordinal => rawClosingActionAt name key world error value ordinal trace)
          (uniqueInsertionPosition unique selected leftParent rightParent leftComponent rightComponent left right))
          (rawClosingActionAtLocated name key world error value trace
            (OInsert selected rightParent rightComponent) right))) of
      Refl => Refl

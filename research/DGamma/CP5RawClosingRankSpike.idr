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

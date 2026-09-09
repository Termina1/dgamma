module DGamma.L2R15PhaseOccurrence

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R10PhaseScan
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| The native event at the head of a physically indexed trail. Eliminating
||| the trail also reveals its forced transition index and genuine source.
export
0 phaseEventAtNativeHead : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (step : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (trail : AvailabilityTrace name key world error value (MoreTransitions step rest)) ->
  head' (phaseEvents nameEq trail) =
    Just (phaseActionOwner nameEq first (transitionAction step), isLifecycleAction (transitionAction step))
phaseEventAtNativeHead nameEq _ _
  (AvailabilityStep source (Fired ne ke action tag checked) rest later) = Refl

||| Drop the authentic native head and apply the structural tail proof.
||| Only the indexed trail is eliminated; the requested offset stays data.
export
0 phaseEventThroughNativeHead : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (step : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (trail : AvailabilityTrace name key world error value (MoreTransitions step rest)) ->
  (ordinal : Nat) -> (event : (Maybe name, Bool)) ->
  (0 tailProof : (later : AvailabilityTrace name key world error value rest) ->
    head' (drop ordinal (phaseEvents nameEq later)) = Just event) ->
  head' (drop (S ordinal) (phaseEvents nameEq trail)) = Just event
phaseEventThroughNativeHead nameEq _ _
  (AvailabilityStep source (Fired ne ke action tag checked) rest later) ordinal event tailProof =
  tailProof later

||| Any native physical prefix places the next event at its exact COUNT.
||| The only recursion is on that prefix, never on a reconstructed event word.
export
0 phaseEventAtNativePrefix : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, source, target, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (before : Transitions first source) ->
  (step : Transition source target) -> (rest : Transitions target finalState) ->
  (trail : AvailabilityTrace name key world error value
    (appendTransitions before (MoreTransitions step rest))) ->
  head' (drop (transitionCount before) (phaseEvents nameEq trail)) =
    Just (phaseActionOwner nameEq source (transitionAction step), isLifecycleAction (transitionAction step))
phaseEventAtNativePrefix nameEq NoTransitions step rest trail =
  phaseEventAtNativeHead nameEq step rest trail
phaseEventAtNativePrefix {source} nameEq (MoreTransitions head before) step rest trail =
  phaseEventThroughNativeHead nameEq head (appendTransitions before (MoreTransitions step rest)) trail
    (transitionCount before) (phaseActionOwner nameEq source (transitionAction step), isLifecycleAction (transitionAction step))
    (phaseEventAtNativePrefix nameEq before step rest)

||| Transport the native prefix query through an authentic global trace
||| decomposition. Only its equality is eliminated, preserving the trail.
export
0 phaseEventAtNativeSplit : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, source, target, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (before : Transitions first source) ->
  (step : Transition source target) -> (rest : Transitions target finalState) ->
  (global : Transitions first finalState) ->
  (trail : AvailabilityTrace name key world error value global) ->
  (0 physical : appendTransitions before (MoreTransitions step rest) = global) ->
  head' (drop (transitionCount before) (phaseEvents nameEq trail)) =
    Just (phaseActionOwner nameEq source (transitionAction step), isLifecycleAction (transitionAction step))
phaseEventAtNativeSplit nameEq before step rest _ trail Refl =
  phaseEventAtNativePrefix nameEq before step rest trail

||| GENERAL event-at-occurrence theorem. The source, action and ordinal are
||| those of the supplied physical occurrence; no independent alignment
||| hypothesis or equality between decision dictionaries is used.
export
0 phaseEventAtOccurrence : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (action : Action name key value world error) ->
  (occurrence : LocatedActionOccurrence action trace) ->
  head' (drop (locatedActionOrdinal occurrence) (phaseEvents nameEq trail)) =
    Just (phaseActionOwner nameEq (actionBeforeState occurrence) action, isLifecycleAction action)
phaseEventAtOccurrence {trace} nameEq trail action occurrence =
  trans (phaseEventAtNativeSplit nameEq (beforeActionOccurrence occurrence)
    (locatedTransition occurrence) (afterActionOccurrence occurrence) trace trail
    (actionOccurrenceDecomposition occurrence))
    (cong (\selected => Just (phaseActionOwner nameEq (actionBeforeState occurrence) selected,
      isLifecycleAction selected)) (locatedAction occurrence))

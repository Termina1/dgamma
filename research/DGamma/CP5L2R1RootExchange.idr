module DGamma.CP5L2R1RootExchange

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| An AUTHENTICATED adjacent root-insert exchange, not an applicability oracle
||| or a proof that all distinct actions commute. The R178 crossed interval
||| checks source AND destination declaration availability and no root input.
||| Producers still discharge both alternate native checked equations.
public export
record AvailabilityRootExchange
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (root : name) (component : Component key value world error)
  {first, middle, finalState : SystemState name key value world error}
  (left : Transition first middle) (right : Transition middle finalState) where
  constructor MkAvailabilityRootExchange
  0 rootSwapDistinct : Not (root = transitionActor left)
  0 rootSwapAction : transitionAction right = OInsert root Root component
  0 rootSwapCutCompatible : rootCutCompatible name key world error value
    nameEq keyEq component 0
    (AvailabilityStep first left NoTransitions (AvailabilityEnd middle)) = True
  rootSwapMiddle : SystemState name key value world error
  0 rootSwapEarlyChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert root Root component) first = Just (OInsertTag, rootSwapMiddle)
  0 rootSwapLaterChecked : checkedApplyAction @{nameEq} @{keyEq}
    (transitionAction left) rootSwapMiddle = Just (transitionTag left, finalState)

||| Execute a produced root square between unchanged physical prefix/suffix.
||| The literal source endpoint is preserved; there is no suffix replay oracle.
public export
rootExchangeInContext :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {root : name} -> {component : Component key value world error} ->
  {initial, first, middle, cut, finalState : SystemState name key value world error} ->
  (earlier : Transitions initial first) ->
  (left : Transition first middle) -> (right : Transition middle cut) ->
  (later : Transitions cut finalState) ->
  AvailabilityRootExchange name key world error value nameEq keyEq root component left right ->
  Transitions initial finalState
rootExchangeInContext {nameEq} {keyEq} {root} {component} earlier left right later
  (MkAvailabilityRootExchange distinct rootAction compatible moved earlyChecked laterChecked) =
  appendTransitions earlier
    (MoreTransitions (Fired nameEq keyEq (OInsert root Root component) OInsertTag earlyChecked)
      (MoreTransitions (Fired nameEq keyEq (transitionAction left) (transitionTag left) laterChecked) later))

||| Executable lifecycle-before-root-BIRTH inversion count on an actual-state
||| trace. `prior` is the count of earlier lifecycle edges. Blocked inversions
||| may remain in a normal form: zero is NOT claimed by R178 availability.
public export
rootBirthInversions :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  Nat -> AvailabilityTrace name key world error value trace -> Nat
rootBirthInversions prior (AvailabilityEnd state) = 0
rootBirthInversions prior (AvailabilityStep first (Fired _ _ (OInsert root Root component) _ _) rest later) =
  prior + rootBirthInversions prior later
rootBirthInversions prior (AvailabilityStep first (Fired _ _ action _ _) rest later) =
  rootBirthInversions (if isLifecycleAction action then S prior else prior) later

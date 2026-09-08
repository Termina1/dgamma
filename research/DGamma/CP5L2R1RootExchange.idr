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

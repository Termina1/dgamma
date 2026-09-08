module DGamma.CP5L2R1RetireExchange

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Decidable.Equality

%default total
%unbound_implicits off

||| An exact adjacent child-Retire square over TWO existing native edges.
||| The alternate equations are proof obligations, not assumed commutation
||| for every foreign action. Concrete producers must discharge both of them.
||| This stronger exact-state specialization is used by the R191 fixture.
public export
record ExactChildRetireExchange
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (child, parent : name)
  {first, middle, finalState : SystemState name key value world error}
  (left : Transition first middle) (right : Transition middle finalState) where
  constructor MkExactChildRetireExchange
  exchangeChildFiber : Fiber name key value world error
  0 exchangeChildFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry first) = Just exchangeChildFiber
  0 exchangeParent : fiberParent exchangeChildFiber = ChildOf parent
  0 exchangeForeign : Not (child = transitionActor left)
  0 exchangeRetire : transitionAction right = ORetire child
  exchangeMiddle : SystemState name key value world error
  0 exchangeEarlyChecked : checkedApplyAction @{nameEq} @{keyEq} (ORetire child) first = Just (ORetireTag, exchangeMiddle)
  0 exchangeLaterChecked : checkedApplyAction @{nameEq} @{keyEq} (transitionAction left) exchangeMiddle = Just (transitionTag left, finalState)

||| Splice an authenticated adjacent square between unchanged physical
||| context traces. The final SystemState is literally the source endpoint.
||| This consumes a produced square; it does not assert all pairs commute.
public export
retireExchangeInContext :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {child, parent : name} ->
  {initial, first, middle, cut, finalState : SystemState name key value world error} ->
  (earlier : Transitions initial first) ->
  (left : Transition first middle) -> (right : Transition middle cut) ->
  (later : Transitions cut finalState) ->
  ExactChildRetireExchange name key world error value nameEq keyEq child parent left right ->
  Transitions initial finalState
retireExchangeInContext {nameEq} {keyEq} {child} earlier left right later
  (MkExactChildRetireExchange fiber found parentExact distinct retireExact moved earlyChecked laterChecked) =
  appendTransitions earlier
    (MoreTransitions (Fired nameEq keyEq (ORetire child) ORetireTag earlyChecked)
      (MoreTransitions (Fired nameEq keyEq (transitionAction left) (transitionTag left) laterChecked) later))

module DGamma.CP5L2R1RetireExchange

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ActorLifecycleOnlyExtended
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

||| Concatenate two actual extended actor bodies, preserving the source
||| lookup and child-parent evidence carried by each retirement/removal edge.
export
0 appendActorLifecycleOnlyExtended :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {selected : name} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (left : Transitions first middle) -> (right : Transitions middle finalState) ->
  ActorLifecycleOnlyExtended nameEq selected left ->
  ActorLifecycleOnlyExtended nameEq selected right ->
  ActorLifecycleOnlyExtended nameEq selected (appendTransitions left right)
appendActorLifecycleOnlyExtended _ right ExtendedLifecycleEnd rightOnly = rightOnly
appendActorLifecycleOnlyExtended _ right (ExtendedLifecycleStep step rest life owned only) rightOnly =
  ExtendedLifecycleStep step (appendTransitions rest right) life owned
    (appendActorLifecycleOnlyExtended rest right only rightOnly)
appendActorLifecycleOnlyExtended _ right (ExtendedYieldedRegistrationStep step rest yielded only) rightOnly =
  ExtendedYieldedRegistrationStep step (appendTransitions rest right) yielded
    (appendActorLifecycleOnlyExtended rest right only rightOnly)
appendActorLifecycleOnlyExtended _ right (ExtendedChildRetireStep step rest child fiber found parentExact action only) rightOnly =
  ExtendedChildRetireStep step (appendTransitions rest right) child fiber found parentExact action
    (appendActorLifecycleOnlyExtended rest right only rightOnly)
appendActorLifecycleOnlyExtended _ right (ExtendedChildRemoveStep step rest child fiber found parentExact action only) rightOnly =
  ExtendedChildRemoveStep step (appendTransitions rest right) child fiber found parentExact action
    (appendActorLifecycleOnlyExtended rest right only rightOnly)

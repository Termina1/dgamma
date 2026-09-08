module DGamma.CP5ActorLifecycleOnlyExtended

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import Decidable.Equality

%default total
%unbound_implicits off

||| A10 RESEARCH COPY ONLY. Child Retire/Remove carry the ACTUAL source lookup
||| and ChildOf owner metadata, not merely an arbitrary orchestration action.
||| The surrounding registration discipline still owns generated provenance.
||| No coercion back to frozen ActorLifecycleOnly exists or is asserted.
public export
data ActorLifecycleOnlyExtended :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  ExtendedLifecycleEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} -> {state : SystemState name key value world error} ->
    ActorLifecycleOnlyExtended nameEq selected (NoTransitions {state})
  ExtendedLifecycleStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, middle, finalState : SystemState name key value world error} ->
    (step : Transition first middle) -> (rest : Transitions middle finalState) ->
    (0 lifecycle : isLifecycleAction (transitionAction step) = True) ->
    (0 owned : transitionActor step = selected) ->
    (0 only : ActorLifecycleOnlyExtended nameEq selected rest) ->
    ActorLifecycleOnlyExtended nameEq selected (MoreTransitions step rest)
  ExtendedYieldedRegistrationStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected, child : name} ->
    {component : Component key value world error} ->
    {first, middle, finalState : SystemState name key value world error} ->
    (step : Transition first middle) -> (rest : Transitions middle finalState) ->
    (0 yielded : transitionAction step = OInsert child (ChildOf selected) component) ->
    (0 only : ActorLifecycleOnlyExtended nameEq selected rest) ->
    ActorLifecycleOnlyExtended nameEq selected (MoreTransitions step rest)
  ExtendedChildRetireStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, middle, finalState : SystemState name key value world error} ->
    (step : Transition first middle) -> (rest : Transitions middle finalState) ->
    (child : name) -> (fiber : Fiber name key value world error) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry first) = Just fiber) ->
    (0 parent : fiberParent fiber = ChildOf selected) ->
    (0 action : transitionAction step = ORetire child) ->
    (0 only : ActorLifecycleOnlyExtended nameEq selected rest) ->
    ActorLifecycleOnlyExtended nameEq selected (MoreTransitions step rest)
  ExtendedChildRemoveStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, middle, finalState : SystemState name key value world error} ->
    (step : Transition first middle) -> (rest : Transitions middle finalState) ->
    (child : name) -> (fiber : Fiber name key value world error) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry first) = Just fiber) ->
    (0 parent : fiberParent fiber = ChildOf selected) ->
    (0 action : transitionAction step = ORemove child) ->
    (0 only : ActorLifecycleOnlyExtended nameEq selected rest) ->
    ActorLifecycleOnlyExtended nameEq selected (MoreTransitions step rest)

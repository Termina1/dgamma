module DGamma.CP5RootOrchestrationTransportSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5RetirementHistorySpike
import Decidable.Equality

%default total
%unbound_implicits off

||| Structural root occurrence: each root proof is indexed by the actual head
||| transition. No equal-ordinal/dependent-state cast is needed by the matcher.
public export
data RootActionOccurs :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (action : Action name key value world error) ->
  {first, finalState : SystemState name key value world error} -> Transitions first finalState -> Type where
  RootActionHere :
    {name, key, world, error : Type} -> {value : key -> Type} -> {nameEq : DecEq name} ->
    {action : Action name key value world error} ->
    {first, middle, finalState : SystemState name key value world error} ->
    (0 step : Transition first middle) -> (0 rest : Transitions middle finalState) ->
    (0 root : RootOrchestrationStep nameEq step) -> (0 exact : transitionAction step = action) ->
    RootActionOccurs name key world error value nameEq action (MoreTransitions step rest)
  RootActionLater :
    {name, key, world, error : Type} -> {value : key -> Type} -> {nameEq : DecEq name} ->
    {action : Action name key value world error} ->
    {first, middle, finalState : SystemState name key value world error} ->
    (0 step : Transition first middle) -> (0 rest : Transitions middle finalState) ->
    (0 later : RootActionOccurs name key world error value nameEq action rest) ->
    RootActionOccurs name key world error value nameEq action (MoreTransitions step rest)

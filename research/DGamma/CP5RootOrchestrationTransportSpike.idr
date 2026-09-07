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

export
0 rootActionOccursPrefix :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (prior : Transitions first middle) -> (later : Transitions middle finalState) ->
  (action : Action name key value world error) -> RootActionOccurs name key world error value nameEq action later ->
  RootActionOccurs name key world error value nameEq action (appendTransitions prior later)
rootActionOccursPrefix name key world error value nameEq NoTransitions later action occurrence = occurrence
rootActionOccursPrefix name key world error value nameEq (MoreTransitions step rest) later action occurrence =
  RootActionLater step (appendTransitions rest later) (rootActionOccursPrefix name key world error value nameEq rest later action occurrence)

export
0 rootActionFromLocated :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  {first, finalState : SystemState name key value world error} -> (trace : Transitions first finalState) ->
  (action : Action name key value world error) -> (occurrence : LocatedActionOccurrence action trace) ->
  RootOrchestrationStep nameEq (locatedTransition occurrence) -> RootActionOccurs name key world error value nameEq action trace
rootActionFromLocated name key world error value nameEq trace action occurrence root =
  replace {p = RootActionOccurs name key world error value nameEq action} (actionOccurrenceDecomposition occurrence)
    (rootActionOccursPrefix name key world error value nameEq (beforeActionOccurrence occurrence)
      (MoreTransitions (locatedTransition occurrence) (afterActionOccurrence occurrence)) action
      (RootActionHere (locatedTransition occurrence) (afterActionOccurrence occurrence) root (locatedAction occurrence)))

module DGamma.CP5RootOrchestrationTransportSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5RetirementHistorySpike
import DGamma.CP5CurrentGenerationBirthSpike
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

0 rootActionHeadView :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (action : Action name key value world error) -> (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  RootActionOccurs name key world error value nameEq action (MoreTransitions step rest) ->
  Either (RootOrchestrationStep nameEq step, transitionAction step = action) (RootActionOccurs name key world error value nameEq action rest)
rootActionHeadView name key world error value nameEq action step rest (RootActionHere _ _ root exact) = Left (root, exact)
rootActionHeadView name key world error value nameEq action step rest (RootActionLater _ _ later) = Right later

export
0 rootActionForward :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  SameExternalOrchestration nameEq left right -> (action : Action name key value world error) ->
  RootActionOccurs name key world error value nameEq action left -> RootActionOccurs name key world error value nameEq action right
rootActionForward name key world error value nameEq _ _ SameExternalOrchestrationEnd action occurrence = case occurrence of {}
rootActionForward name key world error value nameEq _ right (SkipLeftInternal step rest notRoot later) action occurrence =
  case rootActionHeadView name key world error value nameEq action step rest occurrence of
    Left (root, exact) => void (notRoot root)
    Right remaining => rootActionForward name key world error value nameEq rest right later action remaining
rootActionForward name key world error value nameEq left _ (SkipRightInternal step rest notRoot later) action occurrence =
  RootActionLater step rest (rootActionForward name key world error value nameEq left rest later action occurrence)
rootActionForward name key world error value nameEq _ _ (MatchExternalInput matched leftStep leftRest leftRoot rightStep rightRest rightRoot leftExact rightExact later) action occurrence =
  case rootActionHeadView name key world error value nameEq action leftStep leftRest occurrence of
    Left (root, exact) => RootActionHere rightStep rightRest rightRoot (trans rightExact (trans (sym leftExact) exact))
    Right remaining => RootActionLater rightStep rightRest (rootActionForward name key world error value nameEq leftRest rightRest later action remaining)

export
0 rootActionBackward :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  SameExternalOrchestration nameEq left right -> (action : Action name key value world error) ->
  RootActionOccurs name key world error value nameEq action right -> RootActionOccurs name key world error value nameEq action left
rootActionBackward name key world error value nameEq _ _ SameExternalOrchestrationEnd action occurrence = case occurrence of {}
rootActionBackward name key world error value nameEq left _ (SkipRightInternal step rest notRoot later) action occurrence =
  case rootActionHeadView name key world error value nameEq action step rest occurrence of
    Left (root, exact) => void (notRoot root)
    Right remaining => rootActionBackward name key world error value nameEq left rest later action remaining
rootActionBackward name key world error value nameEq _ right (SkipLeftInternal step rest notRoot later) action occurrence =
  RootActionLater step rest (rootActionBackward name key world error value nameEq rest right later action occurrence)
rootActionBackward name key world error value nameEq _ _ (MatchExternalInput matched leftStep leftRest leftRoot rightStep rightRest rightRoot leftExact rightExact later) action occurrence =
  case rootActionHeadView name key world error value nameEq action rightStep rightRest occurrence of
    Left (root, exact) => RootActionHere leftStep leftRest leftRoot (trans leftExact (trans (sym rightExact) exact))
    Right remaining => RootActionLater leftStep leftRest (rootActionBackward name key world error value nameEq leftRest rightRest later action remaining)

export
0 rootActionLocated :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> (action : Action name key value world error) ->
  RootActionOccurs name key world error value nameEq action trace -> LocatedActionOccurrence action trace
rootActionLocated name key world error value nameEq _ action (RootActionHere step rest root exact) =
  MkLocatedActionOccurrence _ _ NoTransitions step rest exact Refl
rootActionLocated name key world error value nameEq _ action (RootActionLater step rest later) =
  currentBirthPrependLocation name key world error value step rest action (rootActionLocated name key world error value nameEq rest action later)

||| A retirement of an actual root endpoint was a ROOT input at its original
||| source step: immutable metadata is recovered from authentic unique births.
export
0 rootEndpointRetirementPacket :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> AlignedTransitions name key world error value nameEq keyEq trace ->
  (bindings (registry first) = []) -> UniqueRawNameInsertions name key world error value nameEq keyEq trace ->
  (selected : name) -> (finalFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} selected (registry finalState) = Just finalFiber) ->
  (fiberParent finalFiber = Root) -> LocatedActionOccurrence (ORetire selected) trace ->
  RootActionOccurs name key world error value nameEq (ORetire selected) trace
rootEndpointRetirementPacket name key world error value nameEq keyEq trace aligned empty unique selected finalFiber finalFound parentExact occurrence =
  case retirementLocatedSource name key world error value nameEq keyEq trace aligned selected occurrence of
    (sourceFiber ** sourceFound) =>
      rootActionFromLocated name key world error value nameEq trace (ORetire selected) occurrence
        (RootRetireStep sourceFiber sourceFound
          (trans (cong fst (actualPrefixEndpointMetadata name key world error value nameEq keyEq trace (beforeActionOccurrence occurrence)
            (MoreTransitions (locatedTransition occurrence) (afterActionOccurrence occurrence)) (actionOccurrenceDecomposition occurrence)
            aligned empty unique selected sourceFiber finalFiber sourceFound finalFound)) parentExact) (locatedAction occurrence))

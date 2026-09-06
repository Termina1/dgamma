module DGamma.R172O17RootLifetimeCapital

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import DGamma.CP3
import DGamma.CP4DeletionRetainedAction
import DGamma.CP4DeletionBoundaryLifecycleCore
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R172O17OpenParentRootReuseCandidate
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Lifetime prefix for the explicitly stated R172ReuseGlobalSortingRefutation.
||| This module does not claim an inhabitant until the final contradiction is assembled.

||| An external occurrence retains its actual pre-state root classification.
public export
data R172RootActionOccurs :
  {first, finalState : SystemState Nat R45Key R45Value Unit String} ->
  Action Nat R45Key R45Value Unit String -> Transitions first finalState -> Type where
  R172RootActionHere :
    {first, middle, finalState : SystemState Nat R45Key R45Value Unit String} ->
    {action : Action Nat R45Key R45Value Unit String} -> (transition : Transition first middle) -> (rest : Transitions middle finalState) ->
    RootOrchestrationStep r45NameEq transition -> transitionAction transition = action ->
    R172RootActionOccurs action (MoreTransitions transition rest)
  R172RootActionLater :
    {first, middle, finalState : SystemState Nat R45Key R45Value Unit String} ->
    {action : Action Nat R45Key R45Value Unit String} -> (transition : Transition first middle) -> (rest : Transitions middle finalState) ->
    R172RootActionOccurs action rest -> R172RootActionOccurs action (MoreTransitions transition rest)

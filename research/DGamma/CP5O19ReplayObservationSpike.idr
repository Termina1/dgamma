module DGamma.CP5O19ReplayObservationSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceRankObservationSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| B21: specialize the EXISTING producer-owned action fold. This observes
||| actual trace data; no execution outcome or replay target is guessed.
public export
0 o19ActionWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, finalState : SystemState name key value world error} ->
  Transitions initial finalState -> List (Action name key value world error)
o19ActionWord {name} {key} {world} {error} {value} trace =
  traceActionFold name key world error value (List (Action name key value world error)) (::) [] trace

||| B22: observed TWO actual checked transitions, not independently supplied
||| moved nodes. Both actions and their complete trace/alignment are owned.
public export
record ObservedTwoActionTrace
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (wantedFirst, wantedSecond : Action name key value world error)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkObservedTwoActionTrace
  twoActionMiddle : SystemState name key value world error
  twoActionFirst : Transition initial twoActionMiddle
  twoActionSecond : Transition twoActionMiddle finalState
  0 twoActionFirstExact : (transitionAction twoActionFirst = wantedFirst)
  0 twoActionSecondExact : (transitionAction twoActionSecond = wantedSecond)
  0 twoActionTraceExact : (MoreTransitions twoActionFirst (MoreTransitions twoActionSecond NoTransitions) = trace)
  0 twoActionAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions twoActionFirst (MoreTransitions twoActionSecond NoTransitions))

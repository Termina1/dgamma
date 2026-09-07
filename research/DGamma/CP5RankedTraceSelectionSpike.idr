module DGamma.CP5RankedTraceSelectionSpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceWorkMeasureSpike
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Surface-independent actual-pair output. The SAME observation supplies both
||| ranks; Nothing denotes a barrier. No smaller target word or diamond is input.
public export
record LocatedRankDescent
  (name, key, world, error : Type) (value : key -> Type)
  (observe : Action name key value world error -> Maybe Nat)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkLocatedRankDescent
  traceDescentBefore : SystemState name key value world error
  traceDescentMiddle : SystemState name key value world error
  traceDescentAfter : SystemState name key value world error
  traceDescentPrefix : Transitions initial traceDescentBefore
  traceDescentLeft : Transition traceDescentBefore traceDescentMiddle
  traceDescentRight : Transition traceDescentMiddle traceDescentAfter
  traceDescentSuffix : Transitions traceDescentAfter finalState
  traceDescentLeftRank : Nat
  traceDescentRightRank : Nat
  0 traceDescentLeftExact : observe (transitionAction traceDescentLeft) = Just traceDescentLeftRank
  0 traceDescentRightExact : observe (transitionAction traceDescentRight) = Just traceDescentRightRank
  0 traceDescentDescending : rankCrossing traceDescentLeftRank traceDescentRightRank = 1
  0 traceDescentDecomposition : appendTransitions traceDescentPrefix
    (MoreTransitions traceDescentLeft (MoreTransitions traceDescentRight traceDescentSuffix)) = trace

||| Construct the exact head choice from the actual checked pair observations.
public export
0 locatedRankDescentHead :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (observe : Action name key value world error -> Maybe Nat) ->
  {before, middle, afterState, finalState : SystemState name key value world error} ->
  (left : Transition before middle) -> (right : Transition middle afterState) ->
  (suffix : Transitions afterState finalState) ->
  (leftRank, rightRank : Nat) ->
  (observe (transitionAction left) = Just leftRank) ->
  (observe (transitionAction right) = Just rightRank) ->
  (rankCrossing leftRank rightRank = 1) ->
  LocatedRankDescent name key world error value observe (MoreTransitions left (MoreTransitions right suffix))
locatedRankDescentHead name key world error value observe {before} {middle} {afterState}
  left right suffix leftRank rightRank leftExact rightExact crossed =
    MkLocatedRankDescent before middle afterState NoTransitions left right suffix
      leftRank rightRank leftExact rightExact crossed Refl

||| Preserve every earlier checked node, including every unowned barrier.
public export
0 locatedRankDescentPrepend :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (observe : Action name key value world error -> Maybe Nat) ->
  {initial, middle, finalState : SystemState name key value world error} ->
  (head : Transition initial middle) -> (rest : Transitions middle finalState) ->
  LocatedRankDescent name key world error value observe rest ->
  LocatedRankDescent name key world error value observe (MoreTransitions head rest)
locatedRankDescentPrepend name key world error value observe head rest
  (MkLocatedRankDescent before middle afterState prior left right suffix leftRank rightRank leftExact rightExact crossed decomposition) =
    MkLocatedRankDescent before middle afterState (MoreTransitions head prior) left right suffix
      leftRank rightRank leftExact rightExact crossed (cong (MoreTransitions head) decomposition)

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

||| Inspect EXPLICIT rank observations once, avoiding dependent elimination of
||| a computed packet. Either unowned head is a barrier, never a swap candidate.
public export
0 observedRankHeadDescent :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (observe : Action name key value world error -> Maybe Nat) ->
  {before, middle, afterState, finalState : SystemState name key value world error} ->
  (left : Transition before middle) -> (right : Transition middle afterState) ->
  (suffix : Transitions afterState finalState) ->
  (seenLeft, seenRight : Maybe Nat) ->
  (observe (transitionAction left) = seenLeft) ->
  (observe (transitionAction right) = seenRight) ->
  Maybe (LocatedRankDescent name key world error value observe (MoreTransitions left (MoreTransitions right suffix)))
observedRankHeadDescent name key world error value observe left right suffix Nothing seenRight leftExact rightExact = Nothing
observedRankHeadDescent name key world error value observe left right suffix (Just leftRank) Nothing leftExact rightExact = Nothing
observedRankHeadDescent name key world error value observe left right suffix (Just leftRank) (Just rightRank) leftExact rightExact =
  case decEq (rankCrossing leftRank rightRank) 1 of
    Yes crossed => Just (locatedRankDescentHead name key world error value observe left right suffix leftRank rightRank leftExact rightExact crossed)
    No notDescending => Nothing

||| Select an ACTUAL checked adjacent descent, retaining its original prefix.
||| Structural recursion scans all actions and never joins across a barrier.
||| Nothing is no candidate found, NOT a canonical-form or applicability proof.
public export
0 findActualRankDescent :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (observe : Action name key value world error -> Maybe Nat) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  Maybe (LocatedRankDescent name key world error value observe trace)
findActualRankDescent name key world error value observe NoTransitions = Nothing
findActualRankDescent name key world error value observe (MoreTransitions left NoTransitions) = Nothing
findActualRankDescent name key world error value observe (MoreTransitions left (MoreTransitions right suffix)) =
  case observedRankHeadDescent name key world error value observe left right suffix
    (observe (transitionAction left)) (observe (transitionAction right)) Refl Refl of
    Just choice => Just choice
    Nothing => map (locatedRankDescentPrepend name key world error value observe left (MoreTransitions right suffix))
      (findActualRankDescent name key world error value observe (MoreTransitions right suffix))

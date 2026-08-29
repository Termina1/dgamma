module DGamma.R45OpaqueGenuineAdjacentInputNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R45GenuineDiamondSafetyDesignPositive
import Decidable.Equality

%default total

||| Negative half of cure (b): the byte-frozen adjacent declaration requires a
||| LocalRelationalDiamond. Passing the opaque genuine wrapper directly is a
||| type error; projecting its bare base typechecks but irretrievably hides the
||| sealed safety from the adjacent body, as the paired positive probe shows.
0 frozenAdjacentInputRejectsOpaqueGenuine :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
    SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (tracePrefix : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) ->
  (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) ->
  (decomposition : appendTransitions tracePrefix
    (MoreTransitions left (MoreTransitions right suffix)) = original) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq
    keyEq original) ->
  (sealed : CandidateOpaqueGenuineDiamond name key world error value nameEq keyEq
    left right) ->
  (0 pairExternalOrder : SameExternalOrchestration nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions (movedRight (revealOpaqueGenuineBase sealed))
      (MoreTransitions (movedLeft (revealOpaqueGenuineBase sealed))
        NoTransitions))) ->
  AdjacentSwapResult name key world error value protocol nameEq keyEq original
    tracePrefix left right suffix (revealOpaqueGenuineBase sealed)
frozenAdjacentInputRejectsOpaqueGenuine nameEq keyEq protocol original tracePrefix
  left right suffix decomposition premises sealed pairExternalOrder =
    adjacentSwapSuffixSpike nameEq keyEq protocol original tracePrefix left right
      suffix decomposition premises sealed pairExternalOrder

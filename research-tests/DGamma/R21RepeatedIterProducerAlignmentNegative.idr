module DGamma.R21RepeatedIterProducerAlignmentNegative

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

||| Historical capital pin for the retired zero-consumer
||| `repeatedIterIdentityDiamond` fixture producer. Its former premises
||| constrained only action/tag projections and the final state; they did not
||| align either reused transition's stored dictionaries with the outer
||| `nameEq`/`keyEq`.
0 repeatedIterPremisesCannotSupplyMovedAlignment :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle finalState) ->
  (leftAdvance : transitionAction left = LAdvance actor) ->
  (leftIter : transitionTag left = LIterTag) ->
  (rightAdvance : transitionAction right = LAdvance actor) ->
  (rightIter : transitionTag right = LIterTag) ->
  registryWellFormed @{nameEq} @{keyEq} finalState = True ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
repeatedIterPremisesCannotSupplyMovedAlignment nameEq keyEq actor left right
  leftAdvance leftIter rightAdvance rightIter finalWellFormed =
    case left of
      Fired storedLeftNameEq storedLeftKeyEq leftAction leftTag leftChecked =>
        case right of
          Fired storedRightNameEq storedRightKeyEq rightAction rightTag
            rightChecked =>
              AlignedStep leftAction leftTag leftChecked
                (MoreTransitions right NoTransitions)
                (AlignedStep rightAction rightTag rightChecked NoTransitions
                  AlignedEnd)

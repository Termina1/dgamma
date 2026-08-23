module DGamma.R9CoordinateBoundaryPositive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import Data.Nat
import Decidable.Equality

%default total

0 equalSelectedStartsImpossible :
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises) ->
  transitionCount (traceBeforeBlock (decomposedBlock sourceBlocks
    (actorLeft orderSwap) (safetyLeftInOrder safety))) + 0 =
  transitionCount (traceBeforeBlock (decomposedBlock sourceBlocks
    (actorRight orderSwap) (safetyRightInOrder safety))) + 0 ->
  Void
equalSelectedStartsImpossible safety exact =
  selectedLeftRightRangesDisjoint (selectedBlockCoordinateInjectivity safety)
    0 0 (LTESucc LTEZero) (LTESucc LTEZero) exact

0 onePastEndImpossible : LTE (S (S n)) (S n) -> Void
onePastEndImpossible {n = Z} (LTESucc prf) impossible
onePastEndImpossible {n = S k} (LTESucc prf) = onePastEndImpossible prf

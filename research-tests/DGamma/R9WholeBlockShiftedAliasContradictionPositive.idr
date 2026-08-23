module DGamma.R9WholeBlockShiftedAliasContradictionPositive

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import Data.Nat
import Decidable.Equality

%default total

||| Whole-wrapper form of the reviewer's start=1,pos=1 versus start=2,pos=0
||| attack. Authoritative bounds and producer range-disjointness turn the
||| compensating equality into Void.
public export
0 shiftedStartAliasContradictsWhole :
  (whole : WholeBlockSwapDerivation name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises safety targetTrace) ->
  LTE 2 (actorBlockTransitionCount (decomposedBlock sourceBlocks
    (actorLeft orderSwap) (safetyLeftInOrder safety))) ->
  LTE 1 (actorBlockTransitionCount (decomposedBlock sourceBlocks
    (actorRight orderSwap) (safetyRightInOrder safety))) ->
  transitionCount (traceBeforeBlock (decomposedBlock sourceBlocks
    (actorLeft orderSwap) (safetyLeftInOrder safety))) = 1 ->
  transitionCount (traceBeforeBlock (decomposedBlock sourceBlocks
    (actorRight orderSwap) (safetyRightInOrder safety))) = 2 ->
  Void
shiftedStartAliasContradictsWhole whole leftBound rightBound leftStart
  rightStart =
    wholeSelectedCoordinateAliasImpossible whole 1 0 leftBound rightBound
      (rewrite leftStart in rewrite rightStart in Refl)

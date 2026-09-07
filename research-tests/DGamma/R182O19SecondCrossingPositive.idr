module DGamma.R182O19SecondCrossingPositive

import DGamma.R182O19ActualCrossingPositive
import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R182O19RevisedSafetyPositive
import DGamma.R182O19RevisedSafetyNegative
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| B20: input-free REAL first TWO Cartesian crossings. Both suffix replays
||| are produced, and the final bundle/uniqueness belong to the same actual
||| second reached trace. Separate module avoids rechecking the 179s B19 body.
public export
0 r182ActualSecondCrossing :
  (firstDiamond : LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq
    (Fired {before = r182IndependentState 3} {afterState = r182IndependentState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl)
    (Fired {before = r182IndependentState 4} {afterState = r182IndependentState 5} r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl) **
   (firstResult : AdjacentSwapResult Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq (r182IndependentTrace False)
      (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) NoTransitions)))
      (Fired {before = r182IndependentState 3} {afterState = r182IndependentState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl)
      (Fired {before = r182IndependentState 4} {afterState = r182IndependentState 5} r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl)
      (MoreTransitions (Fired {before = r182IndependentState 5} {afterState = r182IndependentState 6} r45NameEq r45KeyEq (LAdvance 1) LFinishTag Refl) NoTransitions) firstDiamond **
    (secondDiamond : LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq
       (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) (movedRight firstDiamond) **
     (secondResult : AdjacentSwapResult Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq (swappedTrace firstResult)
        (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) NoTransitions))
        (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) (movedRight firstDiamond)
        (MoreTransitions (movedLeft firstDiamond) (replayedSuffix firstResult)) secondDiamond **
      (NonEmptyFiniteAdjacentSwapDerivation Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq (r182IndependentTrace False) (swappedTrace secondResult),
       UniqueRawNameInsertions Nat R45Key Unit String R45Value r45NameEq r45KeyEq (swappedTrace secondResult))))))
r182ActualSecondCrossing = r182SecondCrossingObserved r182ActualFirstCrossing

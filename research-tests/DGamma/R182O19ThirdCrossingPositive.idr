module DGamma.R182O19ThirdCrossingPositive

import DGamma.R182O19ThirdCrossingConstruction
import DGamma.R182O19RemainingCrossingFacts
import DGamma.R182O19SecondCrossingPositive
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5ConfluenceRankObservationSpike
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

||| B34: simultaneously assemble the ACTUAL three-node pipeline from the
||| observed two-node package. View and node are PRODUCED HERE; no oracle.
||| The computed producer goes through B33's explicit-argument boundary.
public export
0 r182ThirdCrossingObserved :
  ((firstDiamond : LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq
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
       UniqueRawNameInsertions Nat R45Key Unit String R45Value r45NameEq r45KeyEq (swappedTrace secondResult))))))) ->
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
      (observed : ObservedTwoActionTrace Nat R45Key Unit String R45Value r45NameEq r45KeyEq (LAdvance 0) (LAdvance 1) (replayedSuffix secondResult) **
  (thirdDiamond : LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq (twoActionFirst observed) (twoActionSecond observed) **
   (thirdResult : AdjacentSwapResult Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq (swappedTrace secondResult)
     (appendTransitions (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) NoTransitions)) (MoreTransitions (movedRight secondDiamond) (MoreTransitions (movedLeft secondDiamond) NoTransitions)))
     (twoActionFirst observed) (twoActionSecond observed) NoTransitions thirdDiamond **
    (NonEmptyFiniteAdjacentSwapDerivation Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq (r182IndependentTrace False) (swappedTrace thirdResult),
     UniqueRawNameInsertions Nat R45Key Unit String R45Value r45NameEq r45KeyEq (swappedTrace thirdResult)))))))))
r182ThirdCrossingObserved
  (firstDiamond ** (firstResult ** (secondDiamond ** (secondResult ** (reachedDerivation, reachedUnique))))) =
    (firstDiamond ** (firstResult ** (secondDiamond ** (secondResult **
      (r182SecondSuffixView firstDiamond firstResult secondDiamond secondResult **
       o19ComposeProduced reachedDerivation
         (r182ThirdCrossingFromView firstDiamond firstResult secondDiamond secondResult reachedUnique
           (r182SecondSuffixView firstDiamond firstResult secondDiamond secondResult)))))))

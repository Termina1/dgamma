module DGamma.R182O19FourthCrossingFacts

import DGamma.R182O19ThirdCrossingPositive
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

||| B36: actual fourth-node early Finish1 at the opaque second middle cut.
||| That cut is identified by checked determinism; moved labels are composed
||| from their SAME diamonds/view. No scalar observer of a replay builder.
public export
0 r182FourthPairEarly :
  (firstDiamond : LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq (Fired {before = r182IndependentState 3} {afterState = r182IndependentState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl) (Fired {before = r182IndependentState 4} {afterState = r182IndependentState 5} r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl)) ->
  (secondDiamond : LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) (movedRight firstDiamond)) ->
  {finalState : SystemState Nat R45Key R45Value Unit String} ->
  {suffix : Transitions (swappedFinal secondDiamond) finalState} ->
  (observed : ObservedTwoActionTrace Nat R45Key Unit String R45Value r45NameEq r45KeyEq
    (LAdvance 0) (LAdvance 1) suffix) ->
  (thirdDiamond : LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq (twoActionFirst observed) (twoActionSecond observed)) ->
  CheckedEarlyApplication Nat R45Key Unit String R45Value r45NameEq r45KeyEq
    (swappedMiddle secondDiamond) (transitionAction (movedRight thirdDiamond))
    (transitionTag (movedRight thirdDiamond))
r182FourthPairEarly firstDiamond secondDiamond observed thirdDiamond =
  o19EarlyLabels r45NameEq r45KeyEq (LAdvance 1) (transitionAction (movedRight thirdDiamond))
    LFinishTag (transitionTag (movedRight thirdDiamond))
    (trans (movedRightAction thirdDiamond) (twoActionSecondExact observed))
    (trans (movedRightTag thirdDiamond) (Builtin.fst (o19AlignedDestination r45NameEq r45KeyEq (twoActionSecond observed) NoTransitions
    (Builtin.snd (alignedAppendSplit (MoreTransitions (twoActionFirst observed) NoTransitions)
      (MoreTransitions (twoActionSecond observed) NoTransitions) (twoActionAligned observed)))
    (LAdvance 1) LFinishTag (twoActionSecondExact observed) (r182IndependentState 6)
    (trans (cong (\state => checkedApplyAction @{r45NameEq} @{r45KeyEq} (LAdvance 1) state)
      (Builtin.snd (o19AlignedDestination r45NameEq r45KeyEq (twoActionFirst observed)
    (MoreTransitions (twoActionSecond observed) NoTransitions) (twoActionAligned observed)
    (LAdvance 0) LFinishTag (twoActionFirstExact observed) (r182IndependentState 5)
    (trans (cong (\state => checkedApplyAction @{r45NameEq} @{r45KeyEq} (LAdvance 0) state)
      (r182SecondPairEnd firstDiamond secondDiamond)) (Builtin.fst r182RemainingPrimitiveChecks))))) Refl))))
    (MkCheckedEarlyApplication (r182IndependentState 8)
      (trans (cong (\state => checkedApplyAction @{r45NameEq} @{r45KeyEq} (LAdvance 1) state)
        (o19MovedRightDestination r45NameEq r45KeyEq
          (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) (movedRight firstDiamond) secondDiamond
          (o19EarlyLabels r45NameEq r45KeyEq (LBegin 1) (transitionAction (movedRight firstDiamond))
            LBeginTag (transitionTag (movedRight firstDiamond))
            (movedRightAction firstDiamond) (movedRightTag firstDiamond)
            (MkCheckedEarlyApplication (r182IndependentState 7) Refl))))
        (Builtin.fst (Builtin.snd (Builtin.snd (Builtin.snd r182RemainingPrimitiveChecks))))))

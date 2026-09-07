module DGamma.R182O19RemainingCrossingFacts

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

||| B26: six PRIMITIVE edge checks on small explicit runtime cuts. The only
||| projected cut is B9's single explicit state constructor, NEVER an opaque
||| diamond or suffix builder. They will be transported to reached cuts by B16.
public export
0 r182RemainingPrimitiveChecks :
  ((checkedApplyAction @{r45NameEq} @{r45KeyEq} (LAdvance 0)
      (earlyApplicationFinal r182FirstCrossingEarly) = Just (LFinishTag, r182IndependentState 5)),
   (checkedApplyAction @{r45NameEq} @{r45KeyEq} (LAdvance 1)
      (earlyApplicationFinal r182FirstCrossingEarly) = Just (LFinishTag, r182IndependentState 9)),
   (checkedApplyAction @{r45NameEq} @{r45KeyEq} (LBegin 0)
      (r182IndependentState 7) = Just (LBeginTag, earlyApplicationFinal r182FirstCrossingEarly)),
   (checkedApplyAction @{r45NameEq} @{r45KeyEq} (LAdvance 1)
      (r182IndependentState 7) = Just (LFinishTag, r182IndependentState 8)),
   (checkedApplyAction @{r45NameEq} @{r45KeyEq} (LAdvance 0)
      (r182IndependentState 9) = Just (LFinishTag, r182IndependentState 6)),
   (checkedApplyAction @{r45NameEq} @{r45KeyEq} (LBegin 0)
      (r182IndependentState 8) = Just (LBeginTag, r182IndependentState 9)))
r182RemainingPrimitiveChecks = (Refl, Refl, Refl, Refl, Refl, Refl)

||| B27: identify the REAL second pair end, not by evaluating the replay,
||| but by its aligned equations and the already checked primitive path.
public export
0 r182SecondPairEnd :
  (firstDiamond : LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq (Fired {before = r182IndependentState 3} {afterState = r182IndependentState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl) (Fired {before = r182IndependentState 4} {afterState = r182IndependentState 5} r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl)) ->
  (secondDiamond : LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) (movedRight firstDiamond)) ->
  (swappedFinal secondDiamond = earlyApplicationFinal r182FirstCrossingEarly)
r182SecondPairEnd firstDiamond secondDiamond =
  o19MovedPairDestination r45NameEq r45KeyEq
    (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) (movedRight firstDiamond) secondDiamond
    (o19EarlyLabels r45NameEq r45KeyEq (LBegin 1) (transitionAction (movedRight firstDiamond))
      LBeginTag (transitionTag (movedRight firstDiamond))
      (movedRightAction firstDiamond) (movedRightTag firstDiamond)
      (MkCheckedEarlyApplication (r182IndependentState 7) Refl))
    (MkCheckedEarlyApplication (earlyApplicationFinal r182FirstCrossingEarly)
      (Builtin.fst (Builtin.snd (Builtin.snd r182RemainingPrimitiveChecks))))

||| B28: derive the actual two-Finish suffix view from BOTH sealed action
||| folds and the second reached bundle. No supplied node/word/shape oracle.
public export
0 r182SecondSuffixView :
  (firstDiamond : LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq (Fired {before = r182IndependentState 3} {afterState = r182IndependentState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl) (Fired {before = r182IndependentState 4} {afterState = r182IndependentState 5} r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl)) ->
  (firstResult : AdjacentSwapResult Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq (r182IndependentTrace False)
    (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) NoTransitions)))
    (Fired {before = r182IndependentState 3} {afterState = r182IndependentState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl) (Fired {before = r182IndependentState 4} {afterState = r182IndependentState 5} r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl)
    (MoreTransitions (Fired {before = r182IndependentState 5} {afterState = r182IndependentState 6} r45NameEq r45KeyEq (LAdvance 1) LFinishTag Refl) NoTransitions) firstDiamond) ->
  (secondDiamond : LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) (movedRight firstDiamond)) ->
  (secondResult : AdjacentSwapResult Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq (swappedTrace firstResult)
    (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) NoTransitions))
    (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) (movedRight firstDiamond)
    (MoreTransitions (movedLeft firstDiamond) (replayedSuffix firstResult)) secondDiamond) ->
  ObservedTwoActionTrace Nat R45Key Unit String R45Value r45NameEq r45KeyEq
    (LAdvance 0) (LAdvance 1) (replayedSuffix secondResult)
r182SecondSuffixView firstDiamond firstResult secondDiamond secondResult =
  o19TwoActionTraceObserved r45NameEq r45KeyEq (LAdvance 0) (LAdvance 1)
    (replayedSuffix secondResult)
    (o19ReplayedSuffixAligned r45NameEq r45KeyEq r45Protocol (swappedTrace firstResult)
      (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) NoTransitions))
      (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) (movedRight firstDiamond)
      (MoreTransitions (movedLeft firstDiamond) (replayedSuffix firstResult)) secondDiamond secondResult)
    (trans (o19SealedActionWord r45NameEq r45KeyEq (sealedSuffixReplay secondResult))
      (trans (cong (\action => action :: o19ActionWord (replayedSuffix firstResult))
        (movedLeftAction firstDiamond))
        (cong ((LAdvance 0) ::)
          (o19SealedActionWord r45NameEq r45KeyEq (sealedSuffixReplay firstResult)))))

||| B29: derive BOTH actual Finish classes and right-first applicability at
||| the REAL second reached cut. All observations are explicit; no assumed
||| tag, view equality, target state or independent current bundle is added.
public export
0 r182ThirdPairFacts :
  (firstDiamond : LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq (Fired {before = r182IndependentState 3} {afterState = r182IndependentState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl) (Fired {before = r182IndependentState 4} {afterState = r182IndependentState 5} r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl)) ->
  (secondDiamond : LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) (movedRight firstDiamond)) ->
  {finalState : SystemState Nat R45Key R45Value Unit String} ->
  {suffix : Transitions (swappedFinal secondDiamond) finalState} ->
  (observed : ObservedTwoActionTrace Nat R45Key Unit String R45Value r45NameEq r45KeyEq
    (LAdvance 0) (LAdvance 1) suffix) ->
  (PaperActivationStep (twoActionFirst observed),
   PaperActivationStep (twoActionSecond observed),
   CheckedEarlyApplication Nat R45Key Unit String R45Value r45NameEq r45KeyEq
     (swappedFinal secondDiamond) (transitionAction (twoActionSecond observed))
     (transitionTag (twoActionSecond observed)))
r182ThirdPairFacts firstDiamond secondDiamond observed =
  (PaperFinishStep (twoActionFirstExact observed) (Builtin.fst (o19AlignedDestination r45NameEq r45KeyEq (twoActionFirst observed)
    (MoreTransitions (twoActionSecond observed) NoTransitions) (twoActionAligned observed)
    (LAdvance 0) LFinishTag (twoActionFirstExact observed) (r182IndependentState 5)
    (trans (cong (\state => checkedApplyAction @{r45NameEq} @{r45KeyEq} (LAdvance 0) state)
      (r182SecondPairEnd firstDiamond secondDiamond)) (Builtin.fst r182RemainingPrimitiveChecks)))),
   PaperFinishStep (twoActionSecondExact observed) (Builtin.fst (o19AlignedDestination r45NameEq r45KeyEq (twoActionSecond observed) NoTransitions
    (Builtin.snd (alignedAppendSplit (MoreTransitions (twoActionFirst observed) NoTransitions)
      (MoreTransitions (twoActionSecond observed) NoTransitions) (twoActionAligned observed)))
    (LAdvance 1) LFinishTag (twoActionSecondExact observed) (r182IndependentState 6)
    (trans (cong (\state => checkedApplyAction @{r45NameEq} @{r45KeyEq} (LAdvance 1) state)
      (Builtin.snd (o19AlignedDestination r45NameEq r45KeyEq (twoActionFirst observed)
    (MoreTransitions (twoActionSecond observed) NoTransitions) (twoActionAligned observed)
    (LAdvance 0) LFinishTag (twoActionFirstExact observed) (r182IndependentState 5)
    (trans (cong (\state => checkedApplyAction @{r45NameEq} @{r45KeyEq} (LAdvance 0) state)
      (r182SecondPairEnd firstDiamond secondDiamond)) (Builtin.fst r182RemainingPrimitiveChecks))))) Refl))),
   o19EarlyLabels r45NameEq r45KeyEq (LAdvance 1) (transitionAction (twoActionSecond observed))
     LFinishTag (transitionTag (twoActionSecond observed)) (twoActionSecondExact observed)
     (Builtin.fst (o19AlignedDestination r45NameEq r45KeyEq (twoActionSecond observed) NoTransitions
    (Builtin.snd (alignedAppendSplit (MoreTransitions (twoActionFirst observed) NoTransitions)
      (MoreTransitions (twoActionSecond observed) NoTransitions) (twoActionAligned observed)))
    (LAdvance 1) LFinishTag (twoActionSecondExact observed) (r182IndependentState 6)
    (trans (cong (\state => checkedApplyAction @{r45NameEq} @{r45KeyEq} (LAdvance 1) state)
      (Builtin.snd (o19AlignedDestination r45NameEq r45KeyEq (twoActionFirst observed)
    (MoreTransitions (twoActionSecond observed) NoTransitions) (twoActionAligned observed)
    (LAdvance 0) LFinishTag (twoActionFirstExact observed) (r182IndependentState 5)
    (trans (cong (\state => checkedApplyAction @{r45NameEq} @{r45KeyEq} (LAdvance 0) state)
      (r182SecondPairEnd firstDiamond secondDiamond)) (Builtin.fst r182RemainingPrimitiveChecks))))) Refl)))
     (MkCheckedEarlyApplication (r182IndependentState 9)
       (trans (cong (\state => checkedApplyAction @{r45NameEq} @{r45KeyEq} (LAdvance 1) state)
      (r182SecondPairEnd firstDiamond secondDiamond)) (Builtin.fst (Builtin.snd r182RemainingPrimitiveChecks)))))

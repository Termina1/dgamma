module DGamma.R182O19RemainingCrossingFacts

import DGamma.R182O19SecondCrossingPositive
import DGamma.CP5O19ReplayObservationSpike
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

module DGamma.R185O19ActivationInsertionRowPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5O19ActivationInsertionRowSpike
import DGamma.R182O19AdjacencyNegative
import DGamma.CP5O19ResolvedOpeningRowSpike
import DGamma.CP5O19ActivationRowSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19OpeningPropagationSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R182O19RevisedSafetyPositive
import DGamma.R182O19ActualCrossingPositive
import DGamma.R182O19RevisedSafetyNegative
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Actual-source insertion ordinal authentication, not a replay-builder
||| scalar observation. The three source birth positions are 0,1,4.
export
0 r185GapBirthPosition : (selected, ordinal : Nat) ->
  (rawInsertionNameAt Nat R45Key Unit String R45Value ordinal (Builtin.fst r182GapTrace) = Just selected) ->
  (ordinal = selected * selected)
r185GapBirthPosition selected Z observed = cong (\actual => actual * actual) (justInjective observed)
r185GapBirthPosition selected (S Z) observed = cong (\actual => actual * actual) (justInjective observed)
r185GapBirthPosition selected (S (S Z)) observed = case observed of Refl impossible
r185GapBirthPosition selected (S (S (S Z))) observed = case observed of Refl impossible
r185GapBirthPosition selected (S (S (S (S Z)))) observed = cong (\actual => actual * actual) (justInjective observed)
r185GapBirthPosition selected (S (S (S (S (S Z))))) observed = case observed of Refl impossible
r185GapBirthPosition selected (S (S (S (S (S (S Z)))))) observed = case observed of Refl impossible
r185GapBirthPosition selected (S (S (S (S (S (S (S Z))))))) observed = case observed of Refl impossible
r185GapBirthPosition selected (S (S (S (S (S (S (S (S Z)))))))) observed = case observed of Refl impossible
r185GapBirthPosition selected (S (S (S (S (S (S (S (S (S later))))))))) observed = case observed of Refl impossible

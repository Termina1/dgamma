module DGamma.R182O19ActualCrossingPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R182O19RevisedSafetyPositive
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| B9: executable first CARTESIAN crossing guard at actual cut3: moving
||| right Begin1 left across left Finish0. Both fibers become Reloading;
||| the exact inserted-registry uniqueness token is retained by the producer.
public export
0 r182FirstCrossingEarly : CheckedEarlyApplication Nat R45Key Unit String R45Value
  r45NameEq r45KeyEq (r182IndependentState 3) (LBegin 1) LBeginTag
r182FirstCrossingEarly = MkCheckedEarlyApplication
  (MkSystemState ()
    (MkCoeffectContext
      [Bind 1 (MkFiber r45Child Root False emptyOwned (Reloading [] id EmptyView)),
       Bind 0 (MkFiber r45Child Root False emptyOwned (Reloading [] id EmptyView))]
      (uniqueBindings (registry (r182IndependentState 2))))) Refl

||| B10: actual insertion occurrence classifier (R181 F5 technique), not an
||| assumed uniqueness input or a scalar Maybe-execution-builder observer.
public export
0 r182IndependentBirthPosition : (selected, ordinal : Nat) ->
  (rawInsertionNameAt Nat R45Key Unit String R45Value ordinal (r182IndependentTrace False) =
    Just selected) -> (ordinal = selected)
r182IndependentBirthPosition selected Z observed = justInjective observed
r182IndependentBirthPosition selected (S Z) observed = justInjective observed
r182IndependentBirthPosition selected (S (S Z)) observed = case observed of Refl impossible
r182IndependentBirthPosition selected (S (S (S Z))) observed = case observed of Refl impossible
r182IndependentBirthPosition selected (S (S (S (S Z)))) observed = case observed of Refl impossible
r182IndependentBirthPosition selected (S (S (S (S (S Z))))) observed = case observed of Refl impossible
r182IndependentBirthPosition selected (S (S (S (S (S (S later)))))) observed =
  case observed of Refl impossible

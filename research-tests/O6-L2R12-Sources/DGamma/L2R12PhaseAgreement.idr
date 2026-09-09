module DGamma.L2R12PhaseAgreement

import Prelude.Types
import Prelude.Interfaces
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R6ForcedScan
import DGamma.L2R9OrdinalScan
import DGamma.L2R9OrdinalTrails
import DGamma.L2R10OrdinalData
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core
import Decidable.Decidable

%default total
%unbound_implicits off

||| Discharge the bounded whole-trail agreement residue on the two public
||| seed-component/cut4 data fixtures by the checked omega data equations.
||| This is NOT the frozen general filter-head statement or a phase producer.
export
0 phaseFixtureBoundedAgreement :
  (scanReleaseOrdinals (fst fixtureDictionaries) (snd fixtureDictionaries)
     (smallComponent True) 0 4 (fst ordinalFixtureTrails) =
   filter (\ordinal => ordinal < 4) (releaseOrdinalScan (fst fixtureDictionaries)
     (snd fixtureDictionaries) (smallComponent True) (fst ordinalFixtureTrails)),
   scanReleaseOrdinals (fst fixtureDictionaries) (snd fixtureDictionaries)
     (smallComponent True) 0 4 (snd ordinalFixtureTrails) =
   filter (\ordinal => ordinal < 4) (releaseOrdinalScan (fst fixtureDictionaries)
     (snd fixtureDictionaries) (smallComponent True) (snd ordinalFixtureTrails)))
phaseFixtureBoundedAgreement =
  (trans (fst (snd (snd ordinalDataAgreement)))
    (sym (cong (filter (\ordinal => ordinal < 4)) (fst ordinalDataAgreement))),
   trans (snd (snd (snd ordinalDataAgreement)))
    (sym (cong (filter (\ordinal => ordinal < 4)) (fst (snd ordinalDataAgreement)))))

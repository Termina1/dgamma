module DGamma.L2R6ForcedFixtures

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R3ForcedClosure
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Three actual trails with simultaneous observed classifier results. The
||| third starts at smallState4: a native root insertion BEFORE Begin2, no
||| earlier release in that trace. R is key-forced in the full traces; S has
||| no key release and is independently derived by the least barrier closure.
public export
record ForcedClassifierFixtures where
  constructor MkForcedClassifierFixtures
  singleForcedTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) smallTrace
  barrierForcedTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) barrierTrace
  frontRootTrace : Transitions (smallState 4) (smallState 6)
  frontRootTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) frontRootTrace
  singleClassified : List (Nat, Bool)
  barrierClassified : List (Nat, Bool)
  frontClassified : List (Nat, Bool)
  0 singleClassificationEquation : classifyForced %search %search singleForcedTrail (scanRootCatalog 0 singleForcedTrail) Refl = singleClassified
  0 barrierClassificationEquation : classifyForced %search %search barrierForcedTrail (scanRootCatalog 0 barrierForcedTrail) Refl = barrierClassified
  0 frontClassificationEquation : classifyForced %search %search frontRootTrail (scanRootCatalog 0 frontRootTrail) Refl = frontClassified
  0 singleClassificationExpected : singleClassified = [(3, True)]
  0 barrierClassificationExpected : barrierClassified = [(3, True), (4, True)]
  0 frontClassificationExpected : frontClassified = [(3, False)]
  0 singleReleaseComputed : scanReleaseOrdinals %search %search (smallComponent True) 0 4 singleForcedTrail = [3]
  0 barrierReleaseComputed : scanReleaseOrdinals %search %search (smallComponent True) 0 4 barrierForcedTrail = [3]
  0 sNotKeyForced : keyForcedOrdinal %search %search barrierForcedTrail 5 = False
  0 singleClosure : ForcedOnTrace %search %search singleForcedTrail 4
  0 barrierClosure : ForcedOnTrace %search %search barrierForcedTrail 5

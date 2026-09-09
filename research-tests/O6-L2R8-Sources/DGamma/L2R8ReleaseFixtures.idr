module DGamma.L2R8ReleaseFixtures

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R3Attached
import DGamma.L2R6ForcedScan
import DGamma.L2R8ReleaseScan
import Data.List
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Concrete comparison over the isElem release scan; agreement with
||| scanReleaseOrdinals open GENERALLY. Contract requiring both native fixtures to
||| compute the same exact filtered release list; TYPE ONLY — producer OPEN
||| (L2R8 A10 3/3). The new
||| lists contain decoded actual occurrences with parent and shared key.
public export
record ObservedReleaseFixtures where
  constructor MkObservedReleaseFixtures
  singleTrace : Transitions (smallState 0) (smallState 7)
  barrierNativeTrace : Transitions (barrierState 0) (barrierState 8)
  singleTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) singleTrace
  barrierTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) barrierNativeTrace
  singleOrdinals : List Nat
  barrierOrdinals : List Nat
  0 singleNewEquation : filter (< 4) (map (\release => locatedActionOrdinal (releaseOccurrence (snd release)))
    (scanObservedReleases %search %search (smallComponent True) singleTrail)) = singleOrdinals
  0 barrierNewEquation : filter (< 4) (map (\release => locatedActionOrdinal (releaseOccurrence (snd release)))
    (scanObservedReleases %search %search (smallComponent True) barrierTrail)) = barrierOrdinals
  0 singleOldEquation : scanReleaseOrdinals %search %search (smallComponent True) 0 4 singleTrail = singleOrdinals
  0 barrierOldEquation : scanReleaseOrdinals %search %search (smallComponent True) 0 4 barrierTrail = barrierOrdinals
  0 singleExpected : singleOrdinals = [3]
  0 barrierExpected : barrierOrdinals = [3]

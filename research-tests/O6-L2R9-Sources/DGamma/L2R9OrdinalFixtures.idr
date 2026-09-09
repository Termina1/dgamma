module DGamma.L2R9OrdinalFixtures

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
import Data.List
import Decidable.Equality

%default total
%unbound_implicits off

||| Data-level agreement contract over the NEW omega releaseOrdinalScan.
||| Native annotations and all four equations are constructed simultaneously.
||| Does not claim general old/new scan agreement or produced phases.
public export
record OrdinalFixtures where
  constructor MkOrdinalFixtures
  singleTrace : Transitions (smallState 0) (smallState 7)
  barrierNativeTrace : Transitions (barrierState 0) (barrierState 8)
  singleTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) singleTrace
  barrierTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) barrierNativeTrace
  0 singleOmegaComputed : releaseOrdinalScan %search %search (smallComponent True) singleTrail = [3]
  0 barrierOmegaComputed : releaseOrdinalScan %search %search (smallComponent True) barrierTrail = [3]
  0 singleOldComputed : scanReleaseOrdinals %search %search (smallComponent True) 0 4 singleTrail = [3]
  0 barrierOldComputed : scanReleaseOrdinals %search %search (smallComponent True) 0 4 barrierTrail = [3]

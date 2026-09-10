module DGamma.L2R9OrdinalTrails

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

||| Public unrestricted one-origin annotations of the SAME retained native
||| traces. Literal AvailabilityStep data; no opaque availability builder.
public export
ordinalFixtureTrails :
  (DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace Nat Bool Unit String (\key => Unit) smallTrace,
   DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace Nat Bool Unit String (\key => Unit) barrierTrace)
ordinalFixtureTrails =
  ((DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 0) (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) _ (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 1) (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) _ (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 2) (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) _ (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 3) (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) _ (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 4) (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) _ (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 5) (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) _ (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 6) (Fired {before = smallState 6} {afterState = smallState 7} %search %search (LAdvance 2) LFinishTag (smallFinish2 smallNativeExecution)) _ (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd (smallState 7))))))))),
   (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (barrierState 0) (Fired {before = barrierState 0} {afterState = barrierState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) _ (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (barrierState 1) (Fired {before = barrierState 1} {afterState = barrierState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) _ (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (barrierState 2) (Fired {before = barrierState 2} {afterState = barrierState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) _ (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (barrierState 3) (Fired {before = barrierState 3} {afterState = barrierState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) _ (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (barrierState 4) (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) _ (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (barrierState 5) (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) _ (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (barrierState 6) (Fired {before = barrierState 6} {afterState = barrierState 7} %search %search (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution)) _ (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (barrierState 7) (Fired {before = barrierState 7} {afterState = barrierState 8} %search %search (LAdvance 2) LFinishTag (finishFollowing barrierNativeExecution)) _ (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd (barrierState 8)))))))))))

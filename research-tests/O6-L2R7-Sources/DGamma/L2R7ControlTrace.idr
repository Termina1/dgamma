module DGamma.L2R7ControlTrace

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R3Attached
import DGamma.L2R3SmallAttached
import DGamma.L2R7AttachedC
import DGamma.L2R7ControlStates
import DGamma.L2R7ControlExecution
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Ten actual native edges: the original barrier prefix followed by root
||| Retire3/Remove3, then Begin2/Finish2. No replay oracle or synthetic edges.
public export
controlTrace : Transitions (controlState 0) (controlState 10)
controlTrace = (MoreTransitions (Fired {before = controlState 0} {afterState = controlState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) (MoreTransitions (Fired {before = controlState 1} {afterState = controlState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = controlState 2} {afterState = controlState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = controlState 3} {afterState = controlState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = controlState 4} {afterState = controlState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = controlState 5} {afterState = controlState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) (MoreTransitions (Fired {before = controlState 6} {afterState = controlState 7} %search %search (ORetire 3) ORetireTag (retireR controlNativeExecution)) (MoreTransitions (Fired {before = controlState 7} {afterState = controlState 8} %search %search (ORemove 3) ORemoveTag (removeR controlNativeExecution)) (MoreTransitions (Fired {before = controlState 8} {afterState = controlState 9} %search %search (LBegin 2) LBeginTag (beginControlFollowing controlNativeExecution)) (MoreTransitions (Fired {before = controlState 9} {afterState = controlState 10} %search %search (LAdvance 2) LFinishTag (finishControlFollowing controlNativeExecution)) NoTransitions))))))))))

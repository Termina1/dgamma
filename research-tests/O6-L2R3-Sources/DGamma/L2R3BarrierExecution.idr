module DGamma.L2R3BarrierExecution

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3BarrierStates
import Decidable.Equality

%default total
%unbound_implicits off

||| Three new native edges after the unchanged L2R2 freeing prefix and Root3.
||| S declares no provision at all. Its provisions are free at every displayed
||| cut (including before the key-release); its position after R is order-forced.
public export
record BarrierNativeExecution where
  constructor MkBarrierNativeExecution
  0 insertS : checkedApplyAction @{%search} @{%search} (OInsert 4 Root (smallComponent False)) (barrierState 5) = Just (OInsertTag, barrierState 6)
  0 beginFollowing : checkedApplyAction @{%search} @{%search} (LBegin 2) (barrierState 6) = Just (LBeginTag, barrierState 7)
  0 finishFollowing : checkedApplyAction @{%search} @{%search} (LAdvance 2) (barrierState 7) = Just (LFinishTag, barrierState 8)
  0 sEmptyProvisions : dependencies (componentProvisions (smallComponent False)) = []
  0 sFreeAtEveryCut : map (\cut => DGamma.CP5AvailabilityAwarePlacement.rootDeclaredProvisionsFree Nat Bool Unit String (\key => Unit) %search (smallComponent False) (barrierState cut)) [0,1,2,3,4,5,6,7,8] = [True,True,True,True,True,True,True,True,True]

||| Simultaneously authenticate the three new native edges and S's empty,
||| always-free provisions directly on one-origin explicit states.
public export
0 barrierNativeExecution : BarrierNativeExecution
barrierNativeExecution = MkBarrierNativeExecution
  (checkedFromRaw %search %search (OInsert 4 Root (smallComponent False)) (barrierState 5) (barrierState 6) OInsertTag (checkedActionTargetValid %search %search (OInsert 3 Root (smallComponent True)) (smallState 4) (smallState 5) OInsertTag (smallInsert3 smallNativeExecution)) Refl)
  (checkedFromRaw %search %search (LBegin 2) (barrierState 6) (barrierState 7) LBeginTag (checkedActionTargetValid %search %search (OInsert 4 Root (smallComponent False)) (barrierState 5) (barrierState 6) OInsertTag (checkedFromRaw %search %search (OInsert 4 Root (smallComponent False)) (barrierState 5) (barrierState 6) OInsertTag (checkedActionTargetValid %search %search (OInsert 3 Root (smallComponent True)) (smallState 4) (smallState 5) OInsertTag (smallInsert3 smallNativeExecution)) Refl)) Refl)
  (checkedFromRaw %search %search (LAdvance 2) (barrierState 7) (barrierState 8) LFinishTag (checkedActionTargetValid %search %search (LBegin 2) (barrierState 6) (barrierState 7) LBeginTag (checkedFromRaw %search %search (LBegin 2) (barrierState 6) (barrierState 7) LBeginTag (checkedActionTargetValid %search %search (OInsert 4 Root (smallComponent False)) (barrierState 5) (barrierState 6) OInsertTag (checkedFromRaw %search %search (OInsert 4 Root (smallComponent False)) (barrierState 5) (barrierState 6) OInsertTag (checkedActionTargetValid %search %search (OInsert 3 Root (smallComponent True)) (smallState 4) (smallState 5) OInsertTag (smallInsert3 smallNativeExecution)) Refl)) Refl)) Refl)
  Refl Refl

||| Eight checked edges, sharing smallState0 as the only origin. R at ordinal4
||| then S at ordinal5 follow the actual child removal; actor2 starts at cut6.
public export
barrierTrace : Transitions (barrierState 0) (barrierState 8)
barrierTrace = (MoreTransitions (Fired {before = barrierState 0} {afterState = barrierState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 1} {afterState = barrierState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 2} {afterState = barrierState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 3} {afterState = barrierState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) (MoreTransitions (Fired {before = barrierState 6} {afterState = barrierState 7} %search %search (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution)) (MoreTransitions (Fired {before = barrierState 7} {afterState = barrierState 8} %search %search (LAdvance 2) LFinishTag (finishFollowing barrierNativeExecution)) NoTransitions))))))))

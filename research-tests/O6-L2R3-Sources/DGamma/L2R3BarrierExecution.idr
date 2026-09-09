module DGamma.L2R3BarrierExecution

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
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
  0 sFreeAtEveryCut : map (\cut => rootDeclaredProvisionsFree Nat Bool Unit String (\key => Unit) %search (smallComponent False) (barrierState cut)) [0,1,2,3,4,5,6,7,8] = [True,True,True,True,True,True,True,True,True]

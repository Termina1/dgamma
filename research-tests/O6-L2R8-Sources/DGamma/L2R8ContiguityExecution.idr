module DGamma.L2R8ContiguityExecution

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2SmallStates
import DGamma.L2R8ContiguityStates
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Producer-owned exact native equations for all THREE schedules. Snapshot
||| equality concerns their final states, not incompatible old/new core starts.
public export
record ContiguityNativeExecution
  (states : Nat -> SystemState Nat Bool (\key => Unit) Unit String) where
  constructor MkContiguityNativeExecution
  0 contiguityEdge0 : checkedApplyAction @{%search} @{%search} (OInsert 5 (ChildOf 2) (smallComponent False)) (states 0) = Just (OInsertTag, contiguityState 1)
  0 contiguityEdge1 : checkedApplyAction @{%search} @{%search} (LBegin 2) (states 1) = Just (LBeginTag, contiguityState 2)
  0 contiguityEdge2 : checkedApplyAction @{%search} @{%search} (LAdvance 2) (states 2) = Just (LFinishTag, contiguityState 3)
  0 contiguityEdge3 : checkedApplyAction @{%search} @{%search} (ORetire 5) (states 3) = Just (ORetireTag, contiguityState 4)
  0 contiguityEdge4 : checkedApplyAction @{%search} @{%search} (ORemove 5) (states 4) = Just (ORemoveTag, contiguityState 5)
  0 contiguityEdge5 : checkedApplyAction @{%search} @{%search} (OInsert 3 Root (smallComponent True)) (states 5) = Just (OInsertTag, contiguityState 6)
  0 contiguityEdge6 : checkedApplyAction @{%search} @{%search} (OInsert 4 Root (smallComponent False)) (states 6) = Just (OInsertTag, contiguityState 7)
  0 contiguityEdge7 : checkedApplyAction @{%search} @{%search} (OInsert 3 Root (smallComponent True)) (states 4) = Just (OInsertTag, contiguityState 8)
  0 contiguityEdge8 : checkedApplyAction @{%search} @{%search} (ORemove 5) (states 8) = Just (ORemoveTag, contiguityState 9)
  0 contiguityEdge9 : checkedApplyAction @{%search} @{%search} (OInsert 4 Root (smallComponent False)) (states 9) = Just (OInsertTag, contiguityState 10)
  0 contiguityEdge10 : checkedApplyAction @{%search} @{%search} (OInsert 3 Root (smallComponent True)) (states 0) = Just (OInsertTag, contiguityState 11)
  0 contiguityEdge11 : checkedApplyAction @{%search} @{%search} (OInsert 5 (ChildOf 2) (smallComponent False)) (states 11) = Just (OInsertTag, contiguityState 12)
  0 contiguityEdge12 : checkedApplyAction @{%search} @{%search} (LBegin 2) (states 12) = Just (LBeginTag, contiguityState 13)
  0 contiguityEdge13 : checkedApplyAction @{%search} @{%search} (LAdvance 2) (states 13) = Just (LFinishTag, contiguityState 14)
  0 contiguityEdge14 : checkedApplyAction @{%search} @{%search} (ORetire 5) (states 14) = Just (ORetireTag, contiguityState 15)
  0 contiguityEdge15 : checkedApplyAction @{%search} @{%search} (ORemove 5) (states 15) = Just (ORemoveTag, contiguityState 16)
  0 contiguityEdge16 : checkedApplyAction @{%search} @{%search} (OInsert 4 Root (smallComponent False)) (states 16) = Just (OInsertTag, contiguityState 17)
  0 contiguityEnd1 : runtimeSnapshot (states 7) = runtimeSnapshot (states 10)
  0 contiguityEnd2 : runtimeSnapshot (states 7) = runtimeSnapshot (states 17)

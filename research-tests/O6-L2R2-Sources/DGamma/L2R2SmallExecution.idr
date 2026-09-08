module DGamma.L2R2SmallExecution

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2SmallStates
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Producer-owned native equations on the explicit small states. Seven
||| physical edges and two alternate square edges share literal state6/state7
||| endpoints. Native rejected insertion observations authenticate the key
||| collision BEFORE removal (including after retirement).
public export
record SmallNativeExecution where
  constructor MkSmallNativeExecution
  0 smallSourceValid : registryWellFormed @{%search} @{%search} (smallState 0) = True
  0 smallBegin0 : checkedApplyAction @{%search} @{%search} (LBegin 0) (smallState 0) = Just (LBeginTag, smallState 1)
  0 smallFinish0 : checkedApplyAction @{%search} @{%search} (LAdvance 0) (smallState 1) = Just (LFinishTag, smallState 2)
  0 smallRetire1 : checkedApplyAction @{%search} @{%search} (ORetire 1) (smallState 2) = Just (ORetireTag, smallState 3)
  0 smallRemove1 : checkedApplyAction @{%search} @{%search} (ORemove 1) (smallState 3) = Just (ORemoveTag, smallState 4)
  0 smallInsert3 : checkedApplyAction @{%search} @{%search} (OInsert 3 Root (smallComponent True)) (smallState 4) = Just (OInsertTag, smallState 5)
  0 smallBegin2 : checkedApplyAction @{%search} @{%search} (LBegin 2) (smallState 5) = Just (LBeginTag, smallState 6)
  0 smallFinish2 : checkedApplyAction @{%search} @{%search} (LAdvance 2) (smallState 6) = Just (LFinishTag, smallState 7)
  0 smallEarlyBegin2 : checkedApplyAction @{%search} @{%search} (LBegin 2) (smallState 4) = Just (LBeginTag, smallState 8)
  0 smallLateInsert3 : checkedApplyAction @{%search} @{%search} (OInsert 3 Root (smallComponent True)) (smallState 8) = Just (OInsertTag, smallState 6)
  0 smallRootBlockedInitially : checkedApplyAction @{%search} @{%search} (OInsert 3 Root (smallComponent True)) (smallState 0) = Nothing
  0 smallRootBlockedRetired : checkedApplyAction @{%search} @{%search} (OInsert 3 Root (smallComponent True)) (smallState 3) = Nothing

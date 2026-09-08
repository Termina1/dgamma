module DGamma.L2R2SmallExecution

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2SmallStates
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Producer-owned native equations on the explicit small states. Seven
||| physical edges have literal endpoint state7; the alternate root pair ends
||| at state9, SNAPSHOT-equal to state6 but not proof-identical. Native rejected
||| insertion observations authenticate the key
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
  0 smallLateInsert3 : checkedApplyAction @{%search} @{%search} (OInsert 3 Root (smallComponent True)) (smallState 8) = Just (OInsertTag, smallState 9)
  0 smallAlternateSnapshot : runtimeSnapshot (smallState 9) = runtimeSnapshot (smallState 6)
  0 smallRootBlockedInitially : checkedApplyAction @{%search} @{%search} (OInsert 3 Root (smallComponent True)) (smallState 0) = Nothing
  0 smallRootBlockedRetired : checkedApplyAction @{%search} @{%search} (OInsert 3 Root (smallComponent True)) (smallState 3) = Nothing

||| Simultaneously authenticate all nine native edges and both collision
||| rejections directly on the small explicit states. This is a single
||| constructor producer, not scalar reflection over a nested trace builder.
public export
0 smallNativeExecution : SmallNativeExecution
smallNativeExecution = MkSmallNativeExecution Refl Refl Refl Refl Refl Refl Refl Refl Refl Refl Refl Refl Refl

||| The seven-edge native A12 execution. The parent completes, then its own
||| child is retired and removed, then the newly available root is inserted,
||| then the unrelated actor completes. No fallback evaluator or alleged
||| normalization is involved; the endpoint is LITERALLY smallState7.
public export
smallTrace : Transitions (smallState 0) (smallState 7)
smallTrace =
  MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1}
    %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution))
    (    MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2}
      %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution))
      (      MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3}
        %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution))
        (        MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4}
          %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution))
          (          MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5}
            %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution))
            (            MoreTransitions (Fired {before = smallState 5} {afterState = smallState 6}
              %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution))
              (              MoreTransitions (Fired {before = smallState 6} {afterState = smallState 7}
                %search %search (LAdvance 2) LFinishTag (smallFinish2 smallNativeExecution))
                (NoTransitions)))))))

module DGamma.L2R9RestoredPackets

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R8ContiguityStates
import DGamma.L2R8ContiguityExecution
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Restored-path first THREE native equations. Abstract state family keeps
||| the packet contract separate from concrete native normalization cost.
public export
record RestoredFirstPacket (states : Nat -> SystemState Nat Bool (\key => Unit) Unit String) where
  constructor MkRestoredFirstPacket
  0 restoredEdge10 : checkedApplyAction @{%search} @{%search} (OInsert 3 Root (smallComponent True)) (states 0) = Just (OInsertTag, states 11)
  0 restoredEdge11 : checkedApplyAction @{%search} @{%search} (OInsert 5 (ChildOf 2) (smallComponent False)) (states 11) = Just (OInsertTag, states 12)
  0 restoredEdge12 : checkedApplyAction @{%search} @{%search} (LBegin 2) (states 12) = Just (LBeginTag, states 13)

||| Native restored-prefix producer: move R BEFORE the original B core.
||| R's edge is the SAME inherited smallState4 insertion; new child insertion
||| and Begin2 derive source validity from the preceding checked target.
export
0 contiguityRestoredFirst : RestoredFirstPacket contiguityState
contiguityRestoredFirst = MkRestoredFirstPacket {states = contiguityState}
  (smallInsert3 smallNativeExecution)
  (checkedFromRaw %search %search (OInsert 5 (ChildOf 2) (smallComponent False)) (contiguityState 11) (contiguityState 12) OInsertTag (checkedActionTargetValid %search %search (OInsert 3 Root (smallComponent True)) (contiguityState 0) (contiguityState 11) OInsertTag (smallInsert3 smallNativeExecution)) Refl)
  (checkedFromRaw %search %search (LBegin 2) (contiguityState 12) (contiguityState 13) LBeginTag (checkedActionTargetValid %search %search (OInsert 5 (ChildOf 2) (smallComponent False)) (contiguityState 11) (contiguityState 12) OInsertTag (checkedFromRaw %search %search (OInsert 5 (ChildOf 2) (smallComponent False)) (contiguityState 11) (contiguityState 12) OInsertTag (checkedActionTargetValid %search %search (OInsert 3 Root (smallComponent True)) (contiguityState 0) (contiguityState 11) OInsertTag (smallInsert3 smallNativeExecution)) Refl)) Refl)

||| Restored-path last FOUR native equations, not the split-path packet.
public export
record RestoredLastPacket (states : Nat -> SystemState Nat Bool (\key => Unit) Unit String) where
  constructor MkRestoredLastPacket
  0 restoredEdge13 : checkedApplyAction @{%search} @{%search} (LAdvance 2) (states 13) = Just (LFinishTag, states 14)
  0 restoredEdge14 : checkedApplyAction @{%search} @{%search} (ORetire 5) (states 14) = Just (ORetireTag, states 15)
  0 restoredEdge15 : checkedApplyAction @{%search} @{%search} (ORemove 5) (states 15) = Just (ORemoveTag, states 16)
  0 restoredEdge16 : checkedApplyAction @{%search} @{%search} (OInsert 4 Root (smallComponent False)) (states 16) = Just (OInsertTag, states 17)

module DGamma.L2R9ContiguityPackets

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

||| Original-path native equation packet: first FIVE edges only, below the
||| six-equation cap. No alternative evaluator or supplied native edge oracle.
export
0 contiguityOriginalFirst :
  ((checkedApplyAction @{%search} @{%search} (OInsert 5 (ChildOf 2) (smallComponent False)) (contiguityState 0) = Just (OInsertTag, contiguityState 1)),
   (checkedApplyAction @{%search} @{%search} (LBegin 2) (contiguityState 1) = Just (LBeginTag, contiguityState 2)),
   (checkedApplyAction @{%search} @{%search} (LAdvance 2) (contiguityState 2) = Just (LFinishTag, contiguityState 3)),
   (checkedApplyAction @{%search} @{%search} (ORetire 5) (contiguityState 3) = Just (ORetireTag, contiguityState 4)),
   (checkedApplyAction @{%search} @{%search} (ORemove 5) (contiguityState 4) = Just (ORemoveTag, contiguityState 5)))
contiguityOriginalFirst = (Refl, Refl, Refl, Refl, Refl)

||| Original-path suffix packet: native R then S after the complete B core.
export
0 contiguityOriginalLast :
  ((checkedApplyAction @{%search} @{%search} (OInsert 3 Root (smallComponent True)) (contiguityState 5) = Just (OInsertTag, contiguityState 6)),
   (checkedApplyAction @{%search} @{%search} (OInsert 4 Root (smallComponent False)) (contiguityState 6) = Just (OInsertTag, contiguityState 7)))
contiguityOriginalLast = (Refl, Refl)

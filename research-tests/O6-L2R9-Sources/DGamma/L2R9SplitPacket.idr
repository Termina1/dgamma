module DGamma.L2R9SplitPacket

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

||| Three native equations for the split path, with states abstract during
||| contract elaboration. Exactly the B4 packet's three edges; TYPE ONLY.
public export
record SplitPathPacket (states : Nat -> SystemState Nat Bool (\key => Unit) Unit String) where
  constructor MkSplitPathPacket
  0 splitRoot : checkedApplyAction @{%search} @{%search} (OInsert 3 Root (smallComponent True)) (states 4) = Just (OInsertTag, states 8)
  0 splitRemove : checkedApplyAction @{%search} @{%search} (ORemove 5) (states 8) = Just (ORemoveTag, states 9)
  0 splitBarrier : checkedApplyAction @{%search} @{%search} (OInsert 4 Root (smallComponent False)) (states 9) = Just (OInsertTag, states 10)

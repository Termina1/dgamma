module DGamma.L2R7ControlExecution

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressNoDeadlock
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R7ControlStates
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Four additional native edges after the SAME original freeing/R/S prefix.
||| Actual lookup observations authenticate control roots, not stale names.
public export
record ControlNativeExecution where
  constructor MkControlNativeExecution
  0 retireR : checkedApplyAction @{%search} @{%search} (ORetire 3) (controlState 6) = Just (ORetireTag, controlState 7)
  0 removeR : checkedApplyAction @{%search} @{%search} (ORemove 3) (controlState 7) = Just (ORemoveTag, controlState 8)
  0 beginControlFollowing : checkedApplyAction @{%search} @{%search} (LBegin 2) (controlState 8) = Just (LBeginTag, controlState 9)
  0 finishControlFollowing : checkedApplyAction @{%search} @{%search} (LAdvance 2) (controlState 9) = Just (LFinishTag, controlState 10)
  0 retireRootFound : lookupFiber {name = Nat} {key = Bool} {value = (\key => Unit)} {world = Unit} {error = String} @{%search} 3 (registry (controlState 6)) = Just (freshFiber (smallComponent True) Root)
  0 removeRootFound : lookupFiber {name = Nat} {key = Bool} {value = (\key => Unit)} {world = Unit} {error = String} @{%search} 3 (registry (controlState 7)) = Just (retireFiber (freshFiber (smallComponent True) Root))

||| Simultaneous native checker/lookup equations on the one-origin states.
||| This is not scalar reflection over a nested transition builder.
public export
0 controlNativeExecution : ControlNativeExecution
controlNativeExecution = MkControlNativeExecution Refl Refl Refl Refl Refl Refl

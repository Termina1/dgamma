module DGamma.L2R2RootSnapshot

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5L2R1RootExchange
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Supervisor-approved research SNAPSHOT counterpart of
||| CP5L2R1RootExchange:19 AvailabilityRootExchange. Native role, cut-availability
||| and both checked alternate edges are retained. The late endpoint is NEW,
||| related by exact world/ordered bindings, not erased uniqueness identity.
||| This is an auxiliary square, not the full CanonicalSort:1583 hoist package
||| nor an inhabitant of CP3:3156 CanonicalInputPlacement.
public export
record AvailabilityRootSnapshotExchange
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (root : name) (component : Component key value world error)
  {first, middle, finalState : SystemState name key value world error}
  (left : Transition first middle) (right : Transition middle finalState) where
  constructor MkAvailabilityRootSnapshotExchange
  0 snapshotRootDistinct : Not (root = transitionActor left)
  0 snapshotRootAction : transitionAction right = OInsert root Root component
  0 snapshotRootCompatible : rootCutCompatible name key world error value nameEq keyEq component 0
    (AvailabilityStep first left NoTransitions (AvailabilityEnd middle)) = True
  snapshotRootMiddle : SystemState name key value world error
  snapshotRootFinal : SystemState name key value world error
  0 snapshotRootEarly : checkedApplyAction @{nameEq} @{keyEq} (OInsert root Root component) first = Just (OInsertTag, snapshotRootMiddle)
  0 snapshotRootLater : checkedApplyAction @{nameEq} @{keyEq} (transitionAction left) snapshotRootMiddle = Just (transitionTag left, snapshotRootFinal)
  0 snapshotRootSame : runtimeSnapshot finalState = runtimeSnapshot snapshotRootFinal

||| The small native Begin2/Insert3 square after child removal, now at the
||| supervisor-approved snapshot level. Both routes really run; cut4 and cut8
||| are available and the crossed Begin2 is not a root input. The original
||| endpoint is state9, the replay endpoint state6; literal equality is NOT
||| asserted, and the old exact C13 fixture remains parked.
public export
0 smallRootSnapshotSquare : AvailabilityRootSnapshotExchange Nat Bool Unit String (\key => Unit)
  %search %search 3 (smallComponent True)
  (Fired {before = smallState 4} {afterState = smallState 8} %search %search (LBegin 2) LBeginTag (smallEarlyBegin2 smallNativeExecution))
  (Fired {before = smallState 8} {afterState = smallState 9} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution))
smallRootSnapshotSquare = MkAvailabilityRootSnapshotExchange
  (\same => case same of Refl impossible) Refl Refl (smallState 5) (smallState 6)
  (smallInsert3 smallNativeExecution) (smallBegin2 smallNativeExecution) (smallAlternateSnapshot smallNativeExecution)

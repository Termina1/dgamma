module DGamma.L2R2RetireSquare

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import Decidable.Equality

%default total
%unbound_implicits off

||| A square on two existing native edges. Its alternate route is checked;
||| the original and replay endpoints have identical world and ordered bindings.
||| The actual source lookup certifies own-child status. This is the snapshot
||| variant of L2R1's auxiliary ExactChildRetireExchange, not a CP3 copy.
public export
record ChildRetireSnapshotExchange
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (child, parent : name)
  {first, middle, finalState : SystemState name key value world error}
  (left : Transition first middle) (right : Transition middle finalState) where
  constructor MkChildRetireSnapshotExchange
  retireSourceFiber : Fiber name key value world error
  0 retireSourceFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry first) = Just retireSourceFiber
  0 retireOwnParent : fiberParent retireSourceFiber = ChildOf parent
  0 retireForeign : Not (child = transitionActor left)
  0 retireRightAction : transitionAction right = ORetire child
  retireEarlyState : SystemState name key value world error
  retireReplayState : SystemState name key value world error
  0 retireEarlyChecked : checkedApplyAction @{nameEq} @{keyEq} (ORetire child) first = Just (ORetireTag, retireEarlyState)
  0 retireReplayChecked : checkedApplyAction @{nameEq} @{keyEq} (transitionAction left) retireEarlyState = Just (transitionTag left, retireReplayState)
  0 retireReplaySnapshot : runtimeSnapshot finalState = runtimeSnapshot retireReplayState

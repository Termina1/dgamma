module DGamma.L2R2RemoveSquare

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP4DeletionBoundaryLifecycleCore
import DGamma.CP4DeletionBoundaryLifecycleBegin
import DGamma.CP4DeletionBoundaryLifecycleAdvance
import DGamma.CP4DeletionSelectedDeletedOrchestration
import DGamma.CP4DeletionSelectedForeignControlCore
import DGamma.CP5L2R1ChildRelocation
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Checked native own-child Remove exchange with an explicit observed Boolean
||| for the removed binding's absence at the early target. This new package is
||| NOT the exhausted exact childRemoveAtFound statement. Runtime successors
||| remain data; all native equations and ordered-snapshot equality are erased.
public export
record ChildRemoveSnapshotExchange
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (child, parent : name)
  {first, middle, finalState : SystemState name key value world error}
  (left : Transition first middle) (right : Transition middle finalState) where
  constructor MkChildRemoveSnapshotExchange
  removeSourceFiber : Fiber name key value world error
  0 removeSourceFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry first) = Just removeSourceFiber
  0 removeOwnParent : fiberParent removeSourceFiber = ChildOf parent
  0 removeForeign : Not (child = transitionActor left)
  0 removeRightAction : transitionAction right = ORemove child
  removeEarlyState : SystemState name key value world error
  removeReplayState : SystemState name key value world error
  removeBindingPresent : Bool
  0 removeBindingObserved : memberKey @{nameEq} child (registry removeEarlyState) = removeBindingPresent
  0 removeBindingAbsent : removeBindingPresent = False
  0 removeEarlyChecked : checkedApplyAction @{nameEq} @{keyEq} (ORemove child) first = Just (ORemoveTag, removeEarlyState)
  0 removeReplayChecked : checkedApplyAction @{nameEq} @{keyEq} (transitionAction left) removeEarlyState = Just (transitionTag left, removeReplayState)
  0 removeReplaySnapshot : runtimeSnapshot finalState = runtimeSnapshot removeReplayState

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
  0 removeForeign : Not (child = actionOwner (transitionAction left))
  0 removeRightAction : transitionAction right = ORemove child
  removeEarlyState : SystemState name key value world error
  removeReplayState : SystemState name key value world error
  removeBindingPresent : Bool
  0 removeBindingObserved : memberKey @{nameEq} child (registry removeEarlyState) = removeBindingPresent
  0 removeBindingAbsent : removeBindingPresent = False
  0 removeEarlyChecked : checkedApplyAction @{nameEq} @{keyEq} (ORemove child) first = Just (ORemoveTag, removeEarlyState)
  0 removeReplayChecked : checkedApplyAction @{nameEq} @{keyEq} (transitionAction left) removeEarlyState = Just (transitionTag left, removeReplayState)
  0 removeReplaySnapshot : runtimeSnapshot finalState = runtimeSnapshot removeReplayState

||| Eliminating one actual post-delete lookup yields a Boolean absence proof.
||| The present branch contradicts Coeffects:320 deletedKeyNotElem, using native
||| lookupJustElem. CP3:4462 has a private lookup law; it is NOT imported here.
export
0 deletedBindingAbsent :
  {key : Type} -> {item : key -> Type} ->
  (keyEq : DecEq key) -> (removed : key) -> (entries : List (Binding key item)) ->
  (0 unique : UniqueKeys (bindingKeys entries)) ->
  (observed : Maybe (item removed)) ->
  (0 exact : lookupEntries @{keyEq} removed (deleteEntries @{keyEq} removed entries) = observed) ->
  isJust observed = False
deletedBindingAbsent keyEq removed entries unique Nothing exact = Refl
deletedBindingAbsent keyEq removed entries unique (Just found) exact =
  void (deletedKeyNotElem @{keyEq} removed entries unique
    (lookupJustElem @{keyEq} removed (deleteEntries @{keyEq} removed entries) found exact))

||| Assemble the new checked Remove square from a single-role CP4 lifecycle
||| deletion replay and the ACTUAL original removal observation. The Boolean
||| absence and both checked alternate edges are derived inside this helper.
export
0 removeSquareFromObservations :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent : name) ->
  (component : Component key value world error) ->
  (table : OwnedTable key value (componentProvisions component)) -> (outcome : Maybe error) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (middle, finalState : SystemState name key value world error) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child fibers =
    Just (MkFiber component (ChildOf parent) True table (Inactive outcome))) ->
  (0 noChild : hasChild {name} {key} {value} {world} {error} @{nameEq} child fibers = False) ->
  (0 distinct : Not (child = actionOwner action)) ->
  (0 valid : registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (MkSystemState ambient fibers) = True) ->
  (0 foreign : checkedApplyAction @{nameEq} @{keyEq} action (MkSystemState ambient fibers) = Just (tag, middle)) ->
  (0 removed : checkedApplyAction @{nameEq} @{keyEq} (ORemove child) middle = Just (ORemoveTag, finalState)) ->
  (replay : LifecycleDeleteRuntimeCommute name key world error value nameEq keyEq action tag child middle
    (MkSystemState ambient (deleteBinding @{nameEq} child fibers))) ->
  (observation : OrchestrationRuntimeObservation name key world error value (worldState middle)
    (deleteBinding @{nameEq} child (registry middle)) finalState) ->
  ChildRemoveSnapshotExchange name key world error value nameEq keyEq child parent
    (Fired {before = MkSystemState ambient fibers} {afterState = middle} nameEq keyEq action tag foreign)
    (Fired {before = middle} {afterState = finalState} nameEq keyEq (ORemove child) ORemoveTag removed)
removeSquareFromObservations nameEq keyEq child parent component table outcome ambient
  (MkCoeffectContext entries unique) action tag middle finalState found noChild distinct valid foreign removed replay observation =
    MkChildRemoveSnapshotExchange (MkFiber component (ChildOf parent) True table (Inactive outcome)) found Refl distinct Refl
      (MkSystemState ambient (deleteBinding @{nameEq} child (MkCoeffectContext entries unique)))
      (lifecycleDeleteReplayAfter replay)
      (memberKey @{nameEq} child (deleteBinding @{nameEq} child (MkCoeffectContext entries unique))) Refl
      (deletedBindingAbsent nameEq child entries unique
        (lookupEntries @{nameEq} child (deleteEntries @{nameEq} child entries)) Refl)
      (checkedFromRaw nameEq keyEq (ORemove child) (MkSystemState ambient (MkCoeffectContext entries unique))
        (MkSystemState ambient (deleteBinding @{nameEq} child (MkCoeffectContext entries unique))) ORemoveTag valid
        (rewrite found in rewrite noChild in Refl))
      (checkedFromRaw nameEq keyEq action
        (MkSystemState ambient (deleteBinding @{nameEq} child (MkCoeffectContext entries unique)))
        (lifecycleDeleteReplayAfter replay) tag
        (registryWellFormedInactiveDelete nameEq keyEq ambient child component (ChildOf parent) True table outcome
          (MkCoeffectContext entries unique) found noChild valid)
        (lifecycleDeleteReplayRaw replay))
      (cong2 MkRuntimeSnapshot
        (trans (orchestrationObservedWorld observation) (lifecycleDeleteWorld replay))
        (trans (orchestrationObservedBindings observation) (lifecycleDeleteBindings replay)))

||| Discharge the original-removal observation from the actual lifecycle edge.
||| Inactive-leaf survival is derived by CP4's local-update theorem. This helper
||| still consumes a single-role raw replay, supplied by the next producers.
export
0 removeSquareFromLifecycleReplay :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent : name) ->
  (component : Component key value world error) ->
  (table : OwnedTable key value (componentProvisions component)) -> (outcome : Maybe error) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (0 lifecycle : isLifecycleAction action = True) ->
  (middle, finalState : SystemState name key value world error) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child fibers =
    Just (MkFiber component (ChildOf parent) True table (Inactive outcome))) ->
  (0 noChild : hasChild {name} {key} {value} {world} {error} @{nameEq} child fibers = False) ->
  (0 distinct : Not (child = actionOwner action)) ->
  (0 valid : registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (MkSystemState ambient fibers) = True) ->
  (0 foreign : checkedApplyAction @{nameEq} @{keyEq} action (MkSystemState ambient fibers) = Just (tag, middle)) ->
  (0 removed : checkedApplyAction @{nameEq} @{keyEq} (ORemove child) middle = Just (ORemoveTag, finalState)) ->
  (replay : LifecycleDeleteRuntimeCommute name key world error value nameEq keyEq action tag child middle
    (MkSystemState ambient (deleteBinding @{nameEq} child fibers))) ->
  ChildRemoveSnapshotExchange name key world error value nameEq keyEq child parent
    (Fired {before = MkSystemState ambient fibers} {afterState = middle} nameEq keyEq action tag foreign)
    (Fired {before = middle} {afterState = finalState} nameEq keyEq (ORemove child) ORemoveTag removed)
removeSquareFromLifecycleReplay nameEq keyEq child parent component table outcome ambient fibers
  action tag lifecycle (MkSystemState middleWorld middleFibers) finalState found noChild distinct valid foreign removed replay =
    removeSquareFromObservations nameEq keyEq child parent component table outcome ambient fibers
      action tag (MkSystemState middleWorld middleFibers) finalState found noChild distinct valid foreign removed replay
      (removeRuntimeObservation nameEq keyEq child middleWorld middleFibers
        (MkFiber component (ChildOf parent) True table (Inactive outcome))
        (survivingInactiveFound
          (inactiveLeafSurvivesLifecycle nameEq keyEq action lifecycle (MkSystemState ambient fibers)
            (MkSystemState middleWorld middleFibers) tag
            (checkedActionProjects nameEq keyEq action (MkSystemState ambient fibers)
              (MkSystemState middleWorld middleFibers) tag foreign)
            child (\same => distinct (sym same)) component (ChildOf parent) True table outcome found noChild))
        (cong not (survivingInactiveChildless
          (inactiveLeafSurvivesLifecycle nameEq keyEq action lifecycle (MkSystemState ambient fibers)
            (MkSystemState middleWorld middleFibers) tag
            (checkedActionProjects nameEq keyEq action (MkSystemState ambient fibers)
              (MkSystemState middleWorld middleFibers) tag foreign)
            child (\same => distinct (sym same)) component (ChildOf parent) True table outcome found noChild)))
        ORemoveTag finalState
        (checkedActionProjects nameEq keyEq (ORemove child) (MkSystemState middleWorld middleFibers)
          finalState ORemoveTag removed))

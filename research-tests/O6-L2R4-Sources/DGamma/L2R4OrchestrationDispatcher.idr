module DGamma.L2R4OrchestrationDispatcher

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.L2R2CheckedSnapshot
import DGamma.L2R3RemoveDispatch
import DGamma.L2R4RetireReplay
import DGamma.L2R4InsertReplay
import Decidable.Equality

%default total
%unbound_implicits off

||| TOTAL ORCHESTRATION-DOMAIN dispatcher by Action, not an all-role single.
||| All three orchestration kinds use original-edge-only native producers;
||| lifecycle constructors contradict the EXPLICIT domain premise. No wildcard
||| forwarder or Either-role adapter. The full ForeignReplay instance is OPEN.
export
0 replayOrchestrationAfterRetirement :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) ->
  (fiber : Fiber name key value world error) ->
  (first, afterState, current : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (0 nonLifecycle : isLifecycleAction action = True -> Void) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} action first = Just (tag, afterState)) ->
  (0 distinct : Not (child = actionOwner action)) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry first) = Just fiber) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} first = True) ->
  (0 currentValid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 currentSame : runtimeSnapshot current = runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState (worldState first) (replaceBinding @{nameEq} child (retireFiber fiber) (registry first)))) ->
  CheckedSnapshotStep name key world error value nameEq keyEq action current tag
    (runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState afterState) (replaceBinding @{nameEq} child (retireFiber fiber) (registry afterState))))
replayOrchestrationAfterRetirement nameEq keyEq child fiber first afterState current (OInsert actor parent component) tag nonLifecycle checked distinct found valid currentValid currentSame =
  replayInsertAfterRetirement nameEq keyEq child actor parent fiber component first afterState current tag checked distinct found valid currentValid currentSame
replayOrchestrationAfterRetirement nameEq keyEq child fiber first afterState current (ORetire actor) tag nonLifecycle checked distinct found valid currentValid currentSame =
  replayRetireAfterRetirement nameEq keyEq child actor fiber first afterState current tag checked distinct found valid currentValid currentSame
replayOrchestrationAfterRetirement nameEq keyEq child fiber first afterState current (ORemove actor) tag nonLifecycle checked distinct found valid currentValid currentSame =
  replayRemoveAfterRetirement nameEq keyEq child actor fiber first afterState current tag checked distinct found valid currentValid currentSame
replayOrchestrationAfterRetirement nameEq keyEq child fiber first afterState current (LBegin actor) tag nonLifecycle checked distinct found valid currentValid currentSame = void (nonLifecycle Refl)
replayOrchestrationAfterRetirement nameEq keyEq child fiber first afterState current (LAdvance actor) tag nonLifecycle checked distinct found valid currentValid currentSame = void (nonLifecycle Refl)
replayOrchestrationAfterRetirement nameEq keyEq child fiber first afterState current (LDivert actor) tag nonLifecycle checked distinct found valid currentValid currentSame = void (nonLifecycle Refl)
replayOrchestrationAfterRetirement nameEq keyEq child fiber first afterState current (LUnload actor) tag nonLifecycle checked distinct found valid currentValid currentSame = void (nonLifecycle Refl)
replayOrchestrationAfterRetirement nameEq keyEq child fiber first afterState current (LLeave actor) tag nonLifecycle checked distinct found valid currentValid currentSame = void (nonLifecycle Refl)

module DGamma.L2R12KindDispatch

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2CheckedSnapshot
import DGamma.L2R4OrchestrationDispatcher
import DGamma.L2R5RetirementFrame
import DGamma.L2R9LifecycleRoles
import DGamma.L2R10LifecycleRoles
import DGamma.L2R11LifecycleSnapshot
import DGamma.L2R11LifecycleDispatch
import DGamma.L2R11WordInventory
import DGamma.L2R12AdvanceDispatch
import Data.Nat
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Kind-vs-tag integration for Begin/Advance/Insert/Retire/Remove. Begin
||| tag is derived from the successful native edge; Advance covers ALL tags.
||| No role/tag assumption and no alternate checked edge remains.
export
0 replayAdmittedRetirementKind : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent : name) ->
  (childFiber : Fiber name key value world error) ->
  (before, afterState, current : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (0 kind : Elem (actionKindCode action) [0, 1, 2, 3, 4]) ->
  (0 original : checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  (0 distinct : Not (child = actionOwner action)) ->
  (0 childFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry before) = Just childFiber) ->
  (0 ownChild : fiberParent childFiber = ChildOf parent) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} before = True) ->
  (0 currentValid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 currentSame : runtimeSnapshot current = runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState (worldState before) (replaceBinding @{nameEq} child (retireFiber childFiber) (registry before)))) ->
  CheckedSnapshotStep name key world error value nameEq keyEq action current tag
    (runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState afterState) (replaceBinding @{nameEq} child (retireFiber childFiber) (registry afterState))))
replayAdmittedRetirementKind nameEq keyEq child parent childFiber before afterState current
  (OInsert selected birthParent component) tag kind original distinct childFound ownChild valid currentValid currentSame =
  replayAdmittedRetirementRole nameEq keyEq child parent childFiber before afterState current
    (OInsert selected birthParent component) tag (Left absurd) original distinct childFound ownChild valid currentValid currentSame
replayAdmittedRetirementKind nameEq keyEq child parent childFiber before afterState current
  (ORetire selected) tag kind original distinct childFound ownChild valid currentValid currentSame =
  replayAdmittedRetirementRole nameEq keyEq child parent childFiber before afterState current
    (ORetire selected) tag (Left absurd) original distinct childFound ownChild valid currentValid currentSame
replayAdmittedRetirementKind nameEq keyEq child parent childFiber before afterState current
  (ORemove selected) tag kind original distinct childFound ownChild valid currentValid currentSame =
  replayAdmittedRetirementRole nameEq keyEq child parent childFiber before afterState current
    (ORemove selected) tag (Left absurd) original distinct childFound ownChild valid currentValid currentSame
replayAdmittedRetirementKind {name} {key} {world} {error} {value}
  nameEq keyEq child parent childFiber before afterState current
  (LBegin actor) tag kind original distinct childFound ownChild valid currentValid currentSame =
  replayAdmittedRetirementRole nameEq keyEq child parent childFiber before afterState current
    (LBegin actor) tag
    (Right (replace {p = \seen => Elem (the (Action name key value world error) (LBegin actor), seen)
      [(LBegin actor, LBeginTag), (LAdvance actor, LIterTag), (LAdvance actor, LFinishTag)]}
      (sym (fst (lBeginBoundary {name} {key} {world} {error} {value} nameEq keyEq actor before afterState tag original))) Here))
    original distinct childFound ownChild valid currentValid currentSame
replayAdmittedRetirementKind {name} {key} {world} {error} {value}
  nameEq keyEq child parent childFiber before afterState current
  (LAdvance actor) tag kind original distinct childFound ownChild valid currentValid currentSame =
  replayAdvanceAtLookup nameEq keyEq child parent actor childFiber before afterState current tag
    original distinct childFound ownChild
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before)) Refl
    valid currentValid currentSame
replayAdmittedRetirementKind nameEq keyEq child parent childFiber before afterState current
  (LDivert actor) tag kind original distinct childFound ownChild valid currentValid currentSame = absurd kind
replayAdmittedRetirementKind nameEq keyEq child parent childFiber before afterState current
  (LLeave actor) tag kind original distinct childFound ownChild valid currentValid currentSame = absurd kind
replayAdmittedRetirementKind nameEq keyEq child parent childFiber before afterState current
  (LUnload actor) tag kind original distinct childFound ownChild valid currentValid currentSame = absurd kind

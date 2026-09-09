module DGamma.L2R11LifecycleDispatch

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
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Observe the source actor lookup ONCE. Its absent branch is contradicted
||| by the original successful role; its present branch produces the actual
||| frame and arbitrary-source replay. No installed-actor oracle is needed.
export
0 replayLifecycleAtLookup : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber : Fiber name key value world error) ->
  (before, afterState, current : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (0 role : Elem (action, tag) [(LBegin actor, LBeginTag), (LAdvance actor, LIterTag), (LAdvance actor, LFinishTag)]) ->
  (0 original : checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  (0 distinct : Not (child = actor)) ->
  (0 childFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry before) = Just childFiber) ->
  (0 ownChild : fiberParent childFiber = ChildOf parent) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (0 actorEquation : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before) = observed) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} before = True) ->
  (0 currentValid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 currentSame : runtimeSnapshot current = runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState (worldState before) (replaceBinding @{nameEq} child (retireFiber childFiber) (registry before)))) ->
  CheckedSnapshotStep name key world error value nameEq keyEq action current tag
    (runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState afterState) (replaceBinding @{nameEq} child (retireFiber childFiber) (registry afterState))))
replayLifecycleAtLookup nameEq keyEq child parent actor childFiber before afterState current
  action tag role original distinct childFound ownChild Nothing actorEquation valid currentValid currentSame =
  absurd (lifecycleRoleMissing nameEq keyEq actor before afterState action tag role actorEquation original)
replayLifecycleAtLookup nameEq keyEq child parent actor childFiber before afterState current
  action tag role original distinct childFound ownChild (Just actorFiber) actorEquation valid currentValid currentSame =
  replayLifecycleAtFound nameEq keyEq child parent actor childFiber actorFiber before afterState current
    action tag role original distinct childFound ownChild actorEquation valid currentValid currentSame

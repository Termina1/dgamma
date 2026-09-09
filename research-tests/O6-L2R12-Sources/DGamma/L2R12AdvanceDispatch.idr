module DGamma.L2R12AdvanceDispatch

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
import DGamma.L2R10AdvanceReplay
import DGamma.L2R11LifecycleSnapshot
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| All-tag Advance replay at arbitrary snapshot-equal sources. The actual
||| RetirementProviderFrame is PRODUCED from original source metadata.
export
0 replayAdvanceAtFound : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber, actorFiber : Fiber name key value world error) ->
  (before, afterState, current : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (0 original : checkedApplyAction @{nameEq} @{keyEq} (LAdvance actor) before = Just (tag, afterState)) ->
  (0 distinct : Not (child = actor)) ->
  (0 childFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry before) = Just childFiber) ->
  (0 ownChild : fiberParent childFiber = ChildOf parent) ->
  (0 actorFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before) = Just actorFiber) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} before = True) ->
  (0 currentValid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 currentSame : runtimeSnapshot current = runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState (worldState before) (replaceBinding @{nameEq} child (retireFiber childFiber) (registry before)))) ->
  CheckedSnapshotStep name key world error value nameEq keyEq (LAdvance actor) current tag
    (runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState afterState) (replaceBinding @{nameEq} child (retireFiber childFiber) (registry afterState))))
replayAdvanceAtFound nameEq keyEq child parent actor childFiber actorFiber before afterState current
  tag original distinct childFound ownChild actorFound valid currentValid currentSame =
  snapshotStepAtSame nameEq keyEq (LAdvance actor) tag
    (MkSystemState (worldState before) (replaceBinding @{nameEq} child (retireFiber childFiber) (registry before))) current
    (runtimeSnapshot (MkSystemState (worldState afterState)
      (replaceBinding @{nameEq} child (retireFiber childFiber) (registry afterState)))) currentSame currentValid
    (replayRetirementAdvance nameEq keyEq child parent actor childFiber actorFiber before afterState tag
      (retirementProviderFrame nameEq keyEq child parent actor childFiber actorFiber (registry before) childFound ownChild actorFound)
      distinct valid original)


||| ANY successful original Advance tag has an actual source actor.
||| Missing lookup is observed with its own equation, then contradicts the
||| original native edge. No finite Iter/Finish tag assumption is made.
export
0 advanceMissingImpossible : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (0 missing : lookupFiber {name} {key} {value} {world} {error} @{nameEq}
    actor (registry before) = Nothing) ->
  (0 original : checkedApplyAction @{nameEq} @{keyEq} (LAdvance actor) before = Just (tag, afterState)) -> Void
advanceMissingImpossible nameEq keyEq actor before afterState tag missing original =
  absurd (replace {p = \observed => observed = Just (tag, afterState)}
    (the (applyAction @{nameEq} @{keyEq} (LAdvance actor) before = Nothing) (rewrite missing in Refl))
    (checkedActionProjects nameEq keyEq (LAdvance actor) before afterState tag original))

||| Observe the actual source actor once and produce all-tag replay.
export
0 replayAdvanceAtLookup : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber : Fiber name key value world error) ->
  (before, afterState, current : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (0 original : checkedApplyAction @{nameEq} @{keyEq} (LAdvance actor) before = Just (tag, afterState)) ->
  (0 distinct : Not (child = actor)) ->
  (0 childFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry before) = Just childFiber) ->
  (0 ownChild : fiberParent childFiber = ChildOf parent) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (0 actorEquation : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before) = observed) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} before = True) ->
  (0 currentValid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 currentSame : runtimeSnapshot current = runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState (worldState before) (replaceBinding @{nameEq} child (retireFiber childFiber) (registry before)))) ->
  CheckedSnapshotStep name key world error value nameEq keyEq (LAdvance actor) current tag
    (runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState afterState) (replaceBinding @{nameEq} child (retireFiber childFiber) (registry afterState))))
replayAdvanceAtLookup nameEq keyEq child parent actor childFiber before afterState current
  tag original distinct childFound ownChild Nothing actorEquation valid currentValid currentSame =
  absurd (advanceMissingImpossible nameEq keyEq actor before afterState tag actorEquation original)
replayAdvanceAtLookup nameEq keyEq child parent actor childFiber before afterState current
  tag original distinct childFound ownChild (Just actorFiber) actorEquation valid currentValid currentSame =
  replayAdvanceAtFound nameEq keyEq child parent actor childFiber actorFiber before afterState current
    tag original distinct childFound ownChild actorEquation valid currentValid currentSame

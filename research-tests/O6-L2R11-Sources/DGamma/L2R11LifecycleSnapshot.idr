module DGamma.L2R11LifecycleSnapshot

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
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Transport an already PRODUCED checked snapshot packet, preserving its
||| expected endpoint, to any well-formed snapshot-equal current source.
export
0 snapshotStepAtSame : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (source, current : SystemState name key value world error) ->
  (expected : RuntimeSnapshot name key world error value) ->
  (0 same : runtimeSnapshot current = runtimeSnapshot source) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  CheckedSnapshotStep name key world error value nameEq keyEq action source tag expected ->
  CheckedSnapshotStep name key world error value nameEq keyEq action current tag expected
snapshotStepAtSame nameEq keyEq action tag source current expected same valid
  (MkCheckedSnapshotStep afterState checked exact) =
  replace {p = \target => CheckedSnapshotStep name key world error value nameEq keyEq action current tag target}
    exact (checkedAcrossSnapshot nameEq keyEq action tag source afterState current checked (sym same) valid)

||| The retained exact Begin/Iter/Finish producer now works at arbitrary
||| snapshot-equal current sources. Its frame is PRODUCED from native lookup
||| and parent facts; unchanged targets/views and alternate edges are not inputs.
export
0 replayLifecycleAtFound : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber, actorFiber : Fiber name key value world error) ->
  (before, afterState, current : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (0 role : Elem (action, tag) [(LBegin actor, LBeginTag), (LAdvance actor, LIterTag), (LAdvance actor, LFinishTag)]) ->
  (0 original : checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  (0 distinct : Not (child = actor)) ->
  (0 childFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry before) = Just childFiber) ->
  (0 ownChild : fiberParent childFiber = ChildOf parent) ->
  (0 actorFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before) = Just actorFiber) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} before = True) ->
  (0 currentValid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 currentSame : runtimeSnapshot current = runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState (worldState before) (replaceBinding @{nameEq} child (retireFiber childFiber) (registry before)))) ->
  CheckedSnapshotStep name key world error value nameEq keyEq action current tag
    (runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState afterState) (replaceBinding @{nameEq} child (retireFiber childFiber) (registry afterState))))
replayLifecycleAtFound nameEq keyEq child parent actor childFiber actorFiber before afterState current
  action tag role original distinct childFound ownChild actorFound valid currentValid currentSame =
  snapshotStepAtSame nameEq keyEq action tag
    (MkSystemState (worldState before) (replaceBinding @{nameEq} child (retireFiber childFiber) (registry before))) current
    (runtimeSnapshot (MkSystemState (worldState afterState)
      (replaceBinding @{nameEq} child (retireFiber childFiber) (registry afterState)))) currentSame currentValid
    (replayRetirementLifecycle nameEq keyEq child parent actor childFiber actorFiber before action tag role
      (retirementProviderFrame nameEq keyEq child parent actor childFiber actorFiber (registry before) childFound ownChild actorFound)
      distinct valid afterState original)

||| A successful original lifecycle role cannot have a missing actor. This
||| eliminates the finite role witness, never a native computed lookup twice.
export
0 lifecycleRoleMissing : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (0 role : Elem (action, tag) [(LBegin actor, LBeginTag), (LAdvance actor, LIterTag), (LAdvance actor, LFinishTag)]) ->
  (0 missing : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before) = Nothing) ->
  (0 original : checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) -> Void
lifecycleRoleMissing nameEq keyEq actor before afterState _ _ Here missing original =
  absurd (replace {p = \observed => observed = Just (LBeginTag, afterState)}
    (the (applyAction @{nameEq} @{keyEq} (LBegin actor) before = Nothing) (rewrite missing in Refl))
    (checkedActionProjects nameEq keyEq (LBegin actor) before afterState LBeginTag original))
lifecycleRoleMissing nameEq keyEq actor before afterState _ _ (There Here) missing original =
  absurd (replace {p = \observed => observed = Just (LIterTag, afterState)}
    (the (applyAction @{nameEq} @{keyEq} (LAdvance actor) before = Nothing) (rewrite missing in Refl))
    (checkedActionProjects nameEq keyEq (LAdvance actor) before afterState LIterTag original))
lifecycleRoleMissing nameEq keyEq actor before afterState _ _ (There (There Here)) missing original =
  absurd (replace {p = \observed => observed = Just (LFinishTag, afterState)}
    (the (applyAction @{nameEq} @{keyEq} (LAdvance actor) before = Nothing) (rewrite missing in Refl))
    (checkedActionProjects nameEq keyEq (LAdvance actor) before afterState LFinishTag original))
lifecycleRoleMissing nameEq keyEq actor before afterState action tag
  (There (There (There impossibleRole))) missing original = absurd impossibleRole

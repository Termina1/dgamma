module DGamma.L2R9LifecycleRoles

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2CheckedSnapshot
import DGamma.L2R5RetirementFrame
import DGamma.L2R9ResolverRetirement
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| PRECISE original-edge-only three-role contract. TYPE ONLY until its
||| producer checks. The finite membership restricts exactly LBegin/LIter/
||| LFinish; an authentic RetirementProviderFrame and current-cut validity
||| are inputs, NOT unchanged views, a late checked edge, or a replay oracle.
||| Output MUST contain the alternate native checked edge AND the exact
||| world/ordered-binding snapshot after retiring the same installed child.
||| This canonical early-retirement source still needs full-single snapshot
||| transport before feeding L2R2's whole ForeignReplay on R191.
public export
NativeLifecycleRetirementRole :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber, actorFiber : Fiber name key value world error) ->
  (before : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) -> Type
NativeLifecycleRetirementRole {name} {key} {world} {error} {value} nameEq keyEq child parent actor childFiber actorFiber before action tag =
  (0 role : Elem (action, tag) [(LBegin actor, LBeginTag), (LAdvance actor, LIterTag), (LAdvance actor, LFinishTag)]) ->
  (frame : RetirementProviderFrame name key world error value nameEq keyEq child parent actor childFiber actorFiber (registry before)) ->
  (0 distinct : Not (child = actor)) ->
  (0 valid : registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} before = True) ->
  (afterState : SystemState name key value world error) ->
  (0 original : checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  CheckedSnapshotStep name key world error value nameEq keyEq action
    (MkSystemState (worldState before) (replaceBinding @{nameEq} child (retireFiber childFiber) (registry before))) tag
    (runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState afterState) (replaceBinding @{nameEq} child (retireFiber childFiber) (registry afterState))))

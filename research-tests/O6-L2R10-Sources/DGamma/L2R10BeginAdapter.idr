module DGamma.L2R10BeginAdapter

import Prelude.Types
import Prelude.Interfaces
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4DeletionSelectedForeignLifecycleBegin
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2CheckedSnapshot
import DGamma.L2R4RetireReplay
import DGamma.L2R5RetirementFrame
import DGamma.L2R9ResolverRetirement
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Original ForeignBeginPlanView adapter. The view exposes the actual clean
||| owner before transporting the native resolver; replacement commutation
||| gives the exact retired-child endpoint snapshot, not an assumed late edge.
export
0 retirementBeginPlanAdapter :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber, actorFiber : Fiber name key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (frame : RetirementProviderFrame name key world error value nameEq keyEq child parent actor childFiber actorFiber source) ->
  (0 distinct : Not (child = actor)) ->
  ForeignBeginPlanView name key world error value nameEq keyEq actor ambient source actorFiber tag afterState ->
  observeActionResult {name} {key} {world} {error} {value}
    (beginFiberAction @{nameEq} @{keyEq} actor actorFiber
      (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber childFiber) source))) =
  Just (tag, runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState (worldState afterState)
      (replaceBinding @{nameEq} child (retireFiber childFiber) (registry afterState))))
retirementBeginPlanAdapter {name} {key} {world} {error} {value}
  nameEq keyEq child parent actor childFiber actorFiber ambient source afterState tag frame distinct
  (MkForeignBeginPlanView {component} {parent = ownerParent} {table}
    view ownerShape targetFound tagShape afterShape) =
  rewrite ownerShape in
  rewrite sym afterShape in
  rewrite tagShape in
  rewrite sym (replace
    {p = \owner => resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
      (dependencies (componentDependencies (fiberComponent owner))) source =
      resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
      (dependencies (componentDependencies (fiberComponent owner)))
      (replaceBinding @{nameEq} child (retireFiber childFiber) source)}
    ownerShape
    (fst (retirementFrameResolverSame nameEq keyEq child parent actor childFiber actorFiber source frame))) in
  rewrite targetFound in
  cong (\snapshot => Just (LBeginTag, snapshot))
    (retirementUpdateSnapshot nameEq child actor childFiber
      (MkFiber component ownerParent False table
        (Reloading (componentProgram component) (\local => local) view)) ambient source distinct)

||| LBegin ORIGINAL-EDGE-ONLY replay role. Adapter B1 crosses the exposed
||| native owner boundary; raw Preservation checks the alternate successor.
export
0 replayRetirementBegin :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber, actorFiber : Fiber name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (frame : RetirementProviderFrame name key world error value nameEq keyEq child parent actor childFiber actorFiber (registry before)) ->
  (0 distinct : Not (child = actor)) ->
  (0 valid : registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} before = True) ->
  (0 original : checkedApplyAction @{nameEq} @{keyEq} (LBegin actor) before = Just (LBeginTag, afterState)) ->
  CheckedSnapshotStep name key world error value nameEq keyEq (LBegin actor)
    (MkSystemState (worldState before) (replaceBinding @{nameEq} child (retireFiber childFiber) (registry before))) LBeginTag
    (runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState afterState) (replaceBinding @{nameEq} child (retireFiber childFiber) (registry afterState))))
replayRetirementBegin {name} {key} {world} {error} {value}
  nameEq keyEq child parent actor childFiber actorFiber (MkSystemState ambient source) afterState frame distinct valid original =
  checkedSnapshotObserved nameEq keyEq (LBegin actor)
    (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber childFiber) source)) LBeginTag
    (runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState afterState) (replaceBinding @{nameEq} child (retireFiber childFiber) (registry afterState))))
    (applyAction @{nameEq} @{keyEq} (LBegin actor)
      (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber childFiber) source))) Refl
    (rewrite lookupReplaceOther {key = name} {value = FiberAt name key value world error} @{nameEq}
       actor child (\same => distinct (sym same)) (retireFiber childFiber) source in
     rewrite frameActorFound frame in
     retirementBeginPlanAdapter nameEq keyEq child parent actor childFiber actorFiber ambient source afterState LBeginTag frame distinct
       (foreignBeginPlanView nameEq keyEq actor ambient source actorFiber (frameActorFound frame) LBeginTag afterState
         (checkedActionProjects nameEq keyEq (LBegin actor) (MkSystemState ambient source) afterState LBeginTag original)))
    (registryWellFormedRetire nameEq keyEq ambient child childFiber source (frameChildFound frame) valid)

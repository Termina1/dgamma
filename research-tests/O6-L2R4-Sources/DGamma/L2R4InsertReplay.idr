module DGamma.L2R4InsertReplay

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4DeletionCommuteCore
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2CheckedSnapshot
import DGamma.L2R2RetireInsert
import Decidable.Equality
import Data.List.Elem

%default total
%unbound_implicits off

||| General-parent counterpart of L2R2 rootInsertAtAbsence, retaining the
||| FULL native parent-present AND declared-provision guard. Ordered snapshot
||| observation only; not equality of independently reconstructed certificates.
export
0 insertAtNativeGuards :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) -> (parent : Parent name) ->
  (component : Component key value world error) -> (ambient : world) ->
  (source : Registry name key value world error) ->
  (0 absent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor source = Nothing) ->
  (0 guards : parentPresent {name} {key} {value} {world} {error} @{nameEq} parent source &&
    provisionsDisjointFrom {name} {key} {value} {world} {error} @{keyEq}
      (componentProvisions component) (bindings source) = True) ->
  observeActionResult (applyAction @{nameEq} @{keyEq} (OInsert actor parent component) (MkSystemState ambient source)) =
    Just (OInsertTag, MkRuntimeSnapshot ambient (Bind actor (freshFiber component parent) :: bindings source))
insertAtNativeGuards nameEq keyEq actor parent component ambient (MkCoeffectContext entries unique) absent guards =
  rewrite guards in rewrite absent in Refl

||| General-parent counterpart of checkedRootInsert. The observed native
||| evaluator produces its own successor and checked Preservation certificate.
export
0 checkedInsertAtNativeGuards :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) -> (parent : Parent name) ->
  (component : Component key value world error) -> (ambient : world) ->
  (source : Registry name key value world error) ->
  (0 absent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor source = Nothing) ->
  (0 guards : parentPresent {name} {key} {value} {world} {error} @{nameEq} parent source &&
    provisionsDisjointFrom {name} {key} {value} {world} {error} @{keyEq}
      (componentProvisions component) (bindings source) = True) ->
  (0 valid : registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (MkSystemState ambient source) = True) ->
  CheckedSnapshotStep name key world error value nameEq keyEq (OInsert actor parent component)
    (MkSystemState ambient source) OInsertTag
    (MkRuntimeSnapshot ambient (Bind actor (freshFiber component parent) :: bindings source))
checkedInsertAtNativeGuards nameEq keyEq actor parent component ambient source absent guards valid =
  checkedSnapshotObserved nameEq keyEq (OInsert actor parent component) (MkSystemState ambient source)
    OInsertTag (MkRuntimeSnapshot ambient (Bind actor (freshFiber component parent) :: bindings source))
    (applyAction @{nameEq} @{keyEq} (OInsert actor parent component) (MkSystemState ambient source)) Refl
    (insertAtNativeGuards nameEq keyEq actor parent component ambient source absent guards) valid

||| General-parent counterpart of retireInsertedSnapshot: early retirement
||| cannot alter a distinct freshly inserted head in the ordered runtime list.
export
0 retireAnyInsertedSnapshot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (child, actor : name) -> (parent : Parent name) ->
  (fiber : Fiber name key value world error) ->
  (component : Component key value world error) -> (ambient : world) ->
  (source : Registry name key value world error) ->
  (0 absent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor source = Nothing) ->
  (0 distinct : Not (child = actor)) ->
  runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber fiber)
      (insertBinding @{nameEq} actor (freshFiber component parent) source absent))) =
  MkRuntimeSnapshot ambient (Bind actor (freshFiber component parent) ::
    bindings (replaceBinding @{nameEq} child (retireFiber fiber) source))
retireAnyInsertedSnapshot nameEq child actor parent fiber component ambient (MkCoeffectContext entries unique) absent distinct =
  cong (MkRuntimeSnapshot ambient)
    (replaceOtherHeadObserved nameEq child actor (retireFiber fiber) (freshFiber component parent)
      entries (decEq @{nameEq} child actor) Refl distinct)

||| Transport a PRODUCED native insertion replay to an arbitrary snapshot-
||| equal well-formed retired source, retaining the observed original insertion
||| endpoint. Helper for one action role; not a supplied suffix oracle.
export
0 replayInsertObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, actor : name) -> (parent : Parent name) ->
  (fiber : Fiber name key value world error) -> (component : Component key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (current : SystemState name key value world error) ->
  (0 absent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor source = Nothing) ->
  (0 distinct : Not (child = actor)) ->
  (0 currentValid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 currentSame : runtimeSnapshot current = runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber fiber) source))) ->
  CheckedSnapshotStep name key world error value nameEq keyEq (OInsert actor parent component)
    (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber fiber) source)) OInsertTag
    (MkRuntimeSnapshot ambient (Bind actor (freshFiber component parent) :: bindings (replaceBinding @{nameEq} child (retireFiber fiber) source))) ->
  CheckedSnapshotStep name key world error value nameEq keyEq (OInsert actor parent component) current OInsertTag
    (runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber fiber)
        (insertBinding @{nameEq} actor (freshFiber component parent) source absent))))
replayInsertObserved nameEq keyEq child actor parent fiber component ambient source current absent distinct currentValid currentSame replay =
  replace {p = \expected => CheckedSnapshotStep name key world error value nameEq keyEq (OInsert actor parent component) current OInsertTag expected}
    (trans (snapshotExact replay) (sym (retireAnyInsertedSnapshot nameEq child actor parent fiber component ambient source absent distinct)))
    (checkedAcrossSnapshot nameEq keyEq (OInsert actor parent component) OInsertTag
      (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber fiber) source))
      (snapshotAfter replay) current (snapshotChecked replay) (sym currentSame) currentValid)

||| Eliminate the original single-constructor insertion view. Native parent
||| presence and declared-provision guards survive retirement; B9 PRODUCES
||| the alternate checked insertion. Root and child-parent cases are uniform.
export
0 replayInsertFromView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, actor : name) -> (parent : Parent name) ->
  (fiber : Fiber name key value world error) -> (component : Component key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (afterState, current : SystemState name key value world error) -> (tag : RuleTag) ->
  (0 distinct : Not (child = actor)) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child source = Just fiber) ->
  (0 valid : registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (MkSystemState ambient source) = True) ->
  (0 currentValid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 currentSame : runtimeSnapshot current = runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber fiber) source))) ->
  ForeignInsertPlanView name key world error value nameEq keyEq actor parent component ambient source tag afterState ->
  CheckedSnapshotStep name key world error value nameEq keyEq (OInsert actor parent component) current tag
    (runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState afterState) (replaceBinding @{nameEq} child (retireFiber fiber) (registry afterState))))
replayInsertFromView nameEq keyEq child actor parent fiber component ambient source _ current _
  distinct found valid currentValid currentSame (MkForeignInsertPlanView absent guards) =
    replayInsertObserved nameEq keyEq child actor parent fiber component ambient source current absent distinct currentValid currentSame
      (checkedInsertAtNativeGuards nameEq keyEq actor parent component ambient
        (replaceBinding @{nameEq} child (retireFiber fiber) source)
        (trans (lookupReplaceOther @{nameEq} actor child (\same => distinct (sym same)) (retireFiber fiber) source) absent)
        (trans (boolAndCong
          (trans (parentPresentIsInvariant nameEq parent (replaceBinding @{nameEq} child (retireFiber fiber) source))
            (trans (parentInvariantRetireRegistry nameEq parent child fiber source found)
              (sym (parentPresentIsInvariant nameEq parent source))))
          (trans (cong (provisionsDisjointFrom {name} {key} {value} {world} {error} @{keyEq} (componentProvisions component))
            (replaceBindingRuntimeBindings nameEq child (retireFiber fiber) source))
            (provisionsDisjointRetireEntries nameEq keyEq (componentProvisions component) (bindings source)
              child fiber (lookupFiberEntries nameEq child fiber source found)))) guards)
        (registryWellFormedRetire nameEq keyEq ambient child fiber source found valid))

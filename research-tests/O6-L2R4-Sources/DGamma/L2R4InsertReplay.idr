module DGamma.L2R4InsertReplay

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
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

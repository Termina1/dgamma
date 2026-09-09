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

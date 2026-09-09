module DGamma.L2R11ClassifierSquare

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2CheckedSnapshot
import DGamma.L2R4InsertReplay
import DGamma.L2R5Extensional
import DGamma.L2R5CurrentCut
import DGamma.L2R6Iteration
import DGamma.L2R9ControlClass
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| A genuine local early-root crossing square with extensional endpoint.
||| This is NOT an AdmittedDistanceMove: physical whole-word adjacency,
||| forcing, phase/NeverRetired/uniqueness transport and decrement are separate.
public export
record ClassifierSquare
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (root : name) (component : Component key value world error)
  (source : SystemState name key value world error)
  (action : Action name key value world error) (tag : RuleTag)
  (oldFinal : SystemState name key value world error) where
  constructor MkClassifierSquare
  squareMiddle : SystemState name key value world error
  squareFinal : SystemState name key value world error
  0 earlyChecked : checkedApplyAction @{nameEq} @{keyEq} (OInsert root Root component) source = Just (OInsertTag, squareMiddle)
  0 laterChecked : checkedApplyAction @{nameEq} @{keyEq} action squareMiddle = Just (tag, squareFinal)
  0 squareAdmitted : AdmittedCrossing nameEq root source action
  0 squareCurrentCut : rootDeclaredProvisionsFree name key world error value keyEq component source = True
  0 squareEndpoint : RegistryExtensional name key world error value nameEq oldFinal squareFinal

||| Match a produced checked snapshot packet against a known native edge
||| at the SAME source/action/tag. Only the packet is eliminated.
export
0 snapshotPacketMatches : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (source, target : SystemState name key value world error) ->
  (expected : RuntimeSnapshot name key world error value) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} action source = Just (tag, target)) ->
  CheckedSnapshotStep name key world error value nameEq keyEq action source tag expected ->
  runtimeSnapshot target = expected
snapshotPacketMatches nameEq keyEq action tag source target expected checked
  (MkCheckedSnapshotStep afterState produced exact) =
  trans (cong runtimeSnapshot (cong snd (justInjective (trans (sym checked) produced)))) exact

||| Recover the canonical retirement snapshot from the original checked
||| Retire edge and its native installed fiber, not a supplied state equality.
export
0 originalRetireSnapshot : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) ->
  (fiber : Fiber name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry before) = Just fiber) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} before = True) ->
  (0 original : checkedApplyAction @{nameEq} @{keyEq} (ORetire child) before = Just (ORetireTag, afterState)) ->
  runtimeSnapshot afterState = runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState (worldState before) (replaceBinding @{nameEq} child (retireFiber fiber) (registry before)))
originalRetireSnapshot nameEq keyEq child fiber before afterState found valid original =
  cong runtimeSnapshot (cong snd (justInjective (trans (sym original)
    (childRetireAtFound nameEq keyEq child fiber before found valid))))

module DGamma.L2R9OrdinalScan

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3Attached
import DGamma.L2R8SharedKey
import DGamma.L2R8ReleaseScan
import Data.List
import Data.List.Elem
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Runtime head ordinal observation over the SAME isElem overlap as L2R8.
||| The Bool is eliminated before any consumer constructs guard-indexed data.
public export
overlapOrdinals : {key : Type} -> (keyEq : DecEq key) ->
  (left, right : List key) -> (seen : Bool) ->
  (0 equation : any (\item => isYes (isElem @{keyEq} item right)) left = seen) -> List Nat
overlapOrdinals keyEq left right True equation = [0]
overlapOrdinals keyEq left right False equation = []

||| A release may only be an own-child removal. The overlap Bool belongs to
||| the actual isElem scan at this call site, not a recased library decider.
public export
ordinalAtParent : {name, key, world, error : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) -> (component : Component key value world error) ->
  (fiber : Fiber name key value world error) -> (parent : Parent name) ->
  (0 equation : fiberParent fiber = parent) -> List Nat
ordinalAtParent keyEq component fiber Root equation = []
ordinalAtParent keyEq component fiber (ChildOf actor) equation =
  overlapOrdinals keyEq
    (dependencies (componentProvisions (fiberComponent fiber)))
    (dependencies (componentProvisions component))
    (any (\item => isYes (isElem @{keyEq} item (dependencies (componentProvisions component))))
      (dependencies (componentProvisions (fiberComponent fiber)))) Refl

||| Observe the fully indexed source lookup once. Absent fibers emit nothing.
public export
ordinalAtLookup : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (component : Component key value world error) -> (child : name) ->
  (source : SystemState name key value world error) ->
  (found : Maybe (Fiber name key value world error)) ->
  (0 equation : lookupFiber {name} {key} {value} {world} {error} @{nameEq}
    child (registry source) = found) -> List Nat
ordinalAtLookup nameEq keyEq component child source Nothing equation = []
ordinalAtLookup nameEq keyEq component child source (Just fiber) equation =
  ordinalAtParent keyEq component fiber (fiberParent fiber) Refl

||| Only the actual native ORemove action can emit a release ordinal.
public export
ordinalAtAction : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (component : Component key value world error) ->
  (source : SystemState name key value world error) ->
  Action name key value world error -> List Nat
ordinalAtAction nameEq keyEq component source (OInsert child parent inserted) = []
ordinalAtAction nameEq keyEq component source (ORetire child) = []
ordinalAtAction {name} {key} {world} {error} {value} nameEq keyEq component source (ORemove child) =
  ordinalAtLookup nameEq keyEq component child source
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry source)) Refl
ordinalAtAction nameEq keyEq component source (LBegin actor) = []
ordinalAtAction nameEq keyEq component source (LAdvance actor) = []
ordinalAtAction nameEq keyEq component source (LDivert actor) = []
ordinalAtAction nameEq keyEq component source (LUnload actor) = []
ordinalAtAction nameEq keyEq component source (LLeave actor) = []

||| Unrestricted executable release ORDINAL scan. The source/action come
||| from the native availability trail. Relative ordinals are shifted through
||| each head. This is a NEW omega definition, not the erased L2R8 scan.
||| Agreement with the old Bool scan and phase production are separate debt.
public export
releaseOrdinalScan : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (component : Component key value world error) ->
  DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace -> List Nat
releaseOrdinalScan nameEq keyEq component (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd state) = []
releaseOrdinalScan nameEq keyEq component (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep source (Fired ne ke action tag checked) rest later) =
  ordinalAtAction nameEq keyEq component source action ++
  map S (releaseOrdinalScan nameEq keyEq component later)

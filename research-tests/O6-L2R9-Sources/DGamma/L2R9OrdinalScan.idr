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

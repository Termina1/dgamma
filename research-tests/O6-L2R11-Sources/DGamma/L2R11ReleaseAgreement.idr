module DGamma.L2R11ReleaseAgreement

import Prelude.Types
import Prelude.Interfaces
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3Attached
import DGamma.L2R6ForcedScan
import DGamma.L2R8ReleaseScan
import DGamma.L2R9OrdinalScan
import DGamma.L2R9OrdinalLink
import DGamma.L2R10ReleaseAgreement
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core
import Decidable.Decidable

%default total
%unbound_implicits off

||| Whole declaration-list overlap agreement with the library's actual
||| foldl accumulator. Native decisions remain owned by releaseScanAgrees.
||| any is foldl, NOT the right-recursive Boolean fold.
export
0 releaseOverlapAgrees : {key : Type} -> (keyEq : DecEq key) ->
  (left, right : List key) -> (accumulator : Bool) ->
  foldl (\acc, item => acc || isYes (isElem @{keyEq} item right)) accumulator left =
  foldl (\acc, item => acc || elemDec @{keyEq} item right) accumulator left
releaseOverlapAgrees keyEq [] right accumulator = Refl
releaseOverlapAgrees keyEq (head :: tail) right accumulator =
  rewrite releaseScanAgrees keyEq head right in
  releaseOverlapAgrees keyEq tail right (accumulator || elemDec @{keyEq} head right)

||| Eliminate the observed library overlap before constructing its ordinal
||| list. Agreement covers ALL declared keys, including duplicate keys.
export
0 overlapOrdinalsAgrees : {key : Type} -> (keyEq : DecEq key) ->
  (left, right : List key) -> (seen : Bool) ->
  (0 equation : any (\item => isYes (isElem @{keyEq} item right)) left = seen) ->
  overlapOrdinals keyEq left right seen equation =
    (if any (\item => elemDec @{keyEq} item right) left then [0] else [])
overlapOrdinalsAgrees keyEq left right True equation =
  rewrite trans (sym (releaseOverlapAgrees keyEq left right False)) equation in Refl
overlapOrdinalsAgrees keyEq left right False equation =
  rewrite trans (sym (releaseOverlapAgrees keyEq left right False)) equation in Refl

||| Parent-level agreement: root controls cannot emit a release ordinal.
export
0 parentOrdinalsAgrees : {name, key, world, error : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) -> (component : Component key value world error) ->
  (fiber : Fiber name key value world error) -> (parent : Parent name) ->
  (0 equation : fiberParent fiber = parent) ->
  ordinalAtParent keyEq component fiber parent equation =
    (if childDeclaredOverlap keyEq component parent (fiberComponent fiber) then [0] else [])
parentOrdinalsAgrees keyEq component fiber Root equation = Refl
parentOrdinalsAgrees keyEq component fiber (ChildOf actor) equation =
  overlapOrdinalsAgrees keyEq
    (dependencies (componentProvisions (fiberComponent fiber)))
    (dependencies (componentProvisions component))
    (any (\item => isYes (isElem @{keyEq} item (dependencies (componentProvisions component))))
      (dependencies (componentProvisions (fiberComponent fiber)))) Refl

||| Observe the actual fully indexed source lookup; no installed fiber
||| assumption is required in the absent branch.
export
0 lookupOrdinalsAgrees : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (component : Component key value world error) -> (child : name) ->
  (source : SystemState name key value world error) ->
  (found : Maybe (Fiber name key value world error)) ->
  (0 equation : lookupFiber {name} {key} {value} {world} {error} @{nameEq}
    child (registry source) = found) ->
  ordinalAtLookup nameEq keyEq component child source found equation =
    (if foundChildOverlap keyEq component found then [0] else [])
lookupOrdinalsAgrees nameEq keyEq component child source Nothing equation = Refl
lookupOrdinalsAgrees nameEq keyEq component child source (Just fiber) equation =
  parentOrdinalsAgrees keyEq component fiber (fiberParent fiber) Refl

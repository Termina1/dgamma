module DGamma.L2R12ClosedFold

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2CheckedSnapshot
import DGamma.L2R2ForeignReplay
import DGamma.L2R11WordInventory
import DGamma.L2R11ActualWordReplay
import DGamma.L2R12KindDispatch
import DGamma.L2R12InventoryDomain
import Prelude.Types
import Prelude.Interfaces
import Data.List
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| CLOSED actual-kind-domain retirement fold: the local callback is now
||| fully discharged by native orchestration/Begin/all-tag Advance adapters.
||| Actual own-child provenance and finite inventory acceptance are explicit.
||| The old universal ForeignReplay.single theorem remains byte-unchanged.
export
0 replayRestrictedRetirement :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent : name) ->
  (fiber : Fiber name key value world error) ->
  (first, finalState : SystemState name key value world error) ->
  (trace : Transitions first finalState) -> (foreign : ForeignChildRun nameEq keyEq child trace) ->
  (0 foundFinal : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry finalState) = Just fiber) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} first = True) ->
  (0 ownChild : fiberParent fiber = ChildOf parent) ->
  (0 restricted : all (\code => not (wordActionInventory (replayActionWord trace) code) ||
    elemDec code [0, 1, 2, 3, 4]) [0, 1, 2, 3, 4, 5, 6, 7] = True) ->
  RetirementReplay name key world error value nameEq child fiber trace
replayRestrictedRetirement nameEq keyEq child parent fiber first finalState trace foreign foundFinal valid ownChild restricted =
  replayOverActualWord nameEq keyEq child fiber first finalState trace foreign foundFinal valid
    (\before, afterState, current, action, tag, present, original, distinct, found, originalValid, currentValid, same =>
      replayAdmittedRetirementKind nameEq keyEq child parent fiber before afterState current action tag
        (inventoryAdmittedKind (replayActionWord trace) action restricted present)
        original distinct found ownChild originalValid currentValid same)

module DGamma.L2R2RetireInsert

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5L2R1ChildRelocation
import Decidable.Equality
import Data.List.Elem

%default total
%unbound_implicits off

||| Root insertion's raw runtime observation at an actual absent lookup and
||| native declaration guard. No equality of erased uniqueness proofs is asserted.
||| Auxiliary evaluator evidence, not a CP3 placement copy or complete square.
export
0 rootInsertAtAbsence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (root : name) ->
  (component : Component key value world error) -> (ambient : world) ->
  (fibers : Registry name key value world error) ->
  (0 absent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} root fibers = Nothing) ->
  (0 free : provisionsDisjointFrom {name} {key} {value} {world} {error} @{keyEq}
    (componentProvisions component) (bindings fibers) = True) ->
  observeActionResult (applyAction @{nameEq} @{keyEq} (OInsert root Root component)
    (MkSystemState ambient fibers)) =
    Just (OInsertTag, MkRuntimeSnapshot ambient
      (Bind root (freshFiber component Root) :: bindings fibers))
rootInsertAtAbsence nameEq keyEq root component ambient (MkCoeffectContext entries unique) absent free =
  rewrite free in rewrite absent in Refl

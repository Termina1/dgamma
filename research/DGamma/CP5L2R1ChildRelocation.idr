module DGamma.CP5L2R1ChildRelocation

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import Decidable.Equality

%default total
%unbound_implicits off

||| A distinct action owner leaves the child's entire source fiber unchanged.
||| This uses the native evaluator's local-update theorem, not parent metadata
||| supplied for the destination. Consequently its parent lookup is preserved.
export
0 childForeignLookupFrame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) ->
  {before, afterState : SystemState name key value world error} ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  (0 distinct : Not (child = actionOwner action)) ->
  lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry afterState) =
  lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry before)
childForeignLookupFrame nameEq keyEq child {before} {afterState} action tag checked distinct =
  systemLocalUpdateForeign nameEq child (actionOwner action) distinct before afterState
    (applyActionLocalUpdate nameEq keyEq action before afterState tag
      (checkedActionProjects nameEq keyEq action before afterState tag checked))

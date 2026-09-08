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

||| Native early retirement at an observed source fiber, with its checked
||| target admitted by the existing four-clause preservation theorem.
export
0 childRetireAtFound :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) ->
  (fiber : Fiber name key value world error) ->
  (state : SystemState name key value world error) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry state) = Just fiber) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} state = True) ->
  checkedApplyAction @{nameEq} @{keyEq} (ORetire child) state =
    Just (ORetireTag, MkSystemState (worldState state)
      (replaceBinding @{nameEq} child (retireFiber fiber) (registry state)))
childRetireAtFound nameEq keyEq child fiber (MkSystemState ambient fibers) found valid =
  rewrite found in
  rewrite registryWellFormedRetire nameEq keyEq ambient child fiber fibers found valid in Refl

||| Pull a child's actual post-action lookup back through one foreign edge
||| and construct the checked early Retire. This proves early applicability,
||| not yet the second edge or the complete adjacent commutation square.
export
0 childRetireBeforeForeign :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) ->
  (fiber : Fiber name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  (0 distinct : Not (child = actionOwner action)) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry afterState) = Just fiber) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} before = True) ->
  checkedApplyAction @{nameEq} @{keyEq} (ORetire child) before =
    Just (ORetireTag, MkSystemState (worldState before)
      (replaceBinding @{nameEq} child (retireFiber fiber) (registry before)))
childRetireBeforeForeign nameEq keyEq child fiber before afterState action tag checked distinct found valid =
  childRetireAtFound nameEq keyEq child fiber before
    (trans (sym (childForeignLookupFrame nameEq keyEq child action tag checked distinct)) found) valid

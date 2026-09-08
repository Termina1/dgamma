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

||| The type of the producer-owned checked equation at a physical trace
||| ordinal; out-of-range observations carry only Unit, never an edge.
public export
0 NativeCheckedAt :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  Nat -> Transitions first finalState -> Type
NativeCheckedAt position NoTransitions = Unit
NativeCheckedAt Z (MoreTransitions (Fired {before} {afterState} nameEq keyEq action tag checked) rest) =
  checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)
NativeCheckedAt (S position) (MoreTransitions step rest) = NativeCheckedAt position rest

||| Extract the exact native proof at the requested ordinal. No evaluator
||| normalization is repeated, and an absent ordinal yields only Unit.
public export
0 nativeCheckedAt :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  (position : Nat) -> (trace : Transitions first finalState) -> NativeCheckedAt position trace
nativeCheckedAt position NoTransitions = ()
nativeCheckedAt Z (MoreTransitions (Fired nameEq keyEq action tag checked) rest) = checked
nativeCheckedAt (S position) (MoreTransitions step rest) = nativeCheckedAt position rest

||| A physical run whose EVERY native action has a distinct owner from the
||| child. Exact dictionaries and equations are indexed by the actual trace.
public export
data ForeignChildRun :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  ForeignChildEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} -> {child : name} ->
    {state : SystemState name key value world error} ->
    ForeignChildRun nameEq keyEq child (NoTransitions {state})
  ForeignChildStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} -> {child : name} ->
    {first, middle, finalState : SystemState name key value world error} ->
    (action : Action name key value world error) -> (tag : RuleTag) ->
    (0 checked : checkedApplyAction @{nameEq} @{keyEq} action first = Just (tag, middle)) ->
    (rest : Transitions middle finalState) ->
    (0 distinct : Not (child = actionOwner action)) ->
    (0 tail : ForeignChildRun nameEq keyEq child rest) ->
    ForeignChildRun nameEq keyEq child
      (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq action tag checked) rest)

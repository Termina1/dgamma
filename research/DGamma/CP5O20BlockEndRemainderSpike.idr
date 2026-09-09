module DGamma.CP5O20BlockEndRemainderSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5O20ProgramRoleWordSpike
import DGamma.CP5O20PairedRemovalSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5O20CanonicalBlockWordAgreementSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| The same explicitly observed primitive lookup gives equal native Active
||| bits at two states. No projected guard is reconstructed from a record.
export
0 o20ActiveLookupFrame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry before) = observed) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry afterState) = observed) ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected before =
   supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected afterState)
o20ActiveLookupFrame nameEq selected before afterState Nothing leftExact rightExact =
  rewrite leftExact in rewrite rightExact in Refl
o20ActiveLookupFrame nameEq selected before afterState (Just fiber) leftExact rightExact =
  rewrite leftExact in rewrite rightExact in Refl

||| An observed native Active endpoint has no successful-activation remainder.
||| Inactive/Reloading are rejected by the actual native Active-bit equation.
export
0 o20ActiveRemainderObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) -> (state : SystemState name key value world error) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry state) = observed) ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected state = True) ->
  (o20FiberRoleRemainder (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry state)) = [])
o20ActiveRemainderObserved nameEq selected state Nothing exact active = rewrite exact in Refl
o20ActiveRemainderObserved {name} {key} {value} {world} {error} nameEq selected state
  (Just (MkFiber component parent retiredFlag table (Inactive outcome))) exact active =
    void (uninhabited (trans (sym (the
      (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected state = False)
      (rewrite exact in Refl))) active))
o20ActiveRemainderObserved {name} {key} {value} {world} {error} nameEq selected state
  (Just (MkFiber component parent retiredFlag table (Reloading remaining accumulator view))) exact active =
    void (uninhabited (trans (sym (the
      (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected state = False)
      (rewrite exact in Refl))) active))
o20ActiveRemainderObserved nameEq selected state
  (Just (MkFiber component parent retiredFlag table (Active accumulator view))) exact active = rewrite exact in Refl
o20ActiveRemainderObserved nameEq selected state
  (Just (MkFiber component parent retiredFlag table (Unloading accumulator view outcome))) exact active = rewrite exact in Refl

||| An actual Insert's native target is inactive at its newly inserted name.
||| The single-constructor native observation owns its real target registry.
export
0 o20InsertViewNotActive :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  {tag : RuleTag} -> {afterState : SystemState name key value world error} ->
  ForeignInsertPlanView name key world error value nameEq keyEq selected parent component ambient fibers tag afterState ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected afterState = False)
o20InsertViewNotActive nameEq keyEq selected parent component ambient fibers (MkForeignInsertPlanView absent guards) =
  rewrite lookupInserted @{nameEq} selected (freshFiber component parent) fibers absent in Refl

||| Retiring a fiber changes its flag, never its lifecycle Active bit.
export
0 o20RetireFiberActive :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (fiber : Fiber name key value world error) ->
  (isActive (fiberLifecycle (retireFiber fiber)) = isActive (fiberLifecycle fiber))
o20RetireFiberActive (MkFiber component parent retiredFlag table lifecycle) = Refl

||| The actual native Retire observation preserves its owner's Active bit.
||| Both primitive lookups belong to the same replaced fiber and target.
export
0 o20RetireViewActive :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  {tag : RuleTag} -> {afterState : SystemState name key value world error} ->
  RetireSuccessView name key world error value nameEq selected ambient fibers tag afterState ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected (MkSystemState ambient fibers) =
   supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected afterState)
o20RetireViewActive nameEq selected ambient fibers (MkRetireSuccessView fiber found) =
  rewrite lookupReplacedFiber @{nameEq} selected fiber (retireFiber fiber) fibers found in
  rewrite found in sym (o20RetireFiberActive fiber)

||| The actual native Remove observation makes its owner's Active bit false.
||| Absence is obtained by finite deletion lookup, not scalar normalization of
||| an independently reconstructed evaluator endpoint.
export
0 o20RemoveViewNotActive :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  {tag : RuleTag} -> {afterState : SystemState name key value world error} ->
  RemoveSuccessView name key world error value nameEq selected ambient fibers tag afterState ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected afterState = False)
o20RemoveViewNotActive nameEq selected ambient fibers (MkRemoveSuccessView fiber found guards childless) =
  rewrite o20DeletedLookupAbsent nameEq selected fibers in Refl

||| Every actual non-lifecycle owner action reflects Active backwards. Insert
||| and Remove cannot end Active; Retire preserves it. No operation is skipped.
export
0 o20NonLifecycleOwnerActiveBackward :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (applyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} action (MkSystemState ambient fibers) = Just (tag, afterState)) ->
  (isLifecycleAction action = False) ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) afterState = True) ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) (MkSystemState ambient fibers) = True)
o20NonLifecycleOwnerActiveBackward nameEq keyEq (OInsert selected parent component) ambient fibers afterState tag raw nonLifecycle active =
  void (uninhabited (trans (sym (o20InsertViewNotActive nameEq keyEq selected parent component ambient fibers
    (foreignInsertPlanView nameEq keyEq selected parent component ambient fibers tag afterState raw))) active))
o20NonLifecycleOwnerActiveBackward nameEq keyEq (ORetire selected) ambient fibers afterState tag raw nonLifecycle active =
  trans (o20RetireViewActive nameEq selected ambient fibers
    (retireSuccessView nameEq keyEq selected ambient fibers tag afterState raw)) active
o20NonLifecycleOwnerActiveBackward nameEq keyEq (ORemove selected) ambient fibers afterState tag raw nonLifecycle active =
  void (uninhabited (trans (sym (o20RemoveViewNotActive nameEq selected ambient fibers
    (removeSuccessView nameEq keyEq selected ambient fibers tag afterState raw))) active))
o20NonLifecycleOwnerActiveBackward nameEq keyEq (LBegin selected) ambient fibers afterState tag raw nonLifecycle active = absurd nonLifecycle
o20NonLifecycleOwnerActiveBackward nameEq keyEq (LAdvance selected) ambient fibers afterState tag raw nonLifecycle active = absurd nonLifecycle
o20NonLifecycleOwnerActiveBackward nameEq keyEq (LDivert selected) ambient fibers afterState tag raw nonLifecycle active = absurd nonLifecycle
o20NonLifecycleOwnerActiveBackward nameEq keyEq (LLeave selected) ambient fibers afterState tag raw nonLifecycle active = absurd nonLifecycle
o20NonLifecycleOwnerActiveBackward nameEq keyEq (LUnload selected) ambient fibers afterState tag raw nonLifecycle active = absurd nonLifecycle

||| Observe the native lifecycle Bool at its call site. An excluded owner
||| lifecycle cannot occur; the false branch uses real orchestration semantics.
export
0 o20OwnerActiveAtLifecycleBool :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (applyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} action (MkSystemState ambient fibers) = Just (tag, afterState)) ->
  (observed : Bool) -> (isLifecycleAction action = observed) ->
  ((isLifecycleAction action = True) -> Void) ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) afterState = True) ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) (MkSystemState ambient fibers) = True)
o20OwnerActiveAtLifecycleBool nameEq keyEq action ambient fibers afterState tag raw False exact excluded active =
  o20NonLifecycleOwnerActiveBackward nameEq keyEq action ambient fibers afterState tag raw exact active
o20OwnerActiveAtLifecycleBool nameEq keyEq action ambient fibers afterState tag raw True exact excluded active = void (excluded exact)

||| The observed library owner decision selects an actual owner operation or
||| the generic foreign lookup frame. The native lifecycle Bool is observed
||| in the owner branch; no abstract conditional is projected or rebuilt.
export
0 o20NoLifecycleActiveAtOwnerDecision :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (applyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  ((isLifecycleAction action = True) -> (actionOwner action = selected) -> Void) ->
  (decision : Dec (selected = actionOwner action)) ->
  (decEq @{nameEq} selected (actionOwner action) = decision) ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected afterState = True) ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected before = True)
o20NoLifecycleActiveAtOwnerDecision {name} {key} {value} {world} {error}
  nameEq keyEq selected action (MkSystemState ambient fibers) afterState tag raw excluded (Yes same) decisionExact active =
    replace {p = \actor => supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} actor (MkSystemState ambient fibers) = True}
      (sym same)
      (o20OwnerActiveAtLifecycleBool nameEq keyEq action ambient fibers afterState tag raw
        (isLifecycleAction action) Refl (\lifecycle => excluded lifecycle (sym same))
        (replace {p = \actor => supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} actor afterState = True} same active))
o20NoLifecycleActiveAtOwnerDecision {name} {key} {value} {world} {error}
  nameEq keyEq selected action before afterState tag raw excluded (No distinct) decisionExact active =
    trans (o20ActiveLookupFrame nameEq selected before afterState
      (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry before)) Refl
      (systemLocalUpdateForeign nameEq selected (actionOwner action) distinct before afterState
        (applyActionLocalUpdate nameEq keyEq action before afterState tag raw))) active

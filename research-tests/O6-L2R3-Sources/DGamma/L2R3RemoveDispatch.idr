module DGamma.L2R3RemoveDispatch

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP4DeletionCommuteCore
import DGamma.CP4DeletionChildlessInvariant
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2CheckedSnapshot
import Decidable.Equality

%default total
%unbound_implicits off

||| Retirement changes no parent metadata. This one-constructor observation
||| supplies the native childlessness frame needed by a foreign Remove replay.
export
0 retirementKeepsParent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (fiber : Fiber name key value world error) ->
  fiberParent (retireFiber fiber) = fiberParent fiber
retirementKeepsParent (MkFiber component parent retired table lifecycle) = Refl

||| Actual raw foreign ORemove after early retirement of a distinct fiber.
||| Lookup and the full removal guard are transported; retirement preserves
||| parent metadata, hence cannot create a child of the removed actor.
||| This is NOT the exhausted own-child childRemoveAtFound statement.
export
0 removeAfterRetirementRaw :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, removed : name) ->
  (fiber, removedFiber : Fiber name key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (0 distinct : Not (child = removed)) ->
  (0 childFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child source = Just fiber) ->
  (0 removedFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} removed source = Just removedFiber) ->
  (0 removable : retired removedFiber && isInactive (fiberLifecycle removedFiber) &&
    not (hasChild {name} {key} {value} {world} {error} @{nameEq} removed source) = True) ->
  (0 noChild : hasChild {name} {key} {value} {world} {error} @{nameEq} removed source = False) ->
  applyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (ORemove removed)
    (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber fiber) source)) =
  Just (ORemoveTag, MkSystemState ambient
    (deleteBinding @{nameEq} removed (replaceBinding @{nameEq} child (retireFiber fiber) source)))
removeAfterRetirementRaw nameEq keyEq child removed fiber removedFiber ambient source
  distinct childFound removedFound removable noChild =
  rewrite trans (lookupReplaceOther @{nameEq} removed child (\same => distinct (sym same)) (retireFiber fiber) source) removedFound in
  rewrite hasChildReplaceFalse nameEq removed child (retireFiber fiber) fiber source childFound (retirementKeepsParent fiber) noChild in
  rewrite (replace {p = \children => retired removedFiber && isInactive (fiberLifecycle removedFiber) && not children = True} noChild removable) in Refl

||| Exact world/ordered-binding commutation of distinct child retirement and
||| foreign deletion. Uses CP4DeletionCommuteCore:266, not proof irrelevance.
export
0 retireRemoveSnapshot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (child, removed : name) ->
  (0 distinct : Not (child = removed)) ->
  (fiber : Fiber name key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState ambient (deleteBinding @{nameEq} removed (replaceBinding @{nameEq} child (retireFiber fiber) source))) =
  runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber fiber) (deleteBinding @{nameEq} removed source)))
retireRemoveSnapshot nameEq child removed distinct fiber ambient source =
  cong (MkRuntimeSnapshot ambient)
    (trans (deleteBindingAfterDistinctReplaceBindings nameEq child removed distinct (retireFiber fiber) source)
      (sym (replaceBindingRuntimeBindings nameEq child (retireFiber fiber) (deleteBinding @{nameEq} removed source))))

||| Produce a checked foreign Remove replay from its observed original source
||| fiber/guard. The arbitrary replay source need only be well formed and have
||| the exact retired runtime snapshot. Alternate validity is Preservation.
export
0 replayRemoveAtObservedSource :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, removed : name) ->
  (fiber, removedFiber : Fiber name key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (current : SystemState name key value world error) ->
  (0 distinct : Not (child = removed)) ->
  (0 childFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child source = Just fiber) ->
  (0 removedFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} removed source = Just removedFiber) ->
  (0 removable : retired removedFiber && isInactive (fiberLifecycle removedFiber) &&
    not (hasChild {name} {key} {value} {world} {error} @{nameEq} removed source) = True) ->
  (0 noChild : hasChild {name} {key} {value} {world} {error} @{nameEq} removed source = False) ->
  (0 valid : registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (MkSystemState ambient source) = True) ->
  (0 currentValid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 currentSame : runtimeSnapshot current = runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber fiber) source))) ->
  CheckedSnapshotStep name key world error value nameEq keyEq (ORemove removed) current ORemoveTag
    (runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber fiber) (deleteBinding @{nameEq} removed source))))
replayRemoveAtObservedSource nameEq keyEq child removed fiber removedFiber ambient source current
  distinct childFound removedFound removable noChild valid currentValid currentSame =
  replace {p = \expected => CheckedSnapshotStep name key world error value nameEq keyEq (ORemove removed) current ORemoveTag expected}
    (retireRemoveSnapshot nameEq child removed distinct fiber ambient source)
    (checkedAcrossSnapshot nameEq keyEq (ORemove removed) ORemoveTag
      (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber fiber) source))
      (MkSystemState ambient (deleteBinding @{nameEq} removed (replaceBinding @{nameEq} child (retireFiber fiber) source))) current
      (checkedFromRaw nameEq keyEq (ORemove removed)
        (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber fiber) source))
        (MkSystemState ambient (deleteBinding @{nameEq} removed (replaceBinding @{nameEq} child (retireFiber fiber) source))) ORemoveTag
        (registryWellFormedRetire nameEq keyEq ambient child fiber source childFound valid)
        (removeAfterRetirementRaw nameEq keyEq child removed fiber removedFiber ambient source distinct childFound removedFound removable noChild))
      (sym currentSame) currentValid)

||| Eliminate the original native RemoveSuccessView exactly once. Its actual
||| guard, childlessness, tag and literal deletion endpoint determine replay;
||| the view is a single-constructor producer, not an Either-role adapter.
export
0 replayRemoveFromView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, removed : name) ->
  (fiber : Fiber name key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (afterState, current : SystemState name key value world error) -> (tag : RuleTag) ->
  (0 distinct : Not (child = removed)) ->
  (0 childFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child source = Just fiber) ->
  (0 valid : registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (MkSystemState ambient source) = True) ->
  (0 currentValid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 currentSame : runtimeSnapshot current = runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber fiber) source))) ->
  RemoveSuccessView name key world error value nameEq removed ambient source tag afterState ->
  CheckedSnapshotStep name key world error value nameEq keyEq (ORemove removed) current tag
    (runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState afterState) (replaceBinding @{nameEq} child (retireFiber fiber) (registry afterState))))
replayRemoveFromView nameEq keyEq child removed fiber ambient source _ current _
  distinct childFound valid currentValid currentSame (MkRemoveSuccessView removedFiber removedFound removable noChild) =
  replayRemoveAtObservedSource nameEq keyEq child removed fiber removedFiber ambient source current
    distinct childFound removedFound removable noChild valid currentValid currentSame

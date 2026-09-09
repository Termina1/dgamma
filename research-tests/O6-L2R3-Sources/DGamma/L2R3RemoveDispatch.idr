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

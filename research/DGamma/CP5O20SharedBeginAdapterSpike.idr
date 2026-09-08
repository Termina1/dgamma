module DGamma.CP5O20SharedBeginAdapterSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20BeginObservationSpike
import DGamma.CP5O20AllNameSynchronizationSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| B8-style paired observed values: one runtime component, but the two ACTUAL
||| tables, parents, resolver views and output equations. This is the shared
||| adapter boundary, not a projected-record equality or endpoint oracle.
public export
record O20SharedBeginObservations
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (renaming : NameBijection name) (actor : name)
  (leftBefore, leftAfter, rightBefore, rightAfter : SystemState name key value world error) where
  constructor MkO20SharedBeginObservations
  sharedBeginComponent : Component key value world error
  sharedLeftParent : Parent name
  sharedRightParent : Parent name
  sharedLeftTable : OwnedTable key value (componentProvisions sharedBeginComponent)
  sharedRightTable : OwnedTable key value (componentProvisions sharedBeginComponent)
  sharedLeftView : View name (dependencies (componentDependencies sharedBeginComponent))
  sharedRightView : View name (dependencies (componentDependencies sharedBeginComponent))
  0 sharedLeftFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry leftBefore) =
    Just (MkFiber sharedBeginComponent sharedLeftParent False sharedLeftTable (Inactive Nothing))
  0 sharedRightFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) (registry rightBefore) =
    Just (MkFiber sharedBeginComponent sharedRightParent False sharedRightTable (Inactive Nothing))
  0 sharedLeftResolved : resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies sharedBeginComponent)) (registry leftBefore) = Just sharedLeftView
  0 sharedRightResolved : resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies sharedBeginComponent)) (registry rightBefore) = Just sharedRightView
  0 sharedLeftAfter : MkSystemState (worldState leftBefore) (replaceBinding @{nameEq} actor
    (MkFiber sharedBeginComponent sharedLeftParent False sharedLeftTable
      (Reloading (componentProgram sharedBeginComponent) id sharedLeftView)) (registry leftBefore)) = leftAfter
  0 sharedRightAfter : MkSystemState (worldState rightBefore) (replaceBinding @{nameEq} (renameForward renaming actor)
    (MkFiber sharedBeginComponent sharedRightParent False sharedRightTable
      (Reloading (componentProgram sharedBeginComponent) id sharedRightView)) (registry rightBefore)) = rightAfter

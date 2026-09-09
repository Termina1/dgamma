module DGamma.L2R3Attached

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ActorLifecycleOnlyExtended
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Actual key-release evidence inside the extended core. The removed entry
||| belongs to selected and declares a key declared by the attached root.
||| LocatedActionOccurrence owns the native ORemove edge and its decomposition.
||| This is local release evidence, not a universal last-release selector.
public export
record AttachedRelease
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (selected : name)
  {first, coreEnd : SystemState name key value world error}
  (core : Transitions first coreEnd)
  (component : Component key value world error) where
  constructor MkAttachedRelease
  releasedChild : name
  releasedFiber : Fiber name key value world error
  releaseOccurrence : LocatedActionOccurrence (ORemove releasedChild) core
  0 releaseFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq}
    releasedChild (registry (actionBeforeState releaseOccurrence)) = Just releasedFiber
  0 releaseParent : fiberParent releasedFiber = ChildOf selected
  sharedProvision : key
  0 childDeclares : Elem sharedProvision (dependencies (componentProvisions (fiberComponent releasedFiber)))
  0 rootDeclares : Elem sharedProvision (dependencies (componentProvisions component))

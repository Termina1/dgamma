module DGamma.L2R7ControlDisposition

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.L2R7AttachedC
import DGamma.L2R6FrontNormal
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Inhabitable SAME-BUNDLE disposition: both the earlier root birth and
||| its actual root control are INSIDE the ordered controls bundle, hence
||| inside the full attachedC body. Unlike L2R6's interim type, no nonexistent
||| interval AFTER the entire bundle is required. Cross-bundle origins OPEN.
public export
record ForcedRootControlInBundle
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState) (selected : name)
  (block : LocatedOpenEpisodeBlockAttachedC name key world error value nameEq keyEq selected global)
  (root : name) (action : Action name key value world error) where
  constructor MkForcedRootControlInBundle
  controlledComponent : Component key value world error
  controlInGlobal : LocatedActionOccurrence action global
  controlTagObserved : Bool
  0 controlTagEquation : rootControlAction action = controlTagObserved
  0 controlTagAccepted : controlTagObserved = True
  dispositionCoreEnd : SystemState name key value world error
  dispositionCore : Transitions (attachedCStart block) dispositionCoreEnd
  0 dispositionExtended : ActorLifecycleOnlyExtended nameEq selected dispositionCore
  dispositionBundle : Transitions dispositionCoreEnd (attachedCEnd block)
  0 dispositionOrdered : OrderedForcedRootBundleC nameEq selected dispositionCore [] dispositionBundle
  0 dispositionSplit : appendTransitions dispositionCore dispositionBundle = attachedCBody block
  bundledBirth : LocatedActionOccurrence (OInsert root Root controlledComponent) dispositionBundle
  bundledControl : LocatedActionOccurrence action dispositionBundle
  0 birthBeforeControl : LT (locatedActionOrdinal bundledBirth) (locatedActionOrdinal bundledControl)
  0 controlOwner : actionOwner action = root
  controlFiber : Fiber name key value world error
  0 controlFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} root (registry (actionBeforeState bundledControl)) = Just controlFiber
  0 controlRootParent : fiberParent controlFiber = Root
  0 controlPhysicalOrdinal : locatedActionOrdinal controlInGlobal =
    transitionCount (attachedCBefore block) + S (transitionCount dispositionCore + locatedActionOrdinal bundledControl)

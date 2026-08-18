module DGamma.CP4DeletionSelectedForeignLifecycleReplayCore

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import Decidable.Equality

%default total

||| Concrete checked survivor transition paired with the next ordered selected
||| quotient controls.  Effects are joined separately through the already
||| transposed `ForeignSelectedEffectStep` output.
public export
record ForeignLifecycleControlReplay
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (action : Action name key value world error) (tag : RuleTag)
  (planAfter, survivorBefore : SystemState name key value world error) where
  constructor MkForeignLifecycleControlReplay
  foreignLifecycleAfter : SystemState name key value world error
  0 foreignLifecycleRaw : applyAction @{nameEq} @{keyEq} action survivorBefore =
    Just (tag, foreignLifecycleAfter)
  0 foreignLifecycleChecked : checkedApplyAction @{nameEq} @{keyEq} action
    survivorBefore = Just (tag, foreignLifecycleAfter)
  0 foreignLifecycleOrdered : SelectedOrderedRegistryControlsRelated name key
    world error value selected (bindings (registry planAfter))
    (bindings (registry foreignLifecycleAfter))

||| Forget the guard-only observations after saturation and recover the ordered
||| selected-exempt skeleton used by the next replay boundary.
public export
0 foreignLifecycleSourcesGiveSelectedOrdered :
  ForeignLifecycleOrderedSourcesRelated name key world error value nameEq keyEq
    selected deps left right ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    left right
foreignLifecycleSourcesGiveSelectedOrdered ForeignLifecycleSourcesNil =
  SelectedOrderedControlsNil
foreignLifecycleSourcesGiveSelectedOrdered
  (ForeignLifecycleSourcesCons current relation tail) =
    case relation of
      SelectedLifecycleSourceCell currentIsSelected static rightUninstalled
        rightInactive rightReliedFalse leftProviderFalse =>
          SelectedOrderedControlsCons current
            (SelectedFiberControls currentIsSelected static)
            (foreignLifecycleSourcesGiveSelectedOrdered tail)
      ForeignLifecycleSourceCell currentDistinct controls tablesSame reliedSame =>
        SelectedOrderedControlsCons current
          (ForeignFiberControls currentDistinct controls)
          (foreignLifecycleSourcesGiveSelectedOrdered tail)

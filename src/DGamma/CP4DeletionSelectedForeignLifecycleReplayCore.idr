module DGamma.CP4DeletionSelectedForeignLifecycleReplayCore

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionCommuteCore
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

||| Shared replacement-result packager for a reconstructed foreign lifecycle
||| rule.  It compares only ordered controls here; the already-transposed
||| Definition-60 effect output is joined by the selected boundary consumer.
public export
0 packageForeignLifecycleReplacementReplay :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> Not (actor = selected) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (planAfter : SystemState name key value world error) ->
  (survivorAmbient : world) ->
  (plan, survivor : Registry name key value world error) ->
  (leftNext, rightNext : Fiber name key value world error) ->
  FiberControlRelated leftNext rightNext ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (bindings plan) (bindings survivor) ->
  (planAfterWorld : world) ->
  MkSystemState planAfterWorld
    (replaceBinding @{nameEq} actor leftNext plan) = planAfter ->
  (survivorAfterWorld : world) ->
  (survivorRaw : applyAction @{nameEq} @{keyEq} action
    (MkSystemState survivorAmbient survivor) =
      Just (tag, MkSystemState survivorAfterWorld
        (replaceBinding @{nameEq} actor rightNext survivor))) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkSystemState survivorAmbient survivor) = True ->
  ForeignLifecycleControlReplay name key world error value nameEq keyEq
    selected action tag planAfter (MkSystemState survivorAmbient survivor)
packageForeignLifecycleReplacementReplay nameEq keyEq selected actor
  actorDistinct action tag planAfter survivorAmbient plan survivor leftNext
  rightNext nextControls sourceOrdered planAfterWorld planAfterShape
  survivorAfterWorld survivorRaw survivorWellFormed =
    let survivorAfter : SystemState name key value world error
        survivorAfter = MkSystemState survivorAfterWorld
          (replaceBinding @{nameEq} actor rightNext survivor)
        0 survivorAfterWellFormed : registryWellFormed @{nameEq} @{keyEq}
          {name = name} {key = key} {value = value} {world = world}
          {error = error}
          survivorAfter = True
        survivorAfterWellFormed = preservationTheoremProof nameEq keyEq action
          (MkSystemState survivorAmbient survivor) survivorAfter tag
          survivorWellFormed survivorRaw
        0 survivorChecked : checkedApplyAction @{nameEq} @{keyEq} action
          (MkSystemState survivorAmbient survivor) = Just (tag, survivorAfter)
        survivorChecked = rewrite survivorRaw in
          rewrite survivorAfterWellFormed in Refl
        0 replacedOrdered : SelectedOrderedRegistryControlsRelated name key
          world error value selected
          (replaceEntries @{nameEq} actor leftNext (bindings plan))
          (replaceEntries @{nameEq} actor rightNext (bindings survivor))
        replacedOrdered = selectedOrderedReplaceForeign nameEq selected actor
          actorDistinct leftNext rightNext nextControls (bindings plan)
          (bindings survivor) sourceOrdered
        0 planBindings : bindings
          (replaceBinding @{nameEq} actor leftNext plan) =
          replaceEntries @{nameEq} actor leftNext (bindings plan)
        planBindings = replaceBindingRuntimeBindings nameEq actor leftNext plan
        0 survivorBindings : bindings
          (replaceBinding @{nameEq} actor rightNext survivor) =
          replaceEntries @{nameEq} actor rightNext (bindings survivor)
        survivorBindings = replaceBindingRuntimeBindings nameEq actor rightNext
          survivor
        0 concreteOrdered : SelectedOrderedRegistryControlsRelated name key
          world error value selected
          (bindings (replaceBinding @{nameEq} actor leftNext plan))
          (bindings (replaceBinding @{nameEq} actor rightNext survivor))
        concreteOrdered = selectedOrderedTransport (sym planBindings)
          (sym survivorBindings) replacedOrdered
        0 finalOrdered : SelectedOrderedRegistryControlsRelated name key world
          error value selected (bindings (registry planAfter))
          (bindings (registry survivorAfter))
        finalOrdered = selectedOrderedTransport
          (cong (\state => bindings (registry state)) planAfterShape)
          Refl concreteOrdered
    in MkForeignLifecycleControlReplay survivorAfter survivorRaw
      survivorChecked finalOrdered

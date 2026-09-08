module DGamma.CP5O20SingleRoleAdvanceExtractionSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionFrames
import DGamma.CP5O19ActualCommutedDomainSpike
import DGamma.CP5O19CommutedDomainSpike
import DGamma.CP5O19AdvanceObservationSpike
import Data.List
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Single-role native Iter source producer, not an Either Iter/Finish adapter.
||| Its ACTUAL checked step supplies the captured-domain proof. No successful
||| callback, paired cut or assumed partial-map domain is a caller premise.
export
0 o20IterCapturedDomain :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step, next : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (more : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (older : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before) = Just (MkFiber component parent retiredFlag table (Reloading (step :: next :: more) older view))) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance actor) before = Just (LIterTag, afterState)) ->
  (isJust (fiberAdvanceRuntimeEffectMap nameEq keyEq actor
    (MkFiber component parent retiredFlag table (Reloading (step :: next :: more) older view))
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} before)) = True)
o20IterCapturedDomain nameEq keyEq actor before afterState component parent retiredFlag table step next more older view found checked =
  trans (sym (cong isJust
    (the (partialEffectMapFor nameEq keyEq (LAdvance actor) LIterTag before (projectEffectState @{nameEq} before) =
      fiberAdvanceRuntimeEffectMap nameEq keyEq actor (MkFiber component parent retiredFlag table (Reloading (step :: next :: more) older view)) (projectEffectState @{nameEq} before))
      (rewrite found in Refl))))
    (o19RelatedDefined (o19ActualFrameRelated nameEq keyEq (LAdvance actor) LIterTag before afterState
      (actualTransitionEffectFrame nameEq keyEq (LAdvance actor) LIterTag before afterState checked)))

||| Single-role last-step Finish source producer, not an Either Iter/Finish adapter.
||| Its ACTUAL checked step supplies the captured-domain proof. No successful
||| callback, paired cut or assumed partial-map domain is a caller premise.
export
0 o20FinishOneCapturedDomain :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (older : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before) = Just (MkFiber component parent retiredFlag table (Reloading [step] older view))) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance actor) before = Just (LFinishTag, afterState)) ->
  (isJust (fiberAdvanceRuntimeEffectMap nameEq keyEq actor
    (MkFiber component parent retiredFlag table (Reloading [step] older view))
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} before)) = True)
o20FinishOneCapturedDomain nameEq keyEq actor before afterState component parent retiredFlag table step older view found checked =
  trans (sym (cong isJust
    (the (partialEffectMapFor nameEq keyEq (LAdvance actor) LFinishTag before (projectEffectState @{nameEq} before) =
      fiberAdvanceRuntimeEffectMap nameEq keyEq actor (MkFiber component parent retiredFlag table (Reloading [step] older view)) (projectEffectState @{nameEq} before))
      (rewrite found in Refl))))
    (o19RelatedDefined (o19ActualFrameRelated nameEq keyEq (LAdvance actor) LFinishTag before afterState
      (actualTransitionEffectFrame nameEq keyEq (LAdvance actor) LFinishTag before afterState checked)))

||| Runtime capability/callback packet at the actual raw source table. The
||| resolver and callback equations belong to these exact observed values.
public export
record O20NativeStepValues
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (before : SystemState name key value world error)
  (component : Component key value world error)
  (table : OwnedTable key value (componentProvisions component))
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))
  (view : View name (dependencies (componentDependencies component))) where
  constructor MkO20NativeStepValues
  nativeCapability : DepValues key value (dependencies (componentDependencies component))
  0 nativeResolution :
    (resolveCommittedValues {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
      (dependencies (componentDependencies component)) view (registry before) = Just nativeCapability)
  nativeCallback : O19StepObservation key world error value (dependencies (componentDependencies component))
    (componentProvisions component) step nativeCapability
    (MkLocalState (worldState before) (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component) (ownedValues table)))

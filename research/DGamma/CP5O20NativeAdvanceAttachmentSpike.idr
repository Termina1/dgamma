module DGamma.CP5O20NativeAdvanceAttachmentSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionFrameCore
import DGamma.CP5O19AdvanceObservationSpike
import DGamma.CP5O20SingleRoleAdvanceExtractionSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| Capability and callback observations at the exact PROJECTED runtime source
||| used by the history successor. The primitive equations belong to these
||| values, including the successful callback equation; no successor relation
||| is stored. Native producers below must authenticate the success packet.
public export
record O20EffectStepValues
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (actor : name)
  (before : SystemState name key value world error)
  (component : Component key value world error)
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))
  (view : View name (dependencies (componentDependencies component))) where
  constructor MkO20EffectStepValues
  effectStepCapability : DepValues key value (dependencies (componentDependencies component))
  0 effectStepResolved :
    (resolveEffectValues {name} {key} {value} {world} @{keyEq}
      (dependencies (componentDependencies component)) view
      (projectEffectState {name} {key} {value} {world} {error} @{nameEq} before) = Just effectStepCapability)
  effectStepCallback : O19StepObservation key world error value (dependencies (componentDependencies component))
    (componentProvisions component) step effectStepCapability
    (MkLocalState (effectAmbient (projectEffectState {name} {key} {value} {world} {error} @{nameEq} before))
      (restrictOwnedPreservingOrder {key} {value} @{keyEq} (componentProvisions component)
        (effectTables (projectEffectState {name} {key} {value} {world} {error} @{nameEq} before) actor)))

||| Rebase one observed native packet to the projected resolver and table.
||| The exact owner lookup supplies table identity; the producer preserves
||| the SAME callback outputs rather than comparing dependent projections.
export
0 o20NativeValuesAtEffectSource :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before : SystemState name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before) = Just (MkFiber component parent retiredFlag table lifecycle)) ->
  O20NativeStepValues name key world error value nameEq keyEq before component table step view ->
  O20EffectStepValues name key world error value nameEq keyEq actor before component step view
o20NativeValuesAtEffectSource nameEq keyEq actor (MkSystemState ambient fibers) component parent retiredFlag table lifecycle step view found
  (MkO20NativeStepValues capability resolved callback) =
    MkO20EffectStepValues capability
      (trans (resolveEffectValuesProjected nameEq keyEq (dependencies (componentDependencies component)) view (MkSystemState ambient fibers)) resolved)
      (rewrite projectedActorTable nameEq actor (MkSystemState ambient fibers) (MkFiber component parent retiredFlag table lifecycle) found in callback)

||| An actual checked Iter supplies the exact effect-level resolver and
||| callback packet demanded by the history successor. Only the native source
||| lookup remains explicit, not domain, callback success or output equality.
export
0 o20IterEffectValues :
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
  O20EffectStepValues name key world error value nameEq keyEq actor before component step view
o20IterEffectValues nameEq keyEq actor before afterState component parent retiredFlag table step next more older view found checked =
  o20NativeValuesAtEffectSource nameEq keyEq actor before component parent retiredFlag table
    (Reloading (step :: next :: more) older view) step view found
    (o20IterNativeValues nameEq keyEq actor before afterState component parent retiredFlag table step next more older view found checked)

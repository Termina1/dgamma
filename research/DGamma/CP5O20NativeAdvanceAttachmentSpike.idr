module DGamma.CP5O20NativeAdvanceAttachmentSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionFrameCore
import DGamma.CP4ProgressPotential
import DGamma.CP5O20PairedAdvanceSpike
import DGamma.CP5O19AdvanceObservationSpike
import DGamma.CP5O20SingleRoleAdvanceExtractionSpike
import Data.Maybe
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

||| Actual last-step Finish produces the same projected-source packet without
||| an Either-role callback adapter. Empty Finish has no callback and is not
||| claimed by this single-role theorem.
export
0 o20FinishOneEffectValues :
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
  O20EffectStepValues name key world error value nameEq keyEq actor before component step view
o20FinishOneEffectValues nameEq keyEq actor before afterState component parent retiredFlag table step older view found checked =
  o20NativeValuesAtEffectSource nameEq keyEq actor before component parent retiredFlag table
    (Reloading [step] older view) step view found
    (o20FinishOneNativeValues nameEq keyEq actor before afterState component parent retiredFlag table step older view found checked)

||| Primitive successful Advance equation at explicit resolver/callback
||| observations. Only the remaining-program list is eliminated. This retains
||| the literal native target needed to attach a history successor to an edge.
export
0 o20ObservedAdvanceRawEquation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (rest : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (older : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (capability : DepValues key value (dependencies (componentDependencies component))) ->
  (localAfter : LocalState key value world (componentProvisions component)) ->
  (undo : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor fibers = Just (MkFiber component parent retiredFlag table (Reloading (step :: rest) older view))) ->
  (targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table (Reloading (step :: rest) older view)) fibers = Just view) ->
  (resolveCommittedValues {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (dependencies (componentDependencies component)) view fibers = Just capability) ->
  (runStepEffect step capability (MkLocalState ambient (restrictOwnedPreservingOrder {key} {value} @{keyEq} (componentProvisions component) (ownedValues table))) = Right (localAfter, undo)) ->
  (applyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState ambient fibers) =
    Just ((case rest of [] => LFinishTag; _ :: _ => LIterTag),
      MkSystemState (localWorld localAfter) (replaceBinding @{nameEq} actor
        (MkFiber component parent retiredFlag (localTable localAfter)
          (o20SuccessfulAdvanceLifecycle {name} {key} {value} {world} {error} rest
            (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) older undo) view)) fibers)))
o20ObservedAdvanceRawEquation nameEq keyEq actor ambient fibers component parent retiredFlag table step [] older view capability localAfter undo found target resolved ran =
  rewrite found in rewrite resolved in rewrite ran in rewrite target in
    rewrite trans (viewEqSameNameList nameEq view view) (sameNameListReflexive nameEq (DGamma.Calculus.viewProviders view)) in Refl
o20ObservedAdvanceRawEquation nameEq keyEq actor ambient fibers component parent retiredFlag table step (next :: more) older view capability localAfter undo found target resolved ran =
  rewrite found in rewrite resolved in rewrite ran in rewrite target in
    rewrite trans (viewEqSameNameList nameEq view view) (sameNameListReflexive nameEq (DGamma.Calculus.viewProviders view)) in Refl

||| The actual checked edge's endpoint equals its own observed native target.
||| This is evaluator determinism at one shared source, not equality between
||| independently reconstructed proof-carrying states or observations.
export
0 o20ActualAdvanceObservedEndpoint :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (rest : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (older : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor fibers = Just (MkFiber component parent retiredFlag table (Reloading (step :: rest) older view))) ->
  (targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table (Reloading (step :: rest) older view)) fibers = Just view) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState ambient fibers) = Just (tag, afterState)) ->
  (observed : O20NativeStepValues name key world error value nameEq keyEq (MkSystemState ambient fibers) component table step view) ->
  (afterState = MkSystemState (localWorld (stepObservedAfter (nativeCallback observed)))
    (replaceBinding @{nameEq} actor
      (MkFiber component parent retiredFlag (localTable (stepObservedAfter (nativeCallback observed)))
        (o20SuccessfulAdvanceLifecycle {name} {key} {value} {world} {error} rest
          (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) older (stepObservedUndo (nativeCallback observed))) view)) fibers))
o20ActualAdvanceObservedEndpoint nameEq keyEq actor ambient fibers afterState tag component parent retiredFlag table step rest older view
  found target checked (MkO20NativeStepValues capability resolved callback) =
    cong snd (justInjective (trans
      (sym (checkedActionProjects nameEq keyEq (LAdvance actor) (MkSystemState ambient fibers) afterState tag checked))
      (o20ObservedAdvanceRawEquation nameEq keyEq actor ambient fibers component parent retiredFlag table step rest older view
        capability (stepObservedAfter callback) (stepObservedUndo callback) found target resolved (stepObservedRan callback))))

||| Project the SAME native callback's equation without creating a second
||| dependent observation. The primitive owner-table equation is the only
||| reindexing; local after-state and undo remain the native packet's values.
export
0 o20NativeCallbackProjected :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor fibers = Just (MkFiber component parent retiredFlag table lifecycle)) ->
  (observed : O20NativeStepValues name key world error value nameEq keyEq (MkSystemState ambient fibers) component table step view) ->
  (runStepEffect step (nativeCapability observed)
    (MkLocalState ambient (restrictOwnedPreservingOrder {key} {value} @{keyEq} (componentProvisions component)
      (effectTables (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState ambient fibers)) actor))) =
    Right (stepObservedAfter (nativeCallback observed), stepObservedUndo (nativeCallback observed)))
o20NativeCallbackProjected nameEq keyEq actor ambient fibers component parent retiredFlag table lifecycle step view found observed =
  rewrite projectedActorTable nameEq actor (MkSystemState ambient fibers) (MkFiber component parent retiredFlag table lifecycle) found in
    stepObservedRan (nativeCallback observed)

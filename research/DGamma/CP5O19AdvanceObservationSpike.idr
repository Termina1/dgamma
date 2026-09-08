module DGamma.CP5O19AdvanceObservationSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionFrameCore
import DGamma.CP4ProgressPotential
import DGamma.CP5ConfluenceLocalDiamondSpike
import Data.List
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Captured-map rebasing from EXPLICIT equal owner observations. The source
||| states may differ in ambient state and every foreign fiber. This observes
||| the primitive map, not a nested existential replay/diamond builder.
export
0 o19AdvanceCapturedMapAt :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (earlier, later : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) -> (tag : RuleTag) ->
  (lookupFiber @{nameEq} actor (registry earlier) = Just fiber) ->
  (lookupFiber @{nameEq} actor (registry later) = Just fiber) ->
  (state : EffectState name key value world) ->
  partialEffectMapFor nameEq keyEq (LAdvance actor) tag earlier state =
  partialEffectMapFor nameEq keyEq (LAdvance actor) tag later state
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber OInsertTag foundEarly foundLate state = Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber ORetireTag foundEarly foundLate state = Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber ORemoveTag foundEarly foundLate state = Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LBeginTag foundEarly foundLate state = Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LIterTag foundEarly foundLate state =
  rewrite foundEarly in rewrite foundLate in Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LFinishTag foundEarly foundLate state =
  rewrite foundEarly in rewrite foundLate in Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LDivertTag foundEarly foundLate state =
  rewrite foundEarly in rewrite foundLate in Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LRaiseTag foundEarly foundLate state = Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LLeaveTag foundEarly foundLate state = Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LUnloadTag foundEarly foundLate state = Refl

||| Transport only the EXPLICIT resolver observation of a concrete fiber.
||| Retirement is eliminated as an actual Boolean argument; no opaque target
||| or early applicability certificate is supplied by a caller.
export
0 o19ObservedTargetRebase :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) -> (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (earlier, later : Registry name key value world error) ->
  (observed : Maybe (View name (dependencies (componentDependencies component)))) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (dependencies (componentDependencies component)) earlier = observed) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (dependencies (componentDependencies component)) later = observed) ->
  (targetFiber @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table lifecycle) later = Just view) ->
  (targetFiber @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table lifecycle) earlier = Just view)
o19ObservedTargetRebase nameEq keyEq component parent False table lifecycle earlier later
  observed view earlyResolution lateResolution target =
    trans earlyResolution (trans (sym lateResolution) target)
o19ObservedTargetRebase nameEq keyEq component parent True table lifecycle earlier later
  observed view earlyResolution lateResolution target = void (nothingIsNotJust target)

||| Actual successful step output, retaining its own inverse and local state.
||| This observation authenticates the primitive callback, not a control guard.
public export
record O19StepObservation (key, world, error : Type) (value : key -> Type)
  (deps : List key) (provision : CoeffectSpec key)
  (step : StepEffect key value world error deps provision)
  (capability : DepValues key value deps)
  (localBefore : LocalState key value world provision) where
  constructor MkO19StepObservation
  stepObservedAfter : LocalState key value world provision
  stepObservedUndo : LocalState key value world provision -> LocalState key value world provision
  0 stepObservedRan : runStepEffect step capability localBefore = Right (stepObservedAfter, stepObservedUndo)

||| Decode an EXPLICIT callback result using partial-map definedness. A failed
||| callback contradicts that domain; no successful callback is an input.
export
0 o19StepSuccessObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (step : StepEffect key value world error deps provision) ->
  (capability : DepValues key value deps) -> (state : EffectState name key value world) ->
  (observed : Either error (LocalState key value world provision,
    LocalState key value world provision -> LocalState key value world provision)) ->
  (runStepEffect step capability (MkLocalState (effectAmbient state)
    (restrictOwnedPreservingOrder @{keyEq} provision (effectTables state actor))) = observed) ->
  (isJust (stepForwardEffectMap nameEq keyEq actor step capability state) = True) ->
  O19StepObservation key world error value deps provision step capability
    (MkLocalState (effectAmbient state) (restrictOwnedPreservingOrder @{keyEq} provision (effectTables state actor)))
o19StepSuccessObserved nameEq keyEq actor step capability state (Left failure) exact defined =
  case trans (sym (cong isJust
    (the (stepForwardEffectMap nameEq keyEq actor step capability state = Nothing)
      (rewrite exact in Refl)))) defined of
    Refl impossible
o19StepSuccessObserved nameEq keyEq actor step capability state (Right (localAfter, undo)) exact defined =
  MkO19StepObservation localAfter undo exact

||| Decode the ACTUAL captured capability map first, then the callback. Both
||| observations come from ordinary evaluator arguments; no computed dependent
||| result is scrutinized locally and no checked early edge is assumed.
export
0 o19AdvanceValuesObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (rest : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (state : EffectState name key value world) ->
  (observed : Maybe (DepValues key value (dependencies (componentDependencies component)))) ->
  (resolveEffectValues @{keyEq} (dependencies (componentDependencies component)) view state = observed) ->
  (isJust (fiberAdvanceRuntimeEffectMap nameEq keyEq actor
    (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) state) = True) ->
  (capability : DepValues key value (dependencies (componentDependencies component)) **
    (resolveEffectValues @{keyEq} (dependencies (componentDependencies component)) view state = Just capability,
     O19StepObservation key world error value (dependencies (componentDependencies component))
       (componentProvisions component) step capability
       (MkLocalState (effectAmbient state) (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component) (effectTables state actor)))))
o19AdvanceValuesObserved nameEq keyEq actor component parent retiredFlag table step rest accumulator view state Nothing exact defined =
  case trans (sym (cong isJust
    (the (fiberAdvanceRuntimeEffectMap nameEq keyEq actor
      (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) state = Nothing)
      (rewrite exact in Refl)))) defined of
    Refl impossible
o19AdvanceValuesObserved nameEq keyEq actor component parent retiredFlag table step rest accumulator view state (Just capability) exact defined =
  (capability ** (exact,
    o19StepSuccessObserved nameEq keyEq actor step capability state
      (runStepEffect step capability (MkLocalState (effectAmbient state)
        (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component) (effectTables state actor)))) Refl
      (trans (sym (cong isJust
        (the (fiberAdvanceRuntimeEffectMap nameEq keyEq actor
          (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) state =
          stepForwardEffectMap nameEq keyEq actor step capability state)
          (rewrite exact in Refl)))) defined)))

||| Rebase the EXPLICIT capability/callback output onto the raw evaluator's
||| actual committed resolver and owned-table normalization. The two existing
||| projection lemmas do the transport; no proof irrelevance is involved.
export
0 o19AdvanceValuesAtSource :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before : SystemState name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (rest : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (lookupFiber @{nameEq} actor (registry before) = Just (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view))) ->
  (observed : (capability : DepValues key value (dependencies (componentDependencies component)) **
    (resolveEffectValues @{keyEq} (dependencies (componentDependencies component)) view (projectEffectState @{nameEq} before) = Just capability,
     O19StepObservation key world error value (dependencies (componentDependencies component)) (componentProvisions component) step capability
       (MkLocalState (effectAmbient (projectEffectState @{nameEq} before))
         (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component) (effectTables (projectEffectState @{nameEq} before) actor)))))) ->
  (capability : DepValues key value (dependencies (componentDependencies component)) **
    (resolveCommittedValues {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (dependencies (componentDependencies component)) view (registry before) = Just capability,
     O19StepObservation key world error value (dependencies (componentDependencies component)) (componentProvisions component) step capability
       (MkLocalState (worldState before) (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component) (ownedValues table)))))
o19AdvanceValuesAtSource nameEq keyEq actor (MkSystemState ambient fibers) component parent retiredFlag table step rest accumulator view found
  (capability ** (resolved, ran)) =
    (capability **
      (trans (sym (resolveEffectValuesProjected nameEq keyEq (dependencies (componentDependencies component)) view (MkSystemState ambient fibers))) resolved,
       rewrite sym (projectedActorTable nameEq actor (MkSystemState ambient fibers)
         (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) found) in ran))

||| Empty Finish has no callback but still needs the actual target guard.
export
0 o19FinishEmptyAtObservedTarget :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (lookupFiber @{nameEq} actor fibers = Just (MkFiber component parent retiredFlag table (Reloading [] accumulator view))) ->
  (targetFiber @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table (Reloading [] accumulator view)) fibers = Just view) ->
  RawActivationMove {name} {key} {value} {world} {error} nameEq keyEq (LAdvance actor) LFinishTag (MkSystemState ambient fibers)
o19FinishEmptyAtObservedTarget nameEq keyEq actor ambient fibers component parent retiredFlag table accumulator view found target =
  MkRawActivationMove
    (MkSystemState ambient (replaceBinding @{nameEq} actor (MkFiber component parent retiredFlag table (Active accumulator view)) fibers))
    (rewrite found in rewrite target in
      rewrite trans (viewEqSameNameList nameEq view view) (sameNameListReflexive nameEq (DGamma.Calculus.viewProviders view)) in Refl)

module DGamma.CP5O19AdvanceObservationSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
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

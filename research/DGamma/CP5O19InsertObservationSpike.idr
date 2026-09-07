module DGamma.CP5O19InsertObservationSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP4DeletionSelectedForeignLifecycleBegin
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19OpeningPropagationSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| R184 supervisor-authorized cure: own the actual observed resolver VALUE
||| and both exact equations. This is neither a targetFiber equation nor the
||| exhausted insertion-target declaration. A checked insertion produces it.
public export
record O19ResolutionObservation
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (deps : List key)
  (before, afterState : Registry name key value world error) where
  constructor MkO19ResolutionObservation
  resolutionObserved : Maybe (View name deps)
  0 resolutionBefore : resolveView @{nameEq} @{keyEq} {value} {world} {error} deps before = resolutionObserved
  0 resolutionAfter : resolveView @{nameEq} @{keyEq} {value} {world} {error} deps afterState = resolutionObserved

||| The actual insertion plan retains its own absence proof; the shared
||| resolver value is evaluated at the original registry, never supplied.
export
0 o19ResolutionFromInsertPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (deps : List key) ->
  (child : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  ForeignInsertPlanView name key world error value nameEq keyEq child parent
    component ambient source tag afterState ->
  O19ResolutionObservation name key world error value nameEq keyEq deps source (registry afterState)
o19ResolutionFromInsertPlan {name} {key} {world} {error} {value}
  nameEq keyEq deps child parent component ambient source _ _
  (MkForeignInsertPlanView absent guards) =
    MkO19ResolutionObservation (resolveView @{nameEq} @{keyEq} {value} {world} {error} deps source)
      Refl (resolveViewInactiveInsert {name} {key} {world} {error} {value}
        nameEq keyEq deps child component parent source absent)

||| Execute the public insertion-plan producer on the actual checked edge,
||| then pass that explicit result across the A4 observation boundary.
export
0 o19ResolutionAfterCheckedInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (deps : List key) ->
  (child : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (checkedApplyAction @{nameEq} @{keyEq} (OInsert child parent component) before = Just (tag, afterState)) ->
  O19ResolutionObservation name key world error value nameEq keyEq deps (registry before) (registry afterState)
o19ResolutionAfterCheckedInsert nameEq keyEq deps child parent component
  (MkSystemState ambient source) afterState tag checked =
    o19ResolutionFromInsertPlan nameEq keyEq deps child parent component ambient source tag afterState
      (foreignInsertPlanView nameEq keyEq child parent component ambient source tag afterState
        (checkedActionProjects nameEq keyEq (OInsert child parent component)
          (MkSystemState ambient source) afterState tag checked))

module DGamma.CP5O19ResolvedOpeningRowSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19OpeningPropagationSpike
import DGamma.CP5O19InsertObservationSpike
import DGamma.CP5O20BeginObservationSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Reconstruct Begin from an EXPLICIT clean component and resolved view.
||| The goal contains only actual lookup/resolveView observations, never an
||| arbitrary targetFiber transport. Preservation supplies the checked domain.
export
0 o19BeginAtResolvedView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (resolved : View name (dependencies (componentDependencies component))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor source =
    Just (MkFiber component parent False table (Inactive Nothing))) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies component)) source = Just resolved) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (MkSystemState ambient source) = True) ->
  CheckedEarlyApplication name key world error value nameEq keyEq
    (MkSystemState ambient source) (LBegin actor) LBeginTag
o19BeginAtResolvedView nameEq keyEq actor ambient source component parent table
  resolved found resolution wellFormed =
    o19CheckObservedRawMove nameEq keyEq (LBegin actor) LBeginTag
      (MkSystemState ambient source) wellFormed
      (MkRawActivationMove
        (MkSystemState ambient (replaceBinding @{nameEq} actor
          (MkFiber component parent False table
            (Reloading (componentProgram component) id resolved)) source))
        (rewrite found in rewrite resolution in Refl))

||| Per-cut insertion guard with the resolved value/equations EXPLICIT.
||| Eliminate only the actual insertion plan. The owner remains the concrete
||| clean fiber observed at the initial Begin; no targetFiber goal arises.
export
0 o19BeginAfterObservedInsertion :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor, child : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (opened, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (initial : O20BeginObservation name key world error value nameEq keyEq actor
    (MkSystemState ambient source) opened) ->
  (resolution : O19ResolutionObservation name key world error value nameEq keyEq
    (dependencies (componentDependencies (beginObservedComponent initial))) source (registry afterState)) ->
  Not (actor = child) ->
  ForeignInsertPlanView name key world error value nameEq keyEq child parent component
    ambient source tag afterState ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} afterState = True) ->
  CheckedEarlyApplication name key world error value nameEq keyEq afterState (LBegin actor) LBeginTag
o19BeginAfterObservedInsertion nameEq keyEq actor child parent component ambient source
  opened _ _ initial resolution distinct (MkForeignInsertPlanView absent guards) wellFormed =
    o19BeginAtResolvedView nameEq keyEq actor ambient
      (insertBinding @{nameEq} child (freshFiber component parent) source absent)
      (beginObservedComponent initial) (beginObservedParent initial) (beginObservedTable initial)
      (beginObservedView initial)
      (trans (lookupInsertOther @{nameEq} actor child distinct (freshFiber component parent) source absent)
        (beginObservedFound initial))
      (trans (resolutionAfter resolution)
        (trans (sym (resolutionBefore resolution)) (beginObservedResolved initial))) wellFormed

||| Use the SAME checked insertion for its plan and preservation, keeping the
||| resolver observation explicit at the per-cut boundary.
export
0 o19BeginAfterCheckedObservedInsertion :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor, child : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (before, opened, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (initial : O20BeginObservation name key world error value nameEq keyEq actor before opened) ->
  (resolution : O19ResolutionObservation name key world error value nameEq keyEq
    (dependencies (componentDependencies (beginObservedComponent initial)))
    (registry before) (registry afterState)) ->
  Not (actor = child) ->
  (checkedApplyAction @{nameEq} @{keyEq} (OInsert child parent component) before = Just (tag, afterState)) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} before = True) ->
  CheckedEarlyApplication name key world error value nameEq keyEq afterState (LBegin actor) LBeginTag
o19BeginAfterCheckedObservedInsertion nameEq keyEq actor child parent component
  (MkSystemState ambient source) opened afterState tag initial resolution distinct checked wellFormed =
    o19BeginAfterObservedInsertion nameEq keyEq actor child parent component ambient source
      opened afterState tag initial resolution distinct
      (foreignInsertPlanView nameEq keyEq child parent component ambient source tag afterState
        (checkedActionProjects nameEq keyEq (OInsert child parent component)
          (MkSystemState ambient source) afterState tag checked))
      (preservationTheoremProof nameEq keyEq (OInsert child parent component)
        (MkSystemState ambient source) afterState tag wellFormed
        (checkedActionProjects nameEq keyEq (OInsert child parent component)
          (MkSystemState ambient source) afterState tag checked))

||| Explicit observation spine for an O/A Begin row. Each cut owns the actual
||| insertion, its resolved value/equations and the child/licensing exclusions.
||| No checked Begin guard is stored for any intermediate cut.
public export
data O19ObservedInsertions :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (deps : List key) ->
  {before, finalState : SystemState name key value world error} ->
  Transitions before finalState -> Type where
  ObservedInsertionsEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} -> {actor : name} -> {deps : List key} ->
    {before : SystemState name key value world error} ->
    O19ObservedInsertions name key world error value nameEq keyEq actor deps (NoTransitions {state = before})
  ObservedInsertionsStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} -> {actor : name} -> {deps : List key} ->
    {before, middle, finalState : SystemState name key value world error} ->
    (child : name) -> (parent : Parent name) -> (component : Component key value world error) ->
    (tag : RuleTag) ->
    (0 checked : checkedApplyAction @{nameEq} @{keyEq} (OInsert child parent component) before = Just (tag, middle)) ->
    (rest : Transitions middle finalState) ->
    (0 childSafe : Not (actor = child)) ->
    (0 parentSafe : (licensor : name) -> (parent = ChildOf licensor) -> Not (actor = licensor)) ->
    (0 resolution : O19ResolutionObservation name key world error value nameEq keyEq deps
      (registry before) (registry middle)) ->
    (0 remaining : O19ObservedInsertions name key world error value nameEq keyEq actor deps rest) ->
    O19ObservedInsertions name key world error value nameEq keyEq actor deps
      (MoreTransitions (Fired {before} {afterState = middle} nameEq keyEq
        (OInsert child parent component) tag checked) rest)


||| State-observed adapter, retaining the EXPLICIT clean fiber and target.
export
0 o19BeginAtResolvedState :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before : SystemState name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (resolved : View name (dependencies (componentDependencies component))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before) =
    Just (MkFiber component parent False table (Inactive Nothing))) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies component)) (registry before) = Just resolved) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    before = True) ->
  CheckedEarlyApplication name key world error value nameEq keyEq
    before (LBegin actor) LBeginTag
o19BeginAtResolvedState nameEq keyEq actor (MkSystemState ambient source) component parent
  table resolved found resolution wellFormed =
    o19BeginAtResolvedView nameEq keyEq actor ambient source component parent table
      resolved found resolution wellFormed

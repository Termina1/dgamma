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

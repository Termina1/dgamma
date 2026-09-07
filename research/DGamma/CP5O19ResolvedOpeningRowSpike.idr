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

module DGamma.CP5O20BeginObservationSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressProgramBound
import DGamma.CP4DeletionSelectedForeignLifecycleBegin
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionFrames
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20EpisodeSynchronizationSpike
import DGamma.CP5O20PairedPrefixProducerSpike
import DGamma.CP5O20CanonicalPairSelectionSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| An ACTUAL Begin observation owns the exact component, original fiber,
||| successfully resolved dependency view and resulting Reloading state. It
||| never takes a desired resolver result or destination equation as an oracle.
public export
record O20BeginObservation
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (actor : name)
  (before, afterState : SystemState name key value world error) where
  constructor MkO20BeginObservation
  beginObservedComponent : Component key value world error
  beginObservedParent : Parent name
  beginObservedTable : OwnedTable key value (componentProvisions beginObservedComponent)
  beginObservedView : View name (dependencies (componentDependencies beginObservedComponent))
  0 beginObservedFound : (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before) =
    Just (MkFiber beginObservedComponent beginObservedParent False beginObservedTable (Inactive Nothing)))
  0 beginObservedResolved : (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies beginObservedComponent)) (registry before) = Just beginObservedView)
  0 beginObservedAfter : (MkSystemState (worldState before)
    (replaceBinding @{nameEq} actor (MkFiber beginObservedComponent beginObservedParent False beginObservedTable
      (Reloading (componentProgram beginObservedComponent) id beginObservedView)) (registry before)) = afterState)

||| Eliminate an explicit actual Begin plan once. Its concrete False-retired
||| fiber already owns a successful target, so the resolver success is a direct
||| constructor projection, not a neutral targetFiber transport obligation.
export
0 o20BeginObservationFromPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (owner : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor source = Just owner) ->
  (afterState : SystemState name key value world error) ->
  ForeignBeginPlanView name key world error value nameEq keyEq actor ambient source owner LBeginTag afterState ->
  O20BeginObservation name key world error value nameEq keyEq actor (MkSystemState ambient source) afterState
o20BeginObservationFromPlan nameEq keyEq actor ambient source owner found afterState
  (MkForeignBeginPlanView {component} {parent} {table} view ownerShape targetFound tagShape afterShape) =
    MkO20BeginObservation component parent table view
      (trans found (cong Just ownerShape)) targetFound afterShape

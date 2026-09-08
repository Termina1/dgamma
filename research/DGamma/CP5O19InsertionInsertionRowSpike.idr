module DGamma.CP5O19InsertionInsertionRowSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP3StatementChecks
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19ActivationRowSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5UniqueRawNameInsertions
import Data.Nat
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19OpeningPropagationSpike
import DGamma.CP5O19InsertObservationSpike
import DGamma.CP5O19ActivationInsertionRowSpike
import DGamma.CP5O19ResolvedOpeningRowSpike
import DGamma.CP5O20BeginObservationSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Construct an insertion from its explicit setFresh observation and guard facts.
||| Preservation supplies the checked target domain; no early action assumed.
export
0 o19InsertAtObservedFresh :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (child : name) -> (parent : Parent name) -> (component : Component key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (observed : (applied : CoeffectApplied source **
    (setFresh @{nameEq} child (freshFiber component parent) source = Just applied))) ->
  (parentPresent {name} {key} {value} {world} {error} @{nameEq} parent source &&
    provisionsDisjointFrom {name} {key} {value} {world} {error} @{keyEq}
      (componentProvisions component) (bindings source) = True) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (MkSystemState ambient source) = True) ->
  CheckedEarlyApplication name key world error value nameEq keyEq (MkSystemState ambient source)
    (OInsert child parent component) OInsertTag
o19InsertAtObservedFresh nameEq keyEq child parent component ambient source (applied ** inserted) guards wellFormed =
  o19CheckObservedRawMove nameEq keyEq (OInsert child parent component) OInsertTag
    (MkSystemState ambient source) wellFormed
    (MkRawActivationMove
      (MkSystemState ambient (coeffectAfter applied))
      (rewrite guards in rewrite inserted in Refl))

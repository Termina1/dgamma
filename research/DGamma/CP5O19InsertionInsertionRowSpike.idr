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


||| Actual fresh-plan production, not equality of unrelated absence tokens.
export
0 o19InsertFromAbsentGuards :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (child : name) -> (parent : Parent name) -> (component : Component key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (absent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child source = Nothing) ->
  (parentPresent {name} {key} {value} {world} {error} @{nameEq} parent source &&
    provisionsDisjointFrom {name} {key} {value} {world} {error} @{keyEq}
      (componentProvisions component) (bindings source) = True) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (MkSystemState ambient source) = True) ->
  CheckedEarlyApplication name key world error value nameEq keyEq (MkSystemState ambient source)
    (OInsert child parent component) OInsertTag
o19InsertFromAbsentGuards nameEq keyEq child parent component ambient source absent guards wellFormed =
  o19InsertAtObservedFresh nameEq keyEq child parent component ambient source
    (DGamma.CP4DeletionSelectedForeignOrchestration.setFreshFromAbsent nameEq child
      (freshFiber component parent) source absent) guards wellFormed

||| A foreign insertion cannot supply this licensing parent. Observe Parent
||| once; the child case is a named lookup frame, not a resolver transport.
export
0 o19ParentBeforeForeignInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (parent : Parent name) -> (child : name) ->
  (insertedParent : Parent name) -> (component : Component key value world error) ->
  (source : Registry name key value world error) ->
  (absent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child source = Nothing) ->
  ((licensor : name) -> (parent = ChildOf licensor) -> Not (licensor = child)) ->
  (parentPresent {name} {key} {value} {world} {error} @{nameEq} parent
    (insertBinding @{nameEq} child (freshFiber component insertedParent) source absent) =
   parentPresent {name} {key} {value} {world} {error} @{nameEq} parent source)
o19ParentBeforeForeignInsert nameEq Root child insertedParent component source absent foreign = Refl
o19ParentBeforeForeignInsert nameEq (ChildOf licensor) child insertedParent component source absent foreign =
  cong isJust (lookupInsertOther @{nameEq} licensor child (foreign licensor Refl)
    (freshFiber component insertedParent) source absent)

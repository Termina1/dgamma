module DGamma.L2R5ExtensionalRetire

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R5Extensional
import Decidable.Equality

%default total
%unbound_implicits off

||| One observed lookup-name decision proves equal replacement lookups at
||| two extensionally related sources. Original present entry is transported;
||| no registry-order equation or assumed target relation is required.
export
0 replaceLookupExtensionalObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (wanted, selected : name) ->
  (old, next : Fiber name key value world error) ->
  (left, right : SystemState name key value world error) ->
  (0 same : RegistryExtensional name key world error value nameEq left right) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry left) = Just old) ->
  (decision : Dec (wanted = selected)) ->
  (0 exact : decEq @{nameEq} wanted selected = decision) ->
  lookupFiber {name} {key} {value} {world} {error} @{nameEq} wanted (replaceBinding @{nameEq} selected next (registry left)) =
  lookupFiber {name} {key} {value} {world} {error} @{nameEq} wanted (replaceBinding @{nameEq} selected next (registry right))
replaceLookupExtensionalObserved nameEq wanted _ old next
  (MkSystemState leftWorld (MkCoeffectContext leftEntries leftUnique))
  (MkSystemState rightWorld (MkCoeffectContext rightEntries rightUnique)) same found (Yes Refl) exact =
    trans (lookupReplaceEntries @{nameEq} wanted old next leftEntries found)
      (sym (lookupReplaceEntries @{nameEq} wanted old next rightEntries
        (trans (sym (extensionalLookup same wanted)) found)))
replaceLookupExtensionalObserved nameEq wanted selected old next left right same found (No different) exact =
  trans (lookupReplaceOther @{nameEq} wanted selected different next (registry left))
    (trans (extensionalLookup same wanted)
      (sym (lookupReplaceOther @{nameEq} wanted selected different next (registry right))))

||| Replacement by the SAME fiber respects extensional states. This is the
||| per-lookup frame used for Retire and other native single-fiber updates.
export
0 replaceExtensional :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (old, next : Fiber name key value world error) ->
  (left, right : SystemState name key value world error) ->
  (0 same : RegistryExtensional name key world error value nameEq left right) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry left) = Just old) ->
  RegistryExtensional name key world error value nameEq
    (MkSystemState (worldState left) (replaceBinding @{nameEq} selected next (registry left)))
    (MkSystemState (worldState right) (replaceBinding @{nameEq} selected next (registry right)))
replaceExtensional nameEq selected old next left right same found =
  MkRegistryExtensional (extensionalWorld same)
    (\wanted => replaceLookupExtensionalObserved nameEq wanted selected old next left right same found
      (decEq @{nameEq} wanted selected) Refl)

||| A checked native step at a new source with its actual produced successor,
||| same rule tag and extensional endpoint. No successful replay is a field
||| of RegistryExtensional itself. This package does not assert its producer.
public export
record CheckedExtensionalStep
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (action : Action name key value world error)
  (source : SystemState name key value world error) (tag : RuleTag)
  (0 originalAfter : SystemState name key value world error) where
  constructor MkCheckedExtensionalStep
  extensionalAfter : SystemState name key value world error
  0 extensionalChecked : checkedApplyAction @{nameEq} @{keyEq} action source =
    Just (tag, extensionalAfter)
  0 extensionalAfterSame : RegistryExtensional name key world error value nameEq
    originalAfter extensionalAfter

||| Original single-constructor Retire view produces the alternate native
||| edge using transported lookup and current validity, then A15 its endpoint.
export
0 retireExtensionalFromView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (afterState, current : SystemState name key value world error) -> (tag : RuleTag) ->
  (0 same : RegistryExtensional name key world error value nameEq (MkSystemState ambient source) current) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  RetireSuccessView name key world error value nameEq actor ambient source tag afterState ->
  CheckedExtensionalStep name key world error value nameEq keyEq (ORetire actor) current tag afterState
retireExtensionalFromView nameEq keyEq actor ambient source _ current _ same valid
  (MkRetireSuccessView old found) =
    MkCheckedExtensionalStep
      (MkSystemState (worldState current) (replaceBinding @{nameEq} actor (retireFiber old) (registry current)))
      (childRetireAtFound nameEq keyEq actor old current
        (trans (sym (extensionalLookup same actor)) found) valid)
      (replaceExtensional nameEq actor old (retireFiber old) (MkSystemState ambient source) current same found)

||| ORetire transport from an ORIGINAL checked edge at an extensionally equal,
||| well-formed source. Same tag and exact pointwise successor are PRODUCED;
||| no target, raw replay, successful alternate edge or endpoint is a premise.
||| This is one action role, not all-action evaluator congruence.
export
0 checkedRetireAcrossExtensional :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (first, afterState, current : SystemState name key value world error) -> (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (ORetire actor) first = Just (tag, afterState)) ->
  (0 same : RegistryExtensional name key world error value nameEq first current) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  CheckedExtensionalStep name key world error value nameEq keyEq (ORetire actor) current tag afterState
checkedRetireAcrossExtensional nameEq keyEq actor (MkSystemState ambient source) afterState current tag checked same valid =
  retireExtensionalFromView nameEq keyEq actor ambient source afterState current tag same valid
    (retireSuccessView nameEq keyEq actor ambient source tag afterState
      (checkedActionProjects nameEq keyEq (ORetire actor) (MkSystemState ambient source) afterState tag checked))

||| Endpoint relation composes for future native normalizer steps. No trace
||| existence, descent, or normalization is inferred from this relational lemma.
export
0 extensionalTransitive :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {0 first, middle, last : SystemState name key value world error} ->
  RegistryExtensional name key world error value nameEq first middle ->
  RegistryExtensional name key world error value nameEq middle last ->
  RegistryExtensional name key world error value nameEq first last
extensionalTransitive left right = MkRegistryExtensional
  (trans (extensionalWorld left) (extensionalWorld right))
  (\wanted => trans (extensionalLookup left wanted) (extensionalLookup right wanted))

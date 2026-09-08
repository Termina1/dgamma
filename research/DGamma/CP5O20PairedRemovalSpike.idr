module DGamma.CP5O20PairedRemovalSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionFrameCore
import DGamma.CP5O20EpisodeSynchronizationSpike
import DGamma.CP5O20PairedPrefixProducerSpike
import DGamma.CP5O20AllNameSynchronizationSpike
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Exact lookup absence from an actual finite-domain exclusion. Observe the
||| primitive lookup explicitly; no computed dependent package is eliminated.
export
0 o20AbsentLookupObserved :
  {key : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) -> (wanted : key) -> (context : CoeffectContext key value) ->
  (Not (Elem wanted (bindingKeys (bindings context)))) ->
  (observed : Maybe (value wanted)) ->
  (lookupBinding @{keyEq} wanted context = observed) ->
  (lookupBinding @{keyEq} wanted context = Nothing)
o20AbsentLookupObserved keyEq wanted context absent Nothing exact = exact
o20AbsentLookupObserved keyEq wanted (MkCoeffectContext entries unique) absent (Just provided) exact =
  void (absent (lookupJustElem @{keyEq} wanted entries provided exact))

||| Removing a binding really makes that lookup absent. Uses the finite
||| unique-key invariant of the executable context, not a control postulate.
export
0 o20DeletedLookupAbsent :
  {key : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) -> (removed : key) -> (context : CoeffectContext key value) ->
  (lookupBinding @{keyEq} removed (deleteBinding @{keyEq} removed context) = Nothing)
o20DeletedLookupAbsent keyEq removed (MkCoeffectContext entries unique) =
  o20AbsentLookupObserved keyEq removed (deleteBinding @{keyEq} removed (MkCoeffectContext entries unique))
    (deletedKeyNotElem @{keyEq} removed entries unique)
    (lookupBinding @{keyEq} removed (deleteBinding @{keyEq} removed (MkCoeffectContext entries unique))) Refl

||| ALL-name deletion control frame. The removed name is absent on both
||| sides; every other name retains the actual pre-cut relation.
export
0 o20PairedDeleteControls :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (renaming : NameBijection name) -> (actor : name) ->
  (leftRegistry, rightRegistry : Registry name key value world error) ->
  ((selected : name) -> MaybeFiberRelatedBy renaming
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected leftRegistry)
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming selected) rightRegistry)) ->
  (selected : name) -> MaybeFiberRelatedBy renaming
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (deleteBinding @{nameEq} actor leftRegistry))
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming selected)
      (deleteBinding @{nameEq} (renameForward renaming actor) rightRegistry))
o20PairedDeleteControls nameEq renaming actor leftRegistry rightRegistry previous selected =
  case decEq @{nameEq} selected actor of
    Yes same => rewrite same in
      rewrite o20DeletedLookupAbsent nameEq actor leftRegistry in
      rewrite o20DeletedLookupAbsent nameEq (renameForward renaming actor) rightRegistry in RenamedAbsent
    No different =>
      rewrite lookupDeleteOther @{nameEq} selected actor different leftRegistry in
      rewrite lookupDeleteOther @{nameEq} (renameForward renaming selected) (renameForward renaming actor)
        (\same => different (trans (sym (renameLeftInverse renaming selected))
          (trans (cong (renameBackward renaming) same) (renameLeftInverse renaming actor)))) rightRegistry in previous selected

||| Removal synchronizes the complete ordered table projection, including the
||| removed table becoming empty. No assumption that removal never occurs.
export
0 o20PairedDeleteEffects :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) -> (actor : name) ->
  (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
  RenamedRuntimeEffects name key world value renaming
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState leftWorld leftRegistry))
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState rightWorld rightRegistry)) ->
  RenamedRuntimeEffects name key world value renaming
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState leftWorld (deleteBinding @{nameEq} actor leftRegistry)))
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState rightWorld (deleteBinding @{nameEq} (renameForward renaming actor) rightRegistry)))
o20PairedDeleteEffects {name} {key} {world} {error} {value} nameEq keyEq renaming actor leftWorld rightWorld leftRegistry rightRegistry paired =
  MkRenamedRuntimeEffects (synchronizedAmbient paired)
    (\selected => trans (sym (tablesExact (projectDeleteEffectFrame nameEq keyEq actor leftWorld leftRegistry) selected))
      (trans (pairedSetTableBindings name key world value nameEq renaming actor emptyContext emptyContext Refl
        (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState leftWorld leftRegistry))
        (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState rightWorld rightRegistry)) paired selected)
        (tablesExact (projectDeleteEffectFrame nameEq keyEq (renameForward renaming actor) rightWorld rightRegistry) (renameForward renaming selected))))

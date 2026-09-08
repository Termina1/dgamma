module DGamma.CP5O20PairedRemovalSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionFrameCore
import DGamma.CP5O20EpisodeSynchronizationSpike
import DGamma.CP5O20PairedPrefixProducerSpike
import DGamma.CP5O20PairedExecutionSpike
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

||| Actual checked Remove successor, roots OR children. Both native evaluator
||| equations pin the physical destinations; effects and all controls are
||| derived. This neither suppresses Remove nor changes the earlier family.
export
0 o20PairedObservedRemoveCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) -> (actor : name) ->
  (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (ORemove actor) (MkSystemState leftWorld leftRegistry) =
    Just (ORemoveTag, MkSystemState leftWorld (deleteBinding @{nameEq} actor leftRegistry))) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (ORemove (renameForward renaming actor)) (MkSystemState rightWorld rightRegistry) =
    Just (ORemoveTag, MkSystemState rightWorld (deleteBinding @{nameEq} (renameForward renaming actor) rightRegistry))) ->
  O20AllNameCut name key world error value nameEq renaming (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry) ->
  O20AllNameCut name key world error value nameEq renaming
    (MkSystemState leftWorld (deleteBinding @{nameEq} actor leftRegistry))
    (MkSystemState rightWorld (deleteBinding @{nameEq} (renameForward renaming actor) rightRegistry))
o20PairedObservedRemoveCut nameEq keyEq renaming actor leftWorld rightWorld leftRegistry rightRegistry leftChecked rightChecked paired =
  MkO20AllNameCut
    (o20PairedDeleteEffects nameEq keyEq renaming actor leftWorld rightWorld leftRegistry rightRegistry (allNameEffects paired))
    (o20PairedDeleteControls nameEq renaming actor leftRegistry rightRegistry (allNameControls paired))

||| Conservative operational extension: old actual stages plus ACTUAL paired
||| Remove steps at their physical cuts. No conclusion or preservation
||| callback is stored. Failure/diversion and canonical extraction remain open.
public export
data O20PairedExecutionWithRemoval :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) ->
  (leftBefore, rightBefore, leftAfter, rightAfter : SystemState name key value world error) -> Type where
  RemovalExecutionTail :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} -> {renaming : NameBijection name} ->
    {leftBefore, rightBefore, leftAfter, rightAfter : SystemState name key value world error} ->
    (0 tail : O20PairedExecution name key world error value nameEq keyEq renaming leftBefore rightBefore leftAfter rightAfter) ->
    O20PairedExecutionWithRemoval name key world error value nameEq keyEq renaming leftBefore rightBefore leftAfter rightAfter
  RemovalExecutionStage :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} -> {renaming : NameBijection name} ->
    {leftBefore, rightBefore, leftMiddle, rightMiddle, leftAfter, rightAfter : SystemState name key value world error} ->
    (0 stage : O20PairedStage name key world error value nameEq keyEq renaming leftBefore rightBefore leftMiddle rightMiddle) ->
    (0 later : O20PairedExecutionWithRemoval name key world error value nameEq keyEq renaming leftMiddle rightMiddle leftAfter rightAfter) ->
    O20PairedExecutionWithRemoval name key world error value nameEq keyEq renaming leftBefore rightBefore leftAfter rightAfter
  RemovalExecutionRemove :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) -> (actor : name) ->
    (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
    {leftAfter, rightAfter : SystemState name key value world error} ->
    (0 leftChecked : checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (ORemove actor) (MkSystemState leftWorld leftRegistry) =
      Just (ORemoveTag, MkSystemState leftWorld (deleteBinding @{nameEq} actor leftRegistry))) ->
    (0 rightChecked : checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (ORemove (renameForward renaming actor)) (MkSystemState rightWorld rightRegistry) =
      Just (ORemoveTag, MkSystemState rightWorld (deleteBinding @{nameEq} (renameForward renaming actor) rightRegistry))) ->
    (0 later : O20PairedExecutionWithRemoval name key world error value nameEq keyEq renaming
      (MkSystemState leftWorld (deleteBinding @{nameEq} actor leftRegistry))
      (MkSystemState rightWorld (deleteBinding @{nameEq} (renameForward renaming actor) rightRegistry)) leftAfter rightAfter) ->
    O20PairedExecutionWithRemoval name key world error value nameEq keyEq renaming
      (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry) leftAfter rightAfter

||| Structural finite induction, now including Remove. Conditional on genuine
||| paired execution data; NOT extraction from the canonical pair.
export
0 o20PairedRemovalExecutionCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {renaming : NameBijection name} ->
  {leftBefore, rightBefore, leftAfter, rightAfter : SystemState name key value world error} ->
  O20PairedExecutionWithRemoval name key world error value nameEq keyEq renaming leftBefore rightBefore leftAfter rightAfter ->
  O20AllNameCut name key world error value nameEq renaming leftBefore rightBefore ->
  O20AllNameCut name key world error value nameEq renaming leftAfter rightAfter
o20PairedRemovalExecutionCut {nameEq} {keyEq} {renaming} (RemovalExecutionTail tail) paired = o20PairedExecutionCut nameEq keyEq renaming tail paired
o20PairedRemovalExecutionCut {nameEq} {keyEq} {renaming} (RemovalExecutionStage stage later) paired =
  o20PairedRemovalExecutionCut later (o20PairedStageCut nameEq keyEq renaming stage paired)
o20PairedRemovalExecutionCut (RemovalExecutionRemove nameEq keyEq renaming actor leftWorld rightWorld leftRegistry rightRegistry leftChecked rightChecked later) paired =
  o20PairedRemovalExecutionCut later
    (o20PairedObservedRemoveCut nameEq keyEq renaming actor leftWorld rightWorld leftRegistry rightRegistry leftChecked rightChecked paired)

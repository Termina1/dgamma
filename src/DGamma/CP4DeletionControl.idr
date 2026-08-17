module DGamma.CP4DeletionControl

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionControlCore
import DGamma.CP4DeletionControlBegin
import DGamma.CP4DeletionControlStable
import DGamma.CP4DeletionControlAdvance
import DGamma.CP4DeletionControlUnload
import Decidable.Equality

%default total

0 falseNotTrue : False = True -> Void
falseNotTrue Refl impossible

||| Exhaustive raw lifecycle applicability after deleting one distinct Inactive
||| episode residue. L-Advance additionally consumes Definition-58 validity to
||| ensure its committed capability cannot name the deleted entry.
public export
0 lifecycleApplicableAfterInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  isLifecycleAction action = True ->
  (removed : name) -> Not (actionOwner action = removed) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (removedComponent : Component key value world error) ->
  (removedParent : Parent name) -> (removedRetired : Bool) ->
  (removedTable : OwnedTable key value
    (componentProvisions removedComponent)) ->
  (removedOutcome : Maybe error) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} removed fibers = Just
    (MkFiber removedComponent removedParent removedRetired removedTable
      (Inactive removedOutcome)) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkSystemState ambient fibers) = True ->
  {tag : RuleTag} ->
  {afterState : SystemState name key value world error} ->
  applyAction @{nameEq} @{keyEq} action (MkSystemState ambient fibers) =
    Just (tag, afterState) ->
  RawActionResult name key world error value nameEq keyEq action
    (MkSystemState ambient (deleteBinding @{nameEq} removed fibers))
lifecycleApplicableAfterInactiveDelete nameEq keyEq
  (OInsert inserted parent component) lifecycle removed distinct ambient
  fibers removedComponent removedParent removedRetired removedTable removedOutcome
  removedFound wellFormed raw = void (falseNotTrue lifecycle)
lifecycleApplicableAfterInactiveDelete nameEq keyEq (ORetire selected) lifecycle
  removed distinct ambient fibers removedComponent removedParent
  removedRetired removedTable removedOutcome removedFound wellFormed raw =
    void (falseNotTrue lifecycle)
lifecycleApplicableAfterInactiveDelete nameEq keyEq (ORemove selected) lifecycle
  removed distinct ambient fibers removedComponent removedParent
  removedRetired removedTable removedOutcome removedFound wellFormed raw =
    void (falseNotTrue lifecycle)
lifecycleApplicableAfterInactiveDelete nameEq keyEq (LBegin selected) lifecycle
  removed distinct ambient fibers removedComponent removedParent
  removedRetired removedTable removedOutcome removedFound wellFormed raw =
    beginApplicableAfterInactiveDelete nameEq keyEq selected removed distinct ambient
      fibers removedComponent removedParent removedRetired removedTable removedOutcome
      removedFound raw
lifecycleApplicableAfterInactiveDelete nameEq keyEq (LAdvance selected) lifecycle
  removed distinct ambient fibers removedComponent removedParent
  removedRetired removedTable removedOutcome removedFound wellFormed raw =
    advanceApplicableAfterInactiveDelete nameEq keyEq selected removed distinct
      ambient fibers removedComponent removedParent removedRetired removedTable
      removedOutcome removedFound wellFormed raw
lifecycleApplicableAfterInactiveDelete nameEq keyEq (LDivert selected) lifecycle
  removed distinct ambient fibers removedComponent removedParent
  removedRetired removedTable removedOutcome removedFound wellFormed raw =
    divertApplicableAfterInactiveDelete nameEq keyEq selected removed distinct
      ambient fibers removedComponent removedParent removedRetired removedTable
      removedOutcome removedFound raw
lifecycleApplicableAfterInactiveDelete nameEq keyEq (LLeave selected) lifecycle
  removed distinct ambient fibers removedComponent removedParent
  removedRetired removedTable removedOutcome removedFound wellFormed raw =
    leaveApplicableAfterInactiveDelete nameEq keyEq selected removed distinct ambient
      fibers removedComponent removedParent removedRetired removedTable removedOutcome
      removedFound raw
lifecycleApplicableAfterInactiveDelete nameEq keyEq (LUnload selected) lifecycle
  removed distinct ambient fibers removedComponent removedParent
  removedRetired removedTable removedOutcome removedFound wellFormed raw =
    unloadApplicableAfterInactiveDelete nameEq keyEq selected removed distinct
      ambient fibers removedComponent removedParent removedRetired removedTable
      removedOutcome removedFound raw

0 checkedFromRawResult :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (before : SystemState name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} before = True ->
  RawActionResult name key world error value nameEq keyEq action before ->
  TransitionResult before
checkedFromRawResult nameEq keyEq action before sourceWellFormed
  (MkRawActionResult tag afterState raw) =
    let targetWellFormed = preservationTheoremProof nameEq keyEq action before
          afterState tag sourceWellFormed raw
        checked : (checkedApplyAction @{nameEq} @{keyEq} action before =
          Just (tag, afterState))
        checked = rewrite raw in rewrite targetWellFormed in Refl
    in MkTransitionResult afterState tag
      (Fired nameEq keyEq action tag checked)

||| Checked control-guard companion used by Lemma 72 suffix replay. Under the
||| Lemma-57 leaf condition, deleting a distinct Inactive residue preserves
||| Definition-58 and every surviving lifecycle action still fires.
public export
0 checkedLifecycleAfterInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  isLifecycleAction action = True ->
  (removed : name) -> Not (actionOwner action = removed) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (removedComponent : Component key value world error) ->
  (removedParent : Parent name) -> (removedRetired : Bool) ->
  (removedTable : OwnedTable key value
    (componentProvisions removedComponent)) ->
  (removedOutcome : Maybe error) ->
  (removedFound : lookupFiber @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} removed fibers = Just
      (MkFiber removedComponent removedParent removedRetired removedTable
        (Inactive removedOutcome))) ->
  hasChild @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} removed fibers = False ->
  (sourceWellFormed : registryWellFormed @{nameEq} @{keyEq}
    {name = name} {key = key} {value = value} {world = world} {error = error}
    (MkSystemState ambient fibers) = True) ->
  {tag : RuleTag} ->
  {afterState : SystemState name key value world error} ->
  checkedApplyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} action
    (MkSystemState ambient fibers) = Just (tag, afterState) ->
  TransitionResult {name = name} {key = key} {value = value} {world = world}
    {error = error}
    (MkSystemState ambient (deleteBinding @{nameEq} removed fibers))
checkedLifecycleAfterInactiveDelete {name} {key} {world} {error} {value}
  nameEq keyEq action lifecycle removed distinct ambient fibers
  removedComponent removedParent removedRetired removedTable removedOutcome
  removedFound noChild sourceWellFormed checked =
    let raw = checkedActionProjects nameEq keyEq action
          (MkSystemState ambient fibers) _ _ checked
        replayRaw = lifecycleApplicableAfterInactiveDelete nameEq keyEq action
          lifecycle removed distinct ambient fibers removedComponent
          removedParent removedRetired removedTable removedOutcome removedFound
          sourceWellFormed raw
        replayWellFormed = registryWellFormedInactiveDelete nameEq keyEq ambient
          removed removedComponent removedParent removedRetired removedTable
          removedOutcome fibers removedFound noChild sourceWellFormed
    in checkedFromRawResult nameEq keyEq action
      (MkSystemState ambient (deleteBinding @{nameEq} removed fibers))
      replayWellFormed replayRaw

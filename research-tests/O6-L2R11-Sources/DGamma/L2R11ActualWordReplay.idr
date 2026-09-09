module DGamma.L2R11ActualWordReplay

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2CheckedSnapshot
import DGamma.L2R2ForeignReplay
import DGamma.L2R11WordInventory
import Prelude.Types
import Prelude.Interfaces
import Data.List
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| NEW restricted-domain fold, not the old all-action single theorem.
||| The callback is needed ONLY for kinds in this native trace's ACTUAL word.
||| Every head membership and suffix-domain inclusion is produced here.
||| The callback still needs a concrete native square dispatcher; this fold
||| does not assert that the lifecycle/orchestration assembly exists.
export
0 replayActualWordCPS :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) ->
  (fiber : Fiber name key value world error) ->
  (first, finalState : SystemState name key value world error) ->
  (trace : Transitions first finalState) -> ForeignChildRun nameEq keyEq child trace ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry first) = Just fiber) ->
  (0 originalValid : registryWellFormed @{nameEq} @{keyEq} first = True) ->
  (current : SystemState name key value world error) ->
  (0 currentValid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 currentSame : runtimeSnapshot current = runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState (worldState first) (replaceBinding @{nameEq} child (retireFiber fiber) (registry first)))) ->
  (0 single : (before, afterState, replaySource : SystemState name key value world error) ->
    (action : Action name key value world error) -> (tag : RuleTag) ->
    (0 inActualWord : wordActionInventory (replayActionWord trace) (actionKindCode action) = True) ->
    checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
    Not (child = actionOwner action) ->
    lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry before) = Just fiber ->
    registryWellFormed @{nameEq} @{keyEq} before = True ->
    registryWellFormed @{nameEq} @{keyEq} replaySource = True ->
    runtimeSnapshot replaySource = runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState before) (replaceBinding @{nameEq} child (retireFiber fiber) (registry before))) ->
    CheckedSnapshotStep name key world error value nameEq keyEq action replaySource tag
      (runtimeSnapshot {name} {key} {value} {world} {error}
        (MkSystemState (worldState afterState) (replaceBinding @{nameEq} child (retireFiber fiber) (registry afterState))))) ->
  (0 answer : Type) ->
  (0 done : (target : SystemState name key value world error) ->
    (replayed : Transitions current target) ->
    transitionCount replayed = transitionCount trace ->
    runtimeSnapshot target = runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState finalState) (replaceBinding @{nameEq} child (retireFiber fiber) (registry finalState))) -> answer) ->
  answer
replayActualWordCPS nameEq keyEq child fiber _ _ _ ForeignChildEnd
  found originalValid current currentValid currentSame single answer done =
    done current NoTransitions Refl currentSame
replayActualWordCPS nameEq keyEq child fiber first finalState _
  (ForeignChildStep {middle} action tag checked rest distinct tail)
  found originalValid current currentValid currentSame single answer done =
    replayActualWordCPS nameEq keyEq child fiber middle finalState rest tail
      (trans (childForeignLookupFrame nameEq keyEq child action tag checked distinct) found)
      (checkedActionTargetValid nameEq keyEq action first middle tag checked)
      (snapshotAfter (single first middle current action tag (wordInventoryHead action (replayActionWord rest)) checked distinct found originalValid currentValid currentSame))
      (checkedActionTargetValid nameEq keyEq action current
        (snapshotAfter (single first middle current action tag (wordInventoryHead action (replayActionWord rest)) checked distinct found originalValid currentValid currentSame)) tag
        (snapshotChecked (single first middle current action tag (wordInventoryHead action (replayActionWord rest)) checked distinct found originalValid currentValid currentSame)))
      (snapshotExact (single first middle current action tag (wordInventoryHead action (replayActionWord rest)) checked distinct found originalValid currentValid currentSame))
      (\before, afterState, replaySource, selected, selectedTag, inTail =>
        single before afterState replaySource selected selectedTag
          (wordInventoryTail action (replayActionWord rest) (actionKindCode selected) inTail)) answer
      (\target, replayed, count, same => done target
        (MoreTransitions (Fired {before = current}
          {afterState = snapshotAfter (single first middle current action tag (wordInventoryHead action (replayActionWord rest)) checked distinct found originalValid currentValid currentSame)}
          nameEq keyEq action tag
          (snapshotChecked (single first middle current action tag (wordInventoryHead action (replayActionWord rest)) checked distinct found originalValid currentValid currentSame))) replayed)
        (cong S count) same)


||| NEW whole-run replay with actual-word-restricted single. The unchanged
||| L2R2 RetirementReplay conclusion includes early retirement, exact native
||| count and snapshot-equal endpoint. This is a PROVED fold, conditional on
||| the displayed per-kind dispatcher, not its lifecycle/frame construction.
export
0 replayOverActualWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) ->
  (fiber : Fiber name key value world error) ->
  (first, finalState : SystemState name key value world error) ->
  (trace : Transitions first finalState) -> (foreign : ForeignChildRun nameEq keyEq child trace) ->
  (0 foundFinal : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry finalState) = Just fiber) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} first = True) ->
  (0 single : (before, afterState, replaySource : SystemState name key value world error) ->
    (action : Action name key value world error) -> (tag : RuleTag) ->
    (0 inActualWord : wordActionInventory (replayActionWord trace) (actionKindCode action) = True) ->
    checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
    Not (child = actionOwner action) ->
    lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry before) = Just fiber ->
    registryWellFormed @{nameEq} @{keyEq} before = True ->
    registryWellFormed @{nameEq} @{keyEq} replaySource = True ->
    runtimeSnapshot replaySource = runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState before) (replaceBinding @{nameEq} child (retireFiber fiber) (registry before))) ->
    CheckedSnapshotStep name key world error value nameEq keyEq action replaySource tag
      (runtimeSnapshot {name} {key} {value} {world} {error}
        (MkSystemState (worldState afterState) (replaceBinding @{nameEq} child (retireFiber fiber) (registry afterState))))) ->
  RetirementReplay name key world error value nameEq child fiber trace
replayOverActualWord {name} {key} {world} {error} {value}
  nameEq keyEq child fiber first finalState trace foreign foundFinal valid single =
  replayActualWordCPS nameEq keyEq child fiber first finalState trace foreign
    (trans (sym (foreignChildRunLookup nameEq keyEq child trace foreign)) foundFinal) valid
    (MkSystemState (worldState first) (replaceBinding @{nameEq} child (retireFiber fiber) (registry first)))
    (checkedActionTargetValid nameEq keyEq (ORetire child) first
      (MkSystemState (worldState first) (replaceBinding @{nameEq} child (retireFiber fiber) (registry first))) ORetireTag
      (childRetireBeforeForeignRun nameEq keyEq child fiber first finalState trace foreign foundFinal valid))
    Refl single (RetirementReplay name key world error value nameEq child fiber trace)
    (\target, replayed, count, same => MkRetirementReplay target
      (MoreTransitions (Fired {before = first}
        {afterState = MkSystemState (worldState first) (replaceBinding @{nameEq} child (retireFiber fiber) (registry first))}
        nameEq keyEq (ORetire child) ORetireTag
        (childRetireBeforeForeignRun nameEq keyEq child fiber first finalState trace foreign foundFinal valid)) replayed)
      (cong S count) same)

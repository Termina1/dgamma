module DGamma.L2R12ValidWordFold

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

||| Strengthen the SAME actual-word-restricted CPS induction by retaining
||| its already-produced target validity for native suffix splicing. This
||| avoids assuming validity of an opaque RetirementReplay endpoint.
export
0 replayActualWordValidCPS :
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
      (MkSystemState (worldState finalState) (replaceBinding @{nameEq} child (retireFiber fiber) (registry finalState))) ->
    registryWellFormed @{nameEq} @{keyEq} target = True -> answer) ->
  answer
replayActualWordValidCPS nameEq keyEq child fiber _ _ _ ForeignChildEnd
  found originalValid current currentValid currentSame single answer done =
    done current NoTransitions Refl currentSame currentValid
replayActualWordValidCPS nameEq keyEq child fiber first finalState _
  (ForeignChildStep {middle} action tag checked rest distinct tail)
  found originalValid current currentValid currentSame single answer done =
    replayActualWordValidCPS nameEq keyEq child fiber middle finalState rest tail
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
      (\target, replayed, count, same, targetValid => done target
        (MoreTransitions (Fired {before = current}
          {afterState = snapshotAfter (single first middle current action tag (wordInventoryHead action (replayActionWord rest)) checked distinct found originalValid currentValid currentSame)}
          nameEq keyEq action tag
          (snapshotChecked (single first middle current action tag (wordInventoryHead action (replayActionWord rest)) checked distinct found originalValid currentValid currentSame))) replayed)
        (cong S count) same targetValid)

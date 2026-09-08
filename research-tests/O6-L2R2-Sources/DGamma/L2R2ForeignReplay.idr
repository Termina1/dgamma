module DGamma.L2R2ForeignReplay

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2CheckedSnapshot
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| A genuinely replayed native trace, including early child retirement and
||| every foreign edge. The runtime endpoint equals the original endpoint
||| after child retirement at the world/ordered-binding level. This result
||| package alone supplies no commutation or normalization oracle.
public export
record RetirementReplay
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (child : name)
  (fiber : Fiber name key value world error)
  {first, finalState : SystemState name key value world error}
  (original : Transitions first finalState) where
  constructor MkRetirementReplay
  relocatedFinal : SystemState name key value world error
  relocatedTrace : Transitions first relocatedFinal
  0 relocatedCount : transitionCount relocatedTrace = S (transitionCount original)
  0 relocatedSnapshot : runtimeSnapshot relocatedFinal =
    runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState finalState)
        (replaceBinding @{nameEq} child (retireFiber fiber) (registry finalState)))

||| Structural native replay of a whole ForeignChildRun, in continuation form
||| to avoid computed existential eliminations. The EXPLICIT per-edge callback
||| is the missing complete square dispatcher plus snapshot transport: it must
||| supply one checked action, not a suffix replay. This proves the fold only;
||| L2R2 does NOT provide that callback for all foreign action kinds.
export
0 foreignRetireReplayCPS :
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
foreignRetireReplayCPS nameEq keyEq child fiber _ _ _ ForeignChildEnd
  found originalValid current currentValid currentSame single answer done =
    done current NoTransitions Refl currentSame
foreignRetireReplayCPS nameEq keyEq child fiber first finalState _
  (ForeignChildStep {middle} action tag checked rest distinct tail)
  found originalValid current currentValid currentSame single answer done =
    foreignRetireReplayCPS nameEq keyEq child fiber middle finalState rest tail
      (trans (childForeignLookupFrame nameEq keyEq child action tag checked distinct) found)
      (checkedActionTargetValid nameEq keyEq action first middle tag checked)
      (snapshotAfter (single first middle current action tag checked distinct found originalValid currentValid currentSame))
      (checkedActionTargetValid nameEq keyEq action current
        (snapshotAfter (single first middle current action tag checked distinct found originalValid currentValid currentSame)) tag
        (snapshotChecked (single first middle current action tag checked distinct found originalValid currentValid currentSame)))
      (snapshotExact (single first middle current action tag checked distinct found originalValid currentValid currentSame))
      single answer
      (\target, replayed, count, same => done target
        (MoreTransitions (Fired {before = current}
          {afterState = snapshotAfter (single first middle current action tag checked distinct found originalValid currentValid currentSame)}
          nameEq keyEq action tag
          (snapshotChecked (single first middle current action tag checked distinct found originalValid currentValid currentSame))) replayed)
        (cong S count) same)

||| Combine L2R1 B23 early applicability with the native replay fold. This is
||| MORE than applicability: the output contains the full relocated trace and
||| exact count/endpoint theorem. It remains conditional on the displayed
||| LOCAL step dispatcher; missing Retire square kinds are not discharged.
export
0 replayRetirementBeforeForeignRun :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) ->
  (fiber : Fiber name key value world error) ->
  (first, finalState : SystemState name key value world error) ->
  (trace : Transitions first finalState) -> (foreign : ForeignChildRun nameEq keyEq child trace) ->
  (0 foundFinal : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry finalState) = Just fiber) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} first = True) ->
  (0 single : (before, afterState, replaySource : SystemState name key value world error) ->
    (action : Action name key value world error) -> (tag : RuleTag) ->
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
replayRetirementBeforeForeignRun {name} {key} {world} {error} {value}
  nameEq keyEq child fiber first finalState trace foreign foundFinal valid single =
  foreignRetireReplayCPS nameEq keyEq child fiber first finalState trace foreign
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

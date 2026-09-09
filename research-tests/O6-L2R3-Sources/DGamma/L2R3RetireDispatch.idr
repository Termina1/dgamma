module DGamma.L2R3RetireDispatch

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2CheckedSnapshot
import DGamma.L2R2RetireSquare
import DGamma.L2R2RetireInsert
import Decidable.Equality

%default total
%unbound_implicits off

||| Single-role observation bridge, not a dispatcher oracle: transport a real
||| child-retirement square's replay edge to an arbitrary well-formed runtime-
||| equal retired source. Early source equality follows from native ORetire
||| determinism at the supplied lookup, not projected dependent observations.
export
0 retireSquareReplayObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent : name) ->
  (fiber : Fiber name key value world error) ->
  (first, middle, finalState, current : SystemState name key value world error) ->
  (left : Transition first middle) -> (right : Transition middle finalState) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry first) = Just fiber) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} first = True) ->
  (0 currentValid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 currentSame : runtimeSnapshot current = runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState (worldState first) (replaceBinding @{nameEq} child (retireFiber fiber) (registry first)))) ->
  (square : ChildRetireSnapshotExchange name key world error value nameEq keyEq child parent left right) ->
  CheckedSnapshotStep name key world error value nameEq keyEq (transitionAction left) current
    (transitionTag left) (runtimeSnapshot finalState)
retireSquareReplayObserved nameEq keyEq child parent fiber first middle finalState current left right
  found valid currentValid currentSame square =
  replace {p = \expected => CheckedSnapshotStep name key world error value nameEq keyEq
    (transitionAction left) current (transitionTag left) expected}
    (sym (retireReplaySnapshot square))
    (checkedAcrossSnapshot nameEq keyEq (transitionAction left) (transitionTag left)
      (retireEarlyState square) (retireReplayState square) current (retireReplayChecked square)
      (trans (cong runtimeSnapshot (cong snd (justInjective
        (trans (sym (retireEarlyChecked square))
          (childRetireAtFound nameEq keyEq child fiber first found valid))))) (sym currentSame)) currentValid)

||| ROOT OInsert branch of the requested local ForeignReplay dispatcher.
||| Given ONLY the original checked root insertion, an actual own-child lookup,
||| and well-formed snapshot-equal retired source, construct its checked replay.
||| Late retirement and both alternate square edges are derived, never inputs.
||| Other action roles are not discharged by this branch.
export
0 replayRootAfterRetirement :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, root : name) ->
  (fiber : Fiber name key value world error) -> (component : Component key value world error) ->
  (first, afterState, current : SystemState name key value world error) -> (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (OInsert root Root component) first = Just (tag, afterState)) ->
  (0 distinct : Not (child = root)) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry first) = Just fiber) ->
  (0 own : fiberParent fiber = ChildOf parent) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} first = True) ->
  (0 currentValid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 currentSame : runtimeSnapshot current = runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState (worldState first) (replaceBinding @{nameEq} child (retireFiber fiber) (registry first)))) ->
  CheckedSnapshotStep name key world error value nameEq keyEq (OInsert root Root component) current tag
    (runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState afterState) (replaceBinding @{nameEq} child (retireFiber fiber) (registry afterState))))
replayRootAfterRetirement nameEq keyEq child parent root fiber component first afterState current tag
  checked distinct found own valid currentValid currentSame =
  retireSquareReplayObserved nameEq keyEq child parent fiber first afterState
    (MkSystemState (worldState afterState) (replaceBinding @{nameEq} child (retireFiber fiber) (registry afterState))) current
    (Fired {before = first} {afterState = afterState} nameEq keyEq (OInsert root Root component) tag checked)
    (Fired {before = afterState} {afterState = (MkSystemState (worldState afterState) (replaceBinding @{nameEq} child (retireFiber fiber) (registry afterState)))} nameEq keyEq (ORetire child) ORetireTag (childRetireAtFound nameEq keyEq child fiber afterState (trans (childForeignLookupFrame nameEq keyEq child (OInsert root Root component) tag checked distinct) found) (checkedActionTargetValid nameEq keyEq (OInsert root Root component) first afterState tag checked)))
    found valid currentValid currentSame
    (commuteRootInsertChildRetire nameEq keyEq child parent root fiber component first afterState
      (MkSystemState (worldState afterState) (replaceBinding @{nameEq} child (retireFiber fiber) (registry afterState))) tag
      found own distinct valid checked (childRetireAtFound nameEq keyEq child fiber afterState (trans (childForeignLookupFrame nameEq keyEq child (OInsert root Root component) tag checked distinct) found) (checkedActionTargetValid nameEq keyEq (OInsert root Root component) first afterState tag checked)))

module DGamma.L2R4RetireReplay

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2CheckedSnapshot
import DGamma.L2R4ReplaceCommute
import Decidable.Equality

%default total
%unbound_implicits off

||| A foreign runtime replacement commutes with early child retirement on
||| world plus exact ordered bindings. No intrinsic certificate equality.
export
0 retirementUpdateSnapshot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (child, actor : name) ->
  (fiber, nextActor : Fiber name key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (0 distinct : Not (child = actor)) ->
  runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState ambient (replaceBinding @{nameEq} actor nextActor
      (replaceBinding @{nameEq} child (retireFiber fiber) source))) =
  runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber fiber)
      (replaceBinding @{nameEq} actor nextActor source)))
retirementUpdateSnapshot nameEq child actor fiber nextActor ambient (MkCoeffectContext entries unique) distinct =
  cong (MkRuntimeSnapshot ambient)
    (replaceEntriesCommute nameEq actor child nextActor (retireFiber fiber) entries (\same => distinct (sym same)))

||| A single original RetireSuccessView supplies the actual actor fiber and
||| endpoint. Native replay, validity and snapshot are all derived here.
export
0 replayRetireFromView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, actor : name) ->
  (fiber : Fiber name key value world error) -> (ambient : world) ->
  (source : Registry name key value world error) ->
  (afterState, current : SystemState name key value world error) -> (tag : RuleTag) ->
  (0 distinct : Not (child = actor)) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child source = Just fiber) ->
  (0 valid : registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (MkSystemState ambient source) = True) ->
  (0 currentValid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 currentSame : runtimeSnapshot current = runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber fiber) source))) ->
  RetireSuccessView name key world error value nameEq actor ambient source tag afterState ->
  CheckedSnapshotStep name key world error value nameEq keyEq (ORetire actor) current tag
    (runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState afterState) (replaceBinding @{nameEq} child (retireFiber fiber) (registry afterState))))
replayRetireFromView nameEq keyEq child actor fiber ambient source _ current _ distinct found valid currentValid currentSame
  (MkRetireSuccessView actorFiber actorFound) =
    replace {p = \expected => CheckedSnapshotStep name key world error value nameEq keyEq (ORetire actor) current ORetireTag expected}
      (retirementUpdateSnapshot nameEq child actor fiber (retireFiber actorFiber) ambient source distinct)
      (checkedAcrossSnapshot nameEq keyEq (ORetire actor) ORetireTag
        (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber fiber) source))
        (MkSystemState ambient (replaceBinding @{nameEq} actor (retireFiber actorFiber)
          (replaceBinding @{nameEq} child (retireFiber fiber) source))) current
        (childRetireAtFound nameEq keyEq actor actorFiber
          (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber fiber) source))
          (trans (lookupReplaceOther @{nameEq} actor child (\same => distinct (sym same)) (retireFiber fiber) source) actorFound)
          (registryWellFormedRetire nameEq keyEq ambient child fiber source found valid))
        (sym currentSame) currentValid)

||| FOREIGN ORetire local dispatcher role at arbitrary well-formed snapshot-
||| equal retired sources. ONLY the original checked edge is operational input.
||| No ownership metadata, alternate guard or alternate snapshot premise.
export
0 replayRetireAfterRetirement :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, actor : name) ->
  (fiber : Fiber name key value world error) ->
  (first, afterState, current : SystemState name key value world error) -> (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (ORetire actor) first = Just (tag, afterState)) ->
  (0 distinct : Not (child = actor)) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry first) = Just fiber) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} first = True) ->
  (0 currentValid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 currentSame : runtimeSnapshot current = runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState (worldState first) (replaceBinding @{nameEq} child (retireFiber fiber) (registry first)))) ->
  CheckedSnapshotStep name key world error value nameEq keyEq (ORetire actor) current tag
    (runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState afterState) (replaceBinding @{nameEq} child (retireFiber fiber) (registry afterState))))
replayRetireAfterRetirement nameEq keyEq child actor fiber (MkSystemState ambient source) afterState current tag
  checked distinct found valid currentValid currentSame =
    replayRetireFromView nameEq keyEq child actor fiber ambient source afterState current tag
      distinct found valid currentValid currentSame
      (retireSuccessView nameEq keyEq actor ambient source tag afterState
        (checkedActionProjects nameEq keyEq (ORetire actor) (MkSystemState ambient source) afterState tag checked))

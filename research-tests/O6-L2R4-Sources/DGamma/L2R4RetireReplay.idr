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

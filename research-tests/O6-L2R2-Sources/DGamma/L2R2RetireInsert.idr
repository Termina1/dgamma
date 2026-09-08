module DGamma.L2R2RetireInsert

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4ProgressNoDeadlock
import DGamma.L2R2CheckedSnapshot
import DGamma.L2R2RetireSquare
import DGamma.CP5L2R1ChildRelocation
import Decidable.Equality
import Data.List.Elem

%default total
%unbound_implicits off

||| Root insertion's raw runtime observation at an actual absent lookup and
||| native declaration guard. No equality of erased uniqueness proofs is asserted.
||| Auxiliary evaluator evidence, not a CP3 placement copy or complete square.
export
0 rootInsertAtAbsence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (root : name) ->
  (component : Component key value world error) -> (ambient : world) ->
  (fibers : Registry name key value world error) ->
  (0 absent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} root fibers = Nothing) ->
  (0 free : provisionsDisjointFrom {name} {key} {value} {world} {error} @{keyEq}
    (componentProvisions component) (bindings fibers) = True) ->
  observeActionResult (applyAction @{nameEq} @{keyEq} (OInsert root Root component)
    (MkSystemState ambient fibers)) =
    Just (OInsertTag, MkRuntimeSnapshot ambient
      (Bind root (freshFiber component Root) :: bindings fibers))
rootInsertAtAbsence nameEq keyEq root component ambient (MkCoeffectContext entries unique) absent free =
  rewrite free in rewrite absent in Refl

||| Produce an actual checked root insertion from native freshness, declaration
||| availability, and source well-formedness. The returned state has precisely
||| the inserted world/ordered bindings, but owns its uniqueness certificate.
export
0 checkedRootInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (root : name) ->
  (component : Component key value world error) -> (ambient : world) ->
  (fibers : Registry name key value world error) ->
  (0 absent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} root fibers = Nothing) ->
  (0 free : provisionsDisjointFrom {name} {key} {value} {world} {error} @{keyEq}
    (componentProvisions component) (bindings fibers) = True) ->
  (0 valid : registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (MkSystemState ambient fibers) = True) ->
  CheckedSnapshotStep name key world error value nameEq keyEq (OInsert root Root component)
    (MkSystemState ambient fibers) OInsertTag
    (MkRuntimeSnapshot ambient (Bind root (freshFiber component Root) :: bindings fibers))
checkedRootInsert nameEq keyEq root component ambient fibers absent free valid =
  checkedSnapshotObserved nameEq keyEq (OInsert root Root component) (MkSystemState ambient fibers)
    OInsertTag (MkRuntimeSnapshot ambient (Bind root (freshFiber component Root) :: bindings fibers))
    (applyAction @{nameEq} @{keyEq} (OInsert root Root component) (MkSystemState ambient fibers)) Refl
    (rootInsertAtAbsence nameEq keyEq root component ambient fibers absent free) valid

||| One observed name decision proves that replacing a different binding
||| leaves an inserted head untouched. This compares ordered entries only.
export
0 replaceOtherHeadObserved :
  {key : Type} -> {item : key -> Type} ->
  (keyEq : DecEq key) -> (changed, current : key) ->
  (next : item changed) -> (old : item current) ->
  (rest : List (Binding key item)) ->
  (decision : Dec (changed = current)) ->
  (0 exact : decEq @{keyEq} changed current = decision) ->
  (0 distinct : Not (changed = current)) ->
  replaceEntries @{keyEq} changed next (Bind current old :: rest) =
    Bind current old :: replaceEntries @{keyEq} changed next rest
replaceOtherHeadObserved keyEq changed current next old rest (Yes same) exact distinct =
  void (distinct same)
replaceOtherHeadObserved keyEq changed current next old rest (No different) exact distinct =
  rewrite exact in Refl

||| Exact runtime shape of retiring a child after a distinct root birth.
||| This is the ordered-binding half of the exchange, not evaluator replay.
export
0 retireInsertedSnapshot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (child, root : name) ->
  (fiber : Fiber name key value world error) ->
  (component : Component key value world error) -> (ambient : world) ->
  (fibers : Registry name key value world error) ->
  (0 absent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} root fibers = Nothing) ->
  (0 distinct : Not (child = root)) ->
  runtimeSnapshot {name} {key} {value} {world} {error} (MkSystemState ambient
    (replaceBinding @{nameEq} child (retireFiber fiber)
      (insertBinding @{nameEq} root (freshFiber component Root) fibers absent))) =
  MkRuntimeSnapshot ambient (Bind root (freshFiber component Root) ::
    bindings (replaceBinding @{nameEq} child (retireFiber fiber) fibers))
retireInsertedSnapshot nameEq child root fiber component ambient
  (MkCoeffectContext entries unique) absent distinct =
    cong (MkRuntimeSnapshot ambient)
      (replaceOtherHeadObserved nameEq child root (retireFiber fiber)
        (freshFiber component Root) entries (decEq @{nameEq} child root) Refl distinct)

||| Assemble a root/own-child-Retire square from an observed insertion source
||| and an independently produced checked late root insertion. The original
||| retirement endpoint is recovered from its actual native equation.
export
0 rootRetireSquareAtInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, root : name) ->
  (fiber : Fiber name key value world error) ->
  (component : Component key value world error) -> (ambient : world) ->
  (fibers : Registry name key value world error) ->
  (0 absent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} root fibers = Nothing) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child fibers = Just fiber) ->
  (0 own : fiberParent fiber = ChildOf parent) ->
  (0 distinct : Not (child = root)) ->
  (0 valid : registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (MkSystemState ambient fibers) = True) ->
  (finalState : SystemState name key value world error) ->
  (0 inserted : checkedApplyAction @{nameEq} @{keyEq} (OInsert root Root component)
    (MkSystemState ambient fibers) = Just (OInsertTag,
      MkSystemState ambient (insertBinding @{nameEq} root (freshFiber component Root) fibers absent))) ->
  (0 retiredLater : checkedApplyAction @{nameEq} @{keyEq} (ORetire child)
    (MkSystemState ambient (insertBinding @{nameEq} root (freshFiber component Root) fibers absent)) =
      Just (ORetireTag, finalState)) ->
  (replay : CheckedSnapshotStep name key world error value nameEq keyEq (OInsert root Root component)
    (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber fiber) fibers)) OInsertTag
    (MkRuntimeSnapshot ambient (Bind root (freshFiber component Root) ::
      bindings (replaceBinding @{nameEq} child (retireFiber fiber) fibers)))) ->
  ChildRetireSnapshotExchange name key world error value nameEq keyEq child parent
    (Fired {before = MkSystemState ambient fibers}
      {afterState = MkSystemState ambient (insertBinding @{nameEq} root (freshFiber component Root) fibers absent)}
      nameEq keyEq (OInsert root Root component) OInsertTag inserted)
    (Fired {before = MkSystemState ambient (insertBinding @{nameEq} root (freshFiber component Root) fibers absent)}
      {afterState = finalState} nameEq keyEq (ORetire child) ORetireTag retiredLater)
rootRetireSquareAtInsert nameEq keyEq child parent root fiber component ambient fibers
  absent found own distinct valid finalState inserted retiredLater replay =
    MkChildRetireSnapshotExchange fiber found own distinct Refl
      (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber fiber) fibers))
      (snapshotAfter replay)
      (childRetireAtFound nameEq keyEq child fiber (MkSystemState ambient fibers) found valid)
      (snapshotChecked replay)
      (trans
        (cong runtimeSnapshot (cong snd (justInjective
          (trans (sym retiredLater)
            (childRetireAtFound nameEq keyEq child fiber
              (MkSystemState ambient (insertBinding @{nameEq} root (freshFiber component Root) fibers absent))
              (trans (lookupInsertOther @{nameEq} child root distinct (freshFiber component Root) fibers absent) found)
              (checkedActionTargetValid nameEq keyEq (OInsert root Root component)
                (MkSystemState ambient fibers)
                (MkSystemState ambient (insertBinding @{nameEq} root (freshFiber component Root) fibers absent))
                OInsertTag inserted))))))
        (trans (retireInsertedSnapshot nameEq child root fiber component ambient fibers absent distinct)
          (sym (snapshotExact replay))))

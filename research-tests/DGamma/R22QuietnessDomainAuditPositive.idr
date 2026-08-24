module DGamma.R22QuietnessDomainAuditPositive

import DGamma.Coeffects
import DGamma.Calculus
import DGamma.CP3
import DGamma.CP3Support
import DGamma.CP4SupportQuiescence
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality
import Data.Maybe

%default total

||| Pointwise controls are strong enough to recover a source-domain witness for
||| every concrete target binding. No caller-supplied list correspondence is
||| needed merely to reconstruct domain membership.
public export
record ControlledSourceForTarget
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name)
  (source, target : SystemState name key value world error)
  (selected : name)
  (targetFiber : Fiber name key value world error) where
  constructor MkControlledSourceForTarget
  sourceFiber : Fiber name key value world error
  0 sourceFound : lookupFiber @{nameEq} selected (registry source) =
    Just sourceFiber
  0 targetControl : FiberControlRelated sourceFiber targetFiber

0 relatedRightHasSource :
  {sourceMaybe : Maybe (Fiber name key value world error)} ->
  {targetFiber : Fiber name key value world error} ->
  FiberControlMaybeRelated sourceMaybe (Just targetFiber) ->
  (sourceFiber : Fiber name key value world error **
    (sourceMaybe = Just sourceFiber, FiberControlRelated sourceFiber targetFiber))
relatedRightHasSource (SomeControlFibers related) = (_ ** (Refl, related))

public export
0 controlEquivalentTargetHasSource :
  (nameEq : DecEq name) ->
  (source, target : SystemState name key value world error) ->
  ControlEquivalent name key world error value nameEq source target ->
  (selected : name) ->
  (targetFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry target) = Just targetFiber ->
  ControlledSourceForTarget name key world error value nameEq source target
    selected targetFiber
controlEquivalentTargetHasSource nameEq source target controls selected
  targetFiber targetFound =
    let 0 rightIsTarget : FiberControlMaybeRelated
          (lookupFiber @{nameEq} selected (registry source)) (Just targetFiber)
        rightIsTarget = replace
          {p = \observed => FiberControlMaybeRelated
            (lookupFiber @{nameEq} selected (registry source)) observed}
          targetFound (controlPointwise controls selected)
    in case relatedRightHasSource rightIsTarget of
      (sourceFiber ** (sourceFound, related)) =>
        MkControlledSourceForTarget sourceFiber sourceFound related

||| Only Inactive-Nothing and Active quietness inspect `targetFiber`; failed
||| Inactive is locally quiet, while Reloading and Unloading are locally noisy.
public export
lifecycleQuietUsesTarget :
  {key, world, error, name : Type} -> {value : key -> Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  Lifecycle key value world error name deps provision -> Bool
lifecycleQuietUsesTarget (Inactive Nothing) = True
lifecycleQuietUsesTarget (Inactive (Just errorValue)) = False
lifecycleQuietUsesTarget (Reloading remaining accumulator view) = False
lifecycleQuietUsesTarget (Active accumulator view) = True
lifecycleQuietUsesTarget (Unloading accumulator view outcome) = False

public export
0 lifecycleControlPreservesQuietTargetMode :
  LifecycleControlRelated left right ->
  lifecycleQuietUsesTarget left = lifecycleQuietUsesTarget right
lifecycleControlPreservesQuietTargetMode (InactiveControls Refl) = Refl
lifecycleControlPreservesQuietTargetMode
  (ReloadingControls Refl accumulator Refl) = Refl
lifecycleControlPreservesQuietTargetMode (ActiveControls accumulator Refl) = Refl
lifecycleControlPreservesQuietTargetMode
  (UnloadingControls accumulator Refl Refl) = Refl

public export
lifecycleNotFailedBool :
  {key, world, error, name : Type} -> {value : key -> Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  Lifecycle key value world error name deps provision -> Bool
lifecycleNotFailedBool (Inactive (Just errorValue)) = False
lifecycleNotFailedBool (Inactive Nothing) = True
lifecycleNotFailedBool (Reloading remaining accumulator view) = True
lifecycleNotFailedBool (Active accumulator view) = True
lifecycleNotFailedBool (Unloading accumulator view outcome) = True

0 lifecycleControlPreservesNotFailed :
  LifecycleControlRelated left right ->
  lifecycleNotFailedBool left = lifecycleNotFailedBool right
lifecycleControlPreservesNotFailed (InactiveControls Refl) = Refl
lifecycleControlPreservesNotFailed
  (ReloadingControls Refl accumulator Refl) = Refl
lifecycleControlPreservesNotFailed (ActiveControls accumulator Refl) = Refl
lifecycleControlPreservesNotFailed
  (UnloadingControls accumulator Refl Refl) = Refl

0 fiberNotFailedExplicit :
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  fiberNotFailed (MkFiber component parent retiredFlag table lifecycle) =
    lifecycleNotFailedBool lifecycle
fiberNotFailedExplicit component parent retiredFlag table (Inactive Nothing) = Refl
fiberNotFailedExplicit component parent retiredFlag table
  (Inactive (Just errorValue)) = Refl
fiberNotFailedExplicit component parent retiredFlag table
  (Reloading remaining accumulator view) = Refl
fiberNotFailedExplicit component parent retiredFlag table
  (Active accumulator view) = Refl
fiberNotFailedExplicit component parent retiredFlag table
  (Unloading accumulator view outcome) = Refl

||| The no-failure per-fiber predicate is completely preserved by lifecycle
||| controls. Thus if quietness later closes, no-failure's local lifecycle case
||| does not require stronger endpoint capital; only the finite target fold must
||| be rebuilt.
public export
0 fiberControlPreservesNotFailed :
  FiberControlRelated left right ->
  fiberNotFailed left = fiberNotFailed right
fiberControlPreservesNotFailed
  (FibersControlRelated leftParent rightParent leftRetired rightRetired
    leftTable rightTable leftLifecycle rightLifecycle parentSame retiredSame
    lifecycle) =
      trans (fiberNotFailedExplicit _ leftParent leftRetired leftTable
        leftLifecycle)
        (trans (lifecycleControlPreservesNotFailed lifecycle)
          (sym (fiberNotFailedExplicit _ rightParent rightRetired rightTable
            rightLifecycle)))

||| A target-domain head can therefore recover both its source lookup and the
||| exact local no-failure equality. This is the induction step needed for a
||| target `allList` fold; it confirms that raw domain reconstruction itself is
||| not the revision-22 blocker.
public export
0 targetEntryNotFailedFromSource :
  (nameEq : DecEq name) ->
  (source, target : SystemState name key value world error) ->
  (controls : ControlEquivalent name key world error value nameEq source target) ->
  noFailedFibers source = True ->
  (selected : name) ->
  (targetFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry target) = Just targetFiber ->
  fiberNotFailed targetFiber = True
targetEntryNotFailedFromSource nameEq source target controls sourceNoFailure
  selected targetFiber targetFound =
    case controlEquivalentTargetHasSource nameEq source target controls selected
      targetFiber targetFound of
      MkControlledSourceForTarget sourceFiber sourceFound related =>
        trans (sym (fiberControlPreservesNotFailed related))
          (noFailureFromState nameEq source sourceNoFailure selected sourceFiber
            sourceFound)

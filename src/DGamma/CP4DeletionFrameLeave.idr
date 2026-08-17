module DGamma.CP4DeletionFrameLeave

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionFrameCore
import Decidable.Equality

%default total

||| The explicit L-Divert rule changes only lifecycle control.
public export
0 leaveActualEffectFrame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LLeave actor) before =
    Just (tag, afterState) ->
  ActualEffectFrame nameEq keyEq (LLeave actor) tag before afterState
leaveActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
  afterState tag raw with (lookupFiber @{nameEq} actor fibers) proof found
  leaveActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
    afterState tag raw | Nothing = void (nothingIsNotJust raw)
  leaveActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
    afterState tag raw | Just (MkFiber component parent retiredFlag table lifecycle)
    with (fiberLifecycle (MkFiber component parent retiredFlag table lifecycle))
    leaveActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Inactive outcome = void (nothingIsNotJust raw)
    leaveActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Reloading remaining accumulator view = void (nothingIsNotJust raw)
    leaveActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Unloading accumulator view outcome = void (nothingIsNotJust raw)
    leaveActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Active accumulator view with
      (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq}
          (MkFiber component parent retiredFlag table
            (Active accumulator view)) fibers) view)
      leaveActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
        afterState tag raw |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Active accumulator view | True =
              void (nothingIsNotJust raw)
      leaveActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
        afterState tag raw |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Active accumulator view | False =
        let sourceFiber : Fiber name key value world error
            sourceFiber = MkFiber component parent retiredFlag table
              (Active accumulator view)
            next : Fiber name key value world error
            next = setFiberLifecycle sourceFiber
              (Unloading accumulator view Nothing)
            concrete : SystemState name key value world error
            concrete = MkSystemState ambient
              (replaceBinding @{nameEq} actor next fibers)
            0 rawReduced : Just (LLeaveTag, concrete) = Just (tag, afterState)
            rawReduced = raw
            0 concreteAfter : concrete = afterState
            concreteAfter = cong snd (justInjective rawReduced)
            0 nextShape : next = setFiberLifecycle sourceFiber
              (Unloading accumulator view Nothing)
            nextShape = Refl
            0 tableSame : (k : key) ->
              lookupBinding @{keyEq} k (ownedValues (fiberTable next)) =
              lookupBinding @{keyEq} k (ownedValues (fiberTable sourceFiber))
            tableSame k = trans
              (cong (\observed => lookupBinding @{keyEq} k
                (ownedValues (fiberTable observed))) nextShape)
              (setLifecycleTableLookup keyEq k sourceFiber
                (Unloading accumulator view Nothing))
            0 identityMap : partialEffectMapFor nameEq keyEq (LLeave actor) tag
              (the (SystemState name key value world error)
                (MkSystemState ambient fibers))
              (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState ambient fibers))) =
              Just (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState ambient fibers)))
            identityMap = Refl
        in controlReplaceActualEffectFrame nameEq keyEq (LLeave actor) tag actor
          ambient sourceFiber next fibers afterState found tableSame concreteAfter
          identityMap

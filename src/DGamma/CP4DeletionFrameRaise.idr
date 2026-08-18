module DGamma.CP4DeletionFrameRaise

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionFrameCore
import Decidable.Equality

%default total

||| Saturated L-Raise branch frame. The evaluator classifier supplies the
||| concrete failing step/error branch; the rule itself changes only lifecycle
||| control, and its Definition-60 effect generator is identity.
public export
0 raiseConcreteActualEffectFrame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (rest : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (err : error) ->
  (sourceFound : lookupFiber @{nameEq} actor fibers =
    Just (MkFiber component parent retiredFlag table
      (Reloading (step :: rest) accumulator view))) ->
  (afterState : SystemState name key value world error) ->
  (concreteAfter :
    (the (SystemState name key value world error)
      (MkSystemState ambient
        (replaceBinding @{nameEq} actor
          (setFiberLifecycle
            (MkFiber component parent retiredFlag table
              (Reloading (step :: rest) accumulator view))
            (Unloading accumulator view (Just err))) fibers))) = afterState) ->
  ActualEffectFrame nameEq keyEq (LAdvance actor) LRaiseTag
    (MkSystemState ambient fibers) afterState
raiseConcreteActualEffectFrame nameEq keyEq actor ambient fibers component parent
  retiredFlag table step rest accumulator view err sourceFound afterState
  concreteAfter =
  let sourceFiber : Fiber name key value world error
      sourceFiber = MkFiber component parent retiredFlag table
        (Reloading (step :: rest) accumulator view)
      next : Fiber name key value world error
      next = setFiberLifecycle sourceFiber
        (Unloading accumulator view (Just err))
      0 nextShape : next = setFiberLifecycle sourceFiber
        (Unloading accumulator view (Just err))
      nextShape = Refl
      0 tableSame : ownedValues (fiberTable next) =
        ownedValues (fiberTable sourceFiber)
      tableSame = replace
        {p = \observed => ownedValues (fiberTable observed) =
          ownedValues (fiberTable sourceFiber)}
        (sym nextShape)
        (setLifecycleTableExact sourceFiber
          (Unloading accumulator view (Just err)))
      0 identityMap : partialEffectMapFor nameEq keyEq (LAdvance actor) LRaiseTag
        (the (SystemState name key value world error)
          (MkSystemState ambient fibers))
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState ambient fibers))) =
        Just (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState ambient fibers)))
      identityMap = Refl
  in controlReplaceActualEffectFrame nameEq keyEq (LAdvance actor) LRaiseTag actor
    ambient sourceFiber next fibers afterState sourceFound tableSame concreteAfter
    identityMap

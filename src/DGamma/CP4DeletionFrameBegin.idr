module DGamma.CP4DeletionFrameBegin

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionFrameCore
import Decidable.Equality

%default total

||| L-Begin changes only lifecycle control. The committed view and restarted
||| continuation do not alter ambient state or the actor's owned table.
public export
0 beginActualEffectFrame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LBegin actor) before =
    Just (tag, afterState) ->
  ActualEffectFrame nameEq keyEq (LBegin actor) tag before afterState
beginActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
  afterState tag raw with (lookupFiber @{nameEq} actor fibers) proof found
  beginActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
    afterState tag raw | Nothing = void (nothingIsNotJust raw)
  beginActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
    afterState tag raw | Just (MkFiber component parent retiredFlag table lifecycle)
    with (fiberLifecycle (MkFiber component parent retiredFlag table lifecycle))
    beginActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Inactive (Just err) = void (nothingIsNotJust raw)
    beginActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Reloading remaining accumulator view = void (nothingIsNotJust raw)
    beginActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Active accumulator view = void (nothingIsNotJust raw)
    beginActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Unloading accumulator view outcome = void (nothingIsNotJust raw)
    beginActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Inactive Nothing with
      (targetFiber @{nameEq} @{keyEq}
        (MkFiber component parent retiredFlag table (Inactive Nothing)) fibers)
      beginActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
        afterState tag raw |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Inactive Nothing | Nothing = void (nothingIsNotJust raw)
      beginActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
        afterState tag raw |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Inactive Nothing | Just view =
        let sourceFiber : Fiber name key value world error
            sourceFiber = MkFiber component parent retiredFlag table
              (Inactive Nothing)
            next : Fiber name key value world error
            next = setFiberLifecycle sourceFiber
              (Reloading (componentProgram component) (\local => local) view)
            concrete : SystemState name key value world error
            concrete = MkSystemState ambient
              (replaceBinding @{nameEq} actor next fibers)
            0 rawReduced : Just (LBeginTag, concrete) = Just (tag, afterState)
            rawReduced = raw
            0 concreteAfter : concrete = afterState
            concreteAfter = cong snd (justInjective rawReduced)
            0 nextShape : next = setFiberLifecycle sourceFiber
              (Reloading (componentProgram component) (\local => local) view)
            nextShape = Refl
            0 tableSame : (k : key) ->
              lookupBinding @{keyEq} k (ownedValues (fiberTable next)) =
              lookupBinding @{keyEq} k (ownedValues (fiberTable sourceFiber))
            tableSame k = trans
              (cong (\observed => lookupBinding @{keyEq} k
                (ownedValues (fiberTable observed))) nextShape)
              (setLifecycleTableLookup keyEq k sourceFiber
                (Reloading (componentProgram component) (\local => local) view))
            0 relatedConcrete : EffectStateRelated keyEq
              (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState ambient fibers)))
              (projectEffectState @{nameEq} concrete)
            relatedConcrete = projectTablePreservingReplace nameEq keyEq actor
              ambient sourceFiber next fibers found tableSame
            0 relatedAfter : EffectStateRelated keyEq
              (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState ambient fibers)))
              (projectEffectState @{nameEq} afterState)
            relatedAfter = replace
              {p = \state => EffectStateRelated keyEq
                (projectEffectState @{nameEq}
                  (the (SystemState name key value world error)
                    (MkSystemState ambient fibers)))
                (projectEffectState @{nameEq} state)}
              concreteAfter relatedConcrete
        in MkActualEffectFrame (PartialDefined relatedAfter)

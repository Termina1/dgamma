module DGamma.CP4DeletionFrameRemove

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionFrameCore
import Decidable.Equality

%default total

||| O-Remove's generator empties the removed actor table, exactly matching the
||| effect projection of the registry after deletion.
public export
0 removeActualEffectFrame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (ORemove actor) before =
    Just (tag, afterState) ->
  ActualEffectFrame nameEq keyEq (ORemove actor) tag before afterState
removeActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
  afterState tag raw with (lookupFiber @{nameEq} actor fibers)
  removeActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
    afterState tag raw | Nothing = void (nothingIsNotJust raw)
  removeActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
    afterState tag raw | Just fiber with
    (retired fiber && isInactive (fiberLifecycle fiber) &&
      not (hasChild @{nameEq} actor fibers))
    removeActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | False = void (nothingIsNotJust raw)
    removeActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | True =
      let concrete : SystemState name key value world error
          concrete = MkSystemState ambient (deleteBinding @{nameEq} actor fibers)
          0 rawReduced : Just (ORemoveTag, concrete) = Just (tag, afterState)
          rawReduced = raw
          0 concreteAfter : concrete = afterState
          concreteAfter = cong snd (justInjective rawReduced)
          0 relatedConcrete : EffectStateRelated keyEq
            (setEffectTable @{nameEq} actor
              (emptyContext {key = key} {value = value})
              (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState ambient fibers))))
            (projectEffectState @{nameEq} concrete)
          relatedConcrete = projectDeleteEffectFrame nameEq keyEq actor ambient
            fibers
          0 relatedAfter : EffectStateRelated keyEq
            (setEffectTable @{nameEq} actor
              (emptyContext {key = key} {value = value})
              (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState ambient fibers))))
            (projectEffectState @{nameEq} afterState)
          relatedAfter = replace
            {p = \state => EffectStateRelated keyEq
              (setEffectTable @{nameEq} actor
                (emptyContext {key = key} {value = value})
                (projectEffectState @{nameEq}
                  (the (SystemState name key value world error)
                    (MkSystemState ambient fibers))))
              (projectEffectState @{nameEq} state)}
            concreteAfter relatedConcrete
      in PartialDefined relatedAfter

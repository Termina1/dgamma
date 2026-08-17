module DGamma.CP4DeletionFrameInsert

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionFrameCore
import Decidable.Equality

%default total

||| O-Insert's actual generator and its fresh empty runtime table agree
||| pointwise, including every foreign table frame.
public export
0 insertActualEffectFrame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (OInsert actor parent component) before =
    Just (tag, afterState) ->
  ActualEffectFrame nameEq keyEq (OInsert actor parent component) tag before
    afterState
insertActualEffectFrame nameEq keyEq actor parent component
  (MkSystemState ambient fibers) afterState tag raw with
  (parentPresent @{nameEq} parent fibers &&
    provisionsDisjointFrom @{keyEq} (componentProvisions component)
      (registryFibers fibers))
  insertActualEffectFrame nameEq keyEq actor parent component
    (MkSystemState ambient fibers) afterState tag raw | False =
      void (nothingIsNotJust raw)
  insertActualEffectFrame nameEq keyEq actor parent component
    (MkSystemState ambient fibers) afterState tag raw | True with
    (setFresh @{nameEq} actor (freshFiber component parent) fibers) proof inserted
    insertActualEffectFrame nameEq keyEq actor parent component
      (MkSystemState ambient fibers) afterState tag raw | True | Nothing =
        void (nothingIsNotJust raw)
    insertActualEffectFrame nameEq keyEq actor parent component
      (MkSystemState ambient fibers) afterState tag raw | True | Just applied =
      let 0 absent : (lookupFiber @{nameEq} {key = key} {value = value}
            {world = world} {error = error} actor fibers = Nothing)
          absent = setFreshAbsent nameEq actor (freshFiber component parent)
            fibers applied inserted
          0 insertedShape : (coeffectAfter applied =
            insertBinding @{nameEq} actor (freshFiber component parent) fibers
              absent)
          insertedShape = setFreshAfter nameEq actor
            (freshFiber component parent) fibers applied inserted
          concrete : SystemState name key value world error
          concrete = MkSystemState ambient (coeffectAfter applied)
          0 rawReduced : Just (OInsertTag, concrete) = Just (tag, afterState)
          rawReduced = raw
          0 concreteAfter : concrete = afterState
          concreteAfter = cong snd (justInjective rawReduced)
          insertedState : SystemState name key value world error
          insertedState = MkSystemState ambient
            (insertBinding @{nameEq} actor (freshFiber component parent) fibers
              absent)
          0 concreteInserted : concrete = insertedState
          concreteInserted = cong (MkSystemState ambient) insertedShape
          0 relatedInserted : EffectStateRelated keyEq
            (setEffectTable @{nameEq} actor
              (emptyContext {key = key} {value = value})
              (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState ambient fibers))))
            (projectEffectState @{nameEq} insertedState)
          relatedInserted = projectInsertEffectFrame nameEq keyEq actor ambient
            component parent fibers absent
          0 relatedConcrete : EffectStateRelated keyEq
            (setEffectTable @{nameEq} actor
              (emptyContext {key = key} {value = value})
              (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState ambient fibers))))
            (projectEffectState @{nameEq} concrete)
          relatedConcrete = replace
            {p = \state => EffectStateRelated keyEq
              (setEffectTable @{nameEq} actor
                (emptyContext {key = key} {value = value})
                (projectEffectState @{nameEq}
                  (the (SystemState name key value world error)
                    (MkSystemState ambient fibers))))
              (projectEffectState @{nameEq} state)}
            (sym concreteInserted) relatedInserted
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
      in MkActualEffectFrame (PartialDefined relatedAfter)

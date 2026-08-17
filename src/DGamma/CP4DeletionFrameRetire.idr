module DGamma.CP4DeletionFrameRetire

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionFrameCore
import Decidable.Equality

%default total

0 retireTableLookup : (keyEq : DecEq key) -> (k : key) ->
  (fiber : Fiber name key value world error) ->
  lookupBinding @{keyEq} k (ownedValues (fiberTable (retireFiber fiber))) =
  lookupBinding @{keyEq} k (ownedValues (fiberTable fiber))
retireTableLookup keyEq k (MkFiber component parent retiredFlag table lifecycle) =
  Refl

||| O-Retire is control-only. Its actual-forward generator is therefore the
||| identity on effects and the target projection is pointwise unchanged.
public export
0 retireActualEffectFrame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (ORetire actor) before =
    Just (tag, afterState) ->
  ActualEffectFrame nameEq keyEq (ORetire actor) tag
    before afterState
retireActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
  afterState tag raw with (lookupFiber @{nameEq} actor fibers) proof found
  retireActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
    afterState tag raw | Nothing = void (nothingIsNotJust raw)
  retireActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
    afterState tag raw | Just fiber =
    let next : Fiber name key value world error
        next = retireFiber fiber
        concrete : SystemState name key value world error
        concrete = MkSystemState ambient
          (replaceBinding @{nameEq} actor next fibers)
        0 nextFound : lookupFiber @{nameEq} actor (registry concrete) = Just next
        nextFound = lookupReplacedFiber actor fiber next fibers found
        0 rawReduced : Just (ORetireTag, concrete) = Just (tag, afterState)
        rawReduced = raw
        0 concreteAfter : concrete = afterState
        concreteAfter = cong snd (justInjective rawReduced)
        0 nextShape : next = retireFiber fiber
        nextShape = Refl
        0 tableSame : (k : key) ->
          lookupBinding @{keyEq} k (ownedValues (fiberTable next)) =
          lookupBinding @{keyEq} k (ownedValues (fiberTable fiber))
        tableSame k = trans
          (cong (\observed => lookupBinding @{keyEq} k
            (ownedValues (fiberTable observed))) nextShape)
          (retireTableLookup keyEq k fiber)
        0 relatedConcrete : EffectStateRelated keyEq
          (projectEffectState @{nameEq}
            (the (SystemState name key value world error)
              (MkSystemState ambient fibers)))
          (projectEffectState @{nameEq} concrete)
        relatedConcrete = projectTablePreservingReplace nameEq keyEq actor
          ambient fiber next fibers found tableSame
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
    in PartialDefined relatedAfter

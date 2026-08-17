module DGamma.CP4DeletionFrameCore

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import Decidable.Equality

%default total

||| Relational soundness of one actual-forward generator at its concrete source.
||| Pointwise `EffectStateRelated` is required because effect tables are functions
||| and the project deliberately does not assume function extensionality.
public export
ActualEffectFrame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) -> Type
ActualEffectFrame nameEq keyEq action tag before afterState =
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (partialEffectMapFor nameEq keyEq action tag before
      (projectEffectState @{nameEq} before))
    (Just (projectEffectState @{nameEq} afterState))

public export
0 setLifecycleTableLookup : (keyEq : DecEq key) -> (k : key) ->
  (fiber : Fiber name key value world error) ->
  (life : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  lookupBinding @{keyEq} k
    (ownedValues (fiberTable (setFiberLifecycle fiber life))) =
  lookupBinding @{keyEq} k (ownedValues (fiberTable fiber))
setLifecycleTableLookup keyEq k
  (MkFiber component parent retiredFlag table oldLife) life = Refl

||| Replacing one fiber while preserving its owned table is invisible to the
||| full effect-state projection, pointwise on every dynamic table lookup.
public export
0 projectTablePreservingReplace :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (worldValue : world) ->
  (old, next : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} actor fibers = Just old ->
  ((k : key) -> lookupBinding @{keyEq} k (ownedValues (fiberTable next)) =
    lookupBinding @{keyEq} k (ownedValues (fiberTable old))) ->
  EffectStateRelated keyEq
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState worldValue fibers)))
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState worldValue
          (replaceBinding @{nameEq} actor next fibers))))
projectTablePreservingReplace nameEq keyEq actor worldValue old next fibers found
  tableSame = MkEffectStateRelated Refl tables
  where
  0 tables : (selected : name) -> (k : key) ->
    lookupBinding @{keyEq} k
      (effectTables (projectEffectState @{nameEq}
        (the (SystemState name key value world error)
          (MkSystemState worldValue fibers))) selected) =
    lookupBinding @{keyEq} k
      (effectTables (projectEffectState @{nameEq}
        (the (SystemState name key value world error)
          (MkSystemState worldValue
            (replaceBinding @{nameEq} actor next fibers)))) selected)
  tables selected k with (decEq @{nameEq} selected actor)
    tables _ k | Yes Refl =
      rewrite found in
      rewrite lookupReplacedFiber actor old next fibers found in
      sym (tableSame k)
    tables selected k | No distinct with
      (lookupFiber @{nameEq} selected fibers) proof sourceLookup
      tables selected k | No distinct | Nothing =
        let targetLookup = trans
              (lookupReplaceOther selected actor distinct next fibers) sourceLookup
        in rewrite targetLookup in Refl
      tables selected k | No distinct | Just observed =
        let targetLookup = trans
              (lookupReplaceOther selected actor distinct next fibers) sourceLookup
        in rewrite targetLookup in Refl

||| Package a control-only local replacement once its evaluator endpoint and
||| identity effect-map branch have been exposed by a per-rule case split.
public export
0 controlReplaceActualEffectFrame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (actor : name) -> (worldValue : world) ->
  (old, next : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  (afterState : SystemState name key value world error) ->
  lookupFiber @{nameEq} actor fibers = Just old ->
  ((k : key) -> lookupBinding @{keyEq} k (ownedValues (fiberTable next)) =
    lookupBinding @{keyEq} k (ownedValues (fiberTable old))) ->
  (concreteAfter :
    (the (SystemState name key value world error)
      (MkSystemState worldValue
        (replaceBinding @{nameEq} actor next fibers))) = afterState) ->
  (identityMap : partialEffectMapFor nameEq keyEq action tag
    (the (SystemState name key value world error)
      (MkSystemState worldValue fibers))
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState worldValue fibers))) =
      Just (projectEffectState @{nameEq}
        (the (SystemState name key value world error)
          (MkSystemState worldValue fibers)))) ->
  ActualEffectFrame nameEq keyEq action tag (MkSystemState worldValue fibers)
    afterState
controlReplaceActualEffectFrame nameEq keyEq action tag actor worldValue old next
  fibers afterState found tableSame concreteAfter identityMap =
  let 0 concrete : SystemState name key value world error
      concrete = MkSystemState worldValue
        (replaceBinding @{nameEq} actor next fibers)
      0 relatedConcrete : EffectStateRelated keyEq
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState worldValue fibers)))
        (projectEffectState @{nameEq} concrete)
      relatedConcrete = projectTablePreservingReplace nameEq keyEq actor
        worldValue old next fibers found tableSame
      0 relatedAfter : EffectStateRelated keyEq
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState worldValue fibers)))
        (projectEffectState @{nameEq} afterState)
      relatedAfter = replace
        {p = \state => EffectStateRelated keyEq
          (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState worldValue fibers)))
          (projectEffectState @{nameEq} state)}
        concreteAfter relatedConcrete
  in rewrite identityMap in PartialDefined relatedAfter

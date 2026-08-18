module DGamma.CP4DeletionFrameCore

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import Data.List.Elem
import Decidable.Equality

%default total

public export
0 ruleTagFromJust : Just (expectedTag, concrete) = Just (observedTag, after) ->
  expectedTag = observedTag
ruleTagFromJust equation = cong fst (justInjective equation)

public export
0 endpointFromJust : Just (expectedTag, concrete) = Just (observedTag, after) ->
  concrete = after
endpointFromJust equation = cong snd (justInjective equation)

||| Relational soundness of one actual-forward generator at its concrete source.
||| Pointwise `EffectStateRelated` is required because effect tables are functions
||| and the project deliberately does not assume function extensionality.
public export
data ActualEffectFrame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) -> Type where
  MkActualEffectFrame :
    (0 related : PartialRelated (EffectState name key value world)
      (EffectStateRelated keyEq)
      (partialEffectMapFor nameEq keyEq action tag before
        (projectEffectState @{nameEq} before))
      (Just (projectEffectState @{nameEq} afterState))) ->
    ActualEffectFrame nameEq keyEq action tag before afterState

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

public export
0 setLifecycleTableExact :
  (fiber : Fiber name key value world error) ->
  (life : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  ownedValues (fiberTable (setFiberLifecycle fiber life)) =
  ownedValues (fiberTable fiber)
setLifecycleTableExact
  (MkFiber component parent retiredFlag table oldLife) life = Refl

public export
0 setRuntimeTableExact :
  (fiber : Fiber name key value world error) ->
  (table : OwnedTable key value (componentProvisions (fiberComponent fiber))) ->
  (life : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  ownedValues (fiberTable (setFiberRuntime fiber table life)) =
  ownedValues table
setRuntimeTableExact
  (MkFiber component parent retiredFlag oldTable oldLife) table life = Refl

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
  ownedValues (fiberTable next) = ownedValues (fiberTable old) ->
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
  0 tables : (selected : name) ->
    effectTables (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState worldValue fibers))) selected =
    effectTables (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState worldValue
          (replaceBinding @{nameEq} actor next fibers)))) selected
  tables selected with (decEq @{nameEq} selected actor)
    tables _ | Yes Refl =
      rewrite found in
      rewrite lookupReplacedFiber actor old next fibers found in
      sym tableSame
    tables selected | No distinct with
      (lookupFiber @{nameEq} selected fibers) proof sourceLookup
      tables selected | No distinct | Nothing =
        let targetLookup = trans
              (lookupReplaceOther selected actor distinct next fibers) sourceLookup
        in rewrite targetLookup in Refl
      tables selected | No distinct | Just observed =
        let targetLookup = trans
              (lookupReplaceOther selected actor distinct next fibers) sourceLookup
        in rewrite targetLookup in Refl

0 lookupNotElemNothing : DecEq key => (wanted : key) ->
  (entries : List (Binding key value)) ->
  Not (Elem wanted (bindingKeys entries)) -> lookupEntries wanted entries = Nothing
lookupNotElemNothing wanted [] absent = Refl
lookupNotElemNothing wanted (Bind current value :: rest) absent with
  (decEq wanted current)
  lookupNotElemNothing current (Bind current value :: rest) absent | Yes Refl =
    void (absent Here)
  lookupNotElemNothing wanted (Bind current value :: rest) absent | No distinct =
    lookupNotElemNothing wanted rest (\later => absent (There later))

0 lookupDeleteSelf : DecEq key => (removed : key) ->
  (context : CoeffectContext key value) ->
  lookupBinding removed (deleteBinding removed context) = Nothing
lookupDeleteSelf removed (MkCoeffectContext entries unique) =
  lookupNotElemNothing removed (deleteEntries removed entries)
    (deletedKeyNotElem removed entries unique)

||| O-Insert's effect map explicitly creates an empty actor table, matching
||| the fresh fiber's empty owned table in the target projection.
public export
0 projectInsertEffectFrame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (worldValue : world) -> (component : Component key value world error) ->
  (parent : Parent name) -> (fibers : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} actor fibers = Nothing) ->
  EffectStateRelated keyEq
    (setEffectTable @{nameEq} actor
      (emptyContext {key = key} {value = value})
      (projectEffectState @{nameEq}
        (the (SystemState name key value world error)
          (MkSystemState worldValue fibers))))
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState worldValue
          (insertBinding @{nameEq} actor (freshFiber component parent) fibers
            absent))))
projectInsertEffectFrame nameEq keyEq actor worldValue component parent fibers
  absent = MkEffectStateRelated Refl tables
  where
  0 tables : (selected : name) ->
    effectTables (setEffectTable @{nameEq} actor
      (emptyContext {key = key} {value = value})
      (projectEffectState @{nameEq}
        (the (SystemState name key value world error)
          (MkSystemState worldValue fibers)))) selected =
    effectTables (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState worldValue
          (insertBinding @{nameEq} actor (freshFiber component parent) fibers
            absent)))) selected
  tables selected with (decEq @{nameEq} selected actor)
    tables _ | Yes Refl =
      rewrite lookupInserted actor (freshFiber component parent) fibers absent in
        Refl
    tables selected | No distinct with
      (lookupFiber @{nameEq} selected fibers) proof sourceLookup
      tables selected | No distinct | Nothing =
        let targetLookup = trans
              (lookupInsertOther selected actor distinct
                (freshFiber component parent) fibers absent) sourceLookup
        in rewrite targetLookup in Refl
      tables selected | No distinct | Just observed =
        let targetLookup = trans
              (lookupInsertOther selected actor distinct
                (freshFiber component parent) fibers absent) sourceLookup
        in rewrite targetLookup in Refl

||| O-Remove's effect map explicitly empties the removed name. This is
||| pointwise equal to projecting the registry after deleting that binding.
public export
0 projectDeleteEffectFrame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (worldValue : world) -> (fibers : Registry name key value world error) ->
  EffectStateRelated keyEq
    (setEffectTable @{nameEq} actor (emptyContext {key = key} {value = value})
      (projectEffectState @{nameEq}
        (the (SystemState name key value world error)
          (MkSystemState worldValue fibers))))
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState worldValue (deleteBinding @{nameEq} actor fibers))))
projectDeleteEffectFrame nameEq keyEq actor worldValue fibers =
  MkEffectStateRelated Refl tables
  where
  0 tables : (selected : name) ->
    effectTables (setEffectTable @{nameEq} actor
      (emptyContext {key = key} {value = value})
      (projectEffectState @{nameEq}
        (the (SystemState name key value world error)
          (MkSystemState worldValue fibers)))) selected =
    effectTables (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState worldValue
          (deleteBinding @{nameEq} actor fibers)))) selected
  tables selected with (decEq @{nameEq} selected actor)
    tables _ | Yes Refl = rewrite lookupDeleteSelf actor fibers in Refl
    tables selected | No distinct with
      (lookupFiber @{nameEq} selected fibers) proof sourceLookup
      tables selected | No distinct | Nothing =
        let targetLookup = trans (lookupDeleteOther selected actor distinct fibers)
              sourceLookup
        in rewrite targetLookup in Refl
      tables selected | No distinct | Just observed =
        let targetLookup = trans (lookupDeleteOther selected actor distinct fibers)
              sourceLookup
        in rewrite targetLookup in Refl

public export
0 projectedActorTable :
  (nameEq : DecEq name) -> (actor : name) ->
  (state : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor (registry state) = Just fiber ->
  effectTables (projectEffectState @{nameEq} state) actor =
    ownedValues (fiberTable fiber)
projectedActorTable nameEq actor state fiber found = rewrite found in Refl

||| The moved-effect resolver agrees with the evaluator's committed resolver at
||| an actual projected source.
public export
0 resolveEffectValuesProjected :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  (state : SystemState name key value world error) ->
  resolveEffectValues @{keyEq} {name = name} {key = key} {value = value}
    {world = world} deps view (projectEffectState @{nameEq} state) =
  resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} deps view (registry state)
resolveEffectValuesProjected nameEq keyEq [] EmptyView
  (MkSystemState ambient fibers) = Refl
resolveEffectValuesProjected nameEq keyEq (k :: ks) (ProviderView provider rest)
  (MkSystemState ambient fibers) with (lookupFiber @{nameEq} provider fibers)
  resolveEffectValuesProjected nameEq keyEq (k :: ks)
    (ProviderView provider rest) (MkSystemState ambient fibers) | Nothing = Refl
  resolveEffectValuesProjected nameEq keyEq (k :: ks)
    (ProviderView provider rest) (MkSystemState ambient fibers) |
    Just providerFiber with
    (lookupBinding @{keyEq} k (ownedValues (fiberTable providerFiber)))
    resolveEffectValuesProjected nameEq keyEq (k :: ks)
      (ProviderView provider rest) (MkSystemState ambient fibers) |
      Just providerFiber | Nothing = Refl
    resolveEffectValuesProjected nameEq keyEq (k :: ks)
      (ProviderView provider rest) (MkSystemState ambient fibers) |
      Just providerFiber | Just provided = cong (map (OneDepValue provided))
        (resolveEffectValuesProjected nameEq keyEq ks rest
          (MkSystemState ambient fibers))

||| Runtime-changing replacement frame shared by L-Iter/L-Finish/L-Unload.
public export
0 projectRuntimeReplace :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (sourceWorld, targetWorld : world) ->
  (old, next : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} actor fibers = Just old ->
  (targetTable : CoeffectContext key value) ->
  ownedValues (fiberTable next) = targetTable ->
  EffectStateRelated keyEq
    (setEffectTable @{nameEq} actor targetTable
      (setEffectAmbient targetWorld
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState sourceWorld fibers)))))
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState targetWorld
          (replaceBinding @{nameEq} actor next fibers))))
projectRuntimeReplace nameEq keyEq actor sourceWorld targetWorld old next fibers
  found targetTable tableSame = MkEffectStateRelated Refl tables
  where
  0 tables : (selected : name) ->
    effectTables (setEffectTable @{nameEq} actor targetTable
      (setEffectAmbient targetWorld
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState sourceWorld fibers))))) selected =
    effectTables (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState targetWorld
          (replaceBinding @{nameEq} actor next fibers)))) selected
  tables selected with (decEq @{nameEq} selected actor)
    tables _ | Yes Refl =
      rewrite lookupReplacedFiber actor old next fibers found in sym tableSame
    tables selected | No distinct with
      (lookupFiber @{nameEq} selected fibers) proof sourceLookup
      tables selected | No distinct | Nothing =
        let targetLookup = trans
              (lookupReplaceOther selected actor distinct next fibers) sourceLookup
        in rewrite targetLookup in Refl
      tables selected | No distinct | Just observed =
        let targetLookup = trans
              (lookupReplaceOther selected actor distinct next fibers) sourceLookup
        in rewrite targetLookup in Refl

||| Package an effectful runtime replacement once the per-rule evaluator split
||| exposes the exact moved effect state.
public export
0 runtimeReplaceActualEffectFrame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (actor : name) -> (sourceWorld, targetWorld : world) ->
  (old, next : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  (afterState : SystemState name key value world error) ->
  lookupFiber @{nameEq} actor fibers = Just old ->
  (targetTable : CoeffectContext key value) ->
  ownedValues (fiberTable next) = targetTable ->
  (concreteAfter :
    (the (SystemState name key value world error)
      (MkSystemState targetWorld
        (replaceBinding @{nameEq} actor next fibers))) = afterState) ->
  (mapRuns : partialEffectMapFor nameEq keyEq action tag
    (the (SystemState name key value world error)
      (MkSystemState sourceWorld fibers))
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState sourceWorld fibers))) =
    Just (setEffectTable @{nameEq} actor targetTable
      (setEffectAmbient targetWorld
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState sourceWorld fibers)))))) ->
  ActualEffectFrame nameEq keyEq action tag (MkSystemState sourceWorld fibers)
    afterState
runtimeReplaceActualEffectFrame nameEq keyEq action tag actor sourceWorld
  targetWorld old next fibers afterState found targetTable tableSame concreteAfter
  mapRuns =
  let concrete = MkSystemState targetWorld
        (replaceBinding @{nameEq} actor next fibers)
      relatedConcrete = projectRuntimeReplace nameEq keyEq actor sourceWorld
        targetWorld old next fibers found targetTable tableSame
      0 relatedAfter : EffectStateRelated keyEq
        (setEffectTable @{nameEq} actor targetTable
          (setEffectAmbient targetWorld
            (projectEffectState @{nameEq}
              (the (SystemState name key value world error)
                (MkSystemState sourceWorld fibers)))))
        (projectEffectState @{nameEq} afterState)
      relatedAfter = replace
        {p = \state => EffectStateRelated keyEq
          (setEffectTable @{nameEq} actor targetTable
            (setEffectAmbient targetWorld
              (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState sourceWorld fibers)))))
          (projectEffectState @{nameEq} state)}
        concreteAfter relatedConcrete
  in MkActualEffectFrame
    (rewrite mapRuns in PartialDefined relatedAfter)

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
  ownedValues (fiberTable next) = ownedValues (fiberTable old) ->
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
  in MkActualEffectFrame
    (rewrite identityMap in PartialDefined relatedAfter)

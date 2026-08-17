module DGamma.CP4ProgressUnloadingActive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressReliance
import DGamma.CP4ProgressUnloadingShape
import Decidable.Equality

%default total

0 activeLeaveFromMismatch :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (consumer : name) -> (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world
      (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} consumer fibers = Just
    (MkFiber component parent retiredFlag table (Active accumulator view)) ->
  targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq}
      (MkFiber component parent retiredFlag table (Active accumulator view))
      fibers) view = False ->
  LifecycleMove {name = name} {key = key} {value = value} {world = world}
    {error = error} nameEq keyEq (MkSystemState ambient fibers)
activeLeaveFromMismatch nameEq keyEq ambient fibers consumer component parent
  retiredFlag table accumulator view found mismatch =
    let sourceFiber : Fiber name key value world error
        sourceFiber = MkFiber component parent retiredFlag table
          (Active accumulator view)
        afterState : SystemState name key value world error
        afterState = MkSystemState ambient
          (replaceBinding @{nameEq} consumer
            (setFiberLifecycle sourceFiber
              (Unloading accumulator view Nothing)) fibers)
        0 raw : applyAction @{nameEq} @{keyEq} {value = value}
          {world = world} {error = error} (LLeave consumer)
          (MkSystemState ambient fibers) = Just (LLeaveTag, afterState)
        raw = rewrite found in rewrite mismatch in Refl
    in CanLeave consumer afterState raw

||| The Active clause of the unloading reliance descent, proved directly.
||| No cross-module application of the expanded mismatch theorem is used.
public export
0 unloadingActiveConsumerMove :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} (MkSystemState ambient fibers) = True ->
  (provider, consumer : name) ->
  (providerComponent : Component key value world error) ->
  (providerParent : Parent name) -> (providerRetired : Bool) ->
  (providerTable : OwnedTable key value
    (componentProvisions providerComponent)) ->
  (providerAccumulator : LocalState key value world
      (componentProvisions providerComponent) ->
    LocalState key value world (componentProvisions providerComponent)) ->
  (providerView : View name (dependencies
    (componentDependencies providerComponent))) ->
  (providerOutcome : Maybe error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} provider fibers = Just
    (MkFiber providerComponent providerParent providerRetired providerTable
      (Unloading providerAccumulator providerView providerOutcome)) ->
  (consumerComponent : Component key value world error) ->
  (consumerParent : Parent name) -> (consumerRetired : Bool) ->
  (consumerTable : OwnedTable key value
    (componentProvisions consumerComponent)) ->
  (consumerAccumulator : LocalState key value world
      (componentProvisions consumerComponent) ->
    LocalState key value world (componentProvisions consumerComponent)) ->
  (consumerView : View name (dependencies
    (componentDependencies consumerComponent))) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} consumer fibers = Just
    (MkFiber consumerComponent consumerParent consumerRetired consumerTable
      (Active consumerAccumulator consumerView)) ->
  ViewProviderOccurrence provider
    (dependencies (componentDependencies consumerComponent)) consumerView ->
  LifecycleMove {name = name} {key = key} {value = value} {world = world}
    {error = error} nameEq keyEq (MkSystemState ambient fibers)
unloadingActiveConsumerMove nameEq keyEq ambient fibers wellFormed provider
  consumer providerComponent providerParent providerRetired providerTable
  providerAccumulator providerView providerOutcome providerFound
  consumerComponent consumerParent True consumerTable consumerAccumulator
  consumerView consumerFound occurrence =
    activeLeaveFromMismatch nameEq keyEq ambient fibers consumer
      consumerComponent consumerParent True consumerTable consumerAccumulator
      consumerView consumerFound Refl
unloadingActiveConsumerMove nameEq keyEq ambient fibers wellFormed provider
  consumer providerComponent providerParent providerRetired providerTable
  providerAccumulator providerView providerOutcome providerFound
  consumerComponent consumerParent False consumerTable consumerAccumulator
  consumerView consumerFound occurrence
  with (the (Maybe (View name
          (dependencies (componentDependencies consumerComponent))))
        (resolveView @{nameEq} @{keyEq} {value = value} {world = world}
          {error = error}
          (dependencies (componentDependencies consumerComponent)) fibers))
    proof resolved
  unloadingActiveConsumerMove nameEq keyEq ambient fibers wellFormed provider
    consumer providerComponent providerParent providerRetired providerTable
    providerAccumulator providerView providerOutcome providerFound
    consumerComponent consumerParent False consumerTable consumerAccumulator
    consumerView consumerFound occurrence | Nothing =
      let 0 targetNone : (targetFiber @{nameEq} @{keyEq}
            (MkFiber consumerComponent consumerParent False consumerTable
              (Active consumerAccumulator consumerView)) fibers = Nothing)
          targetNone = trans
            (targetFiberExplicit nameEq keyEq consumerComponent consumerParent
              False consumerTable (Active consumerAccumulator consumerView)
              fibers) resolved
          0 mismatch : (targetMatches @{nameEq}
            (targetFiber @{nameEq} @{keyEq}
              (MkFiber consumerComponent consumerParent False consumerTable
                (Active consumerAccumulator consumerView)) fibers)
            consumerView = False)
          mismatch = rewrite targetNone in Refl
      in activeLeaveFromMismatch nameEq keyEq ambient fibers consumer
        consumerComponent consumerParent False consumerTable consumerAccumulator
        consumerView consumerFound mismatch
  unloadingActiveConsumerMove nameEq keyEq ambient fibers wellFormed provider
    consumer providerComponent providerParent providerRetired providerTable
    providerAccumulator providerView providerOutcome providerFound
    consumerComponent consumerParent False consumerTable consumerAccumulator
    consumerView consumerFound occurrence | Just target
    with (the Bool (viewEq @{nameEq} target consumerView)) proof same
    unloadingActiveConsumerMove nameEq keyEq ambient fibers wellFormed provider
      consumer providerComponent providerParent providerRetired providerTable
      providerAccumulator providerView providerOutcome providerFound
      consumerComponent consumerParent False consumerTable consumerAccumulator
      consumerView consumerFound occurrence | Just target | False =
        let 0 targetJust : (targetFiber @{nameEq} @{keyEq}
              (MkFiber consumerComponent consumerParent False consumerTable
                (Active consumerAccumulator consumerView)) fibers = Just target)
            targetJust = trans
              (targetFiberExplicit nameEq keyEq consumerComponent consumerParent
                False consumerTable (Active consumerAccumulator consumerView)
                fibers) resolved
            0 mismatch : (targetMatches @{nameEq}
              (targetFiber @{nameEq} @{keyEq}
                (MkFiber consumerComponent consumerParent False consumerTable
                  (Active consumerAccumulator consumerView)) fibers)
              consumerView = False)
            mismatch = rewrite targetJust in same
        in activeLeaveFromMismatch nameEq keyEq ambient fibers consumer
          consumerComponent consumerParent False consumerTable
          consumerAccumulator consumerView consumerFound mismatch
    unloadingActiveConsumerMove nameEq keyEq ambient fibers wellFormed provider
      consumer providerComponent providerParent providerRetired providerTable
      providerAccumulator providerView providerOutcome providerFound
      consumerComponent consumerParent False consumerTable consumerAccumulator
      consumerView consumerFound occurrence | Just target | True =
        let targetEqual = viewEqTrueEqual nameEq target consumerView same
            resolvedCommitted = trans resolved (cong Just targetEqual)
            (wanted ** (dependency, providerSelected)) =
              resolveViewOccurrenceProvider nameEq keyEq provider
                (dependencies (componentDependencies consumerComponent))
                consumerView fibers occurrence resolvedCommitted
            providerSound = providerOfSound nameEq keyEq wanted provider fibers
              providerSelected
            sameProviderFiber = justInjective
              (trans (sym providerFound) (providerOfLookup providerSound))
            0 impossibleActive : (False = True)
            impossibleActive = replace
              {p = \selected => isActive (fiberLifecycle selected) = True}
              (sym sameProviderFiber) (providerOfActive providerSound)
        in case impossibleActive of Refl impossible

||| Pre-saturated unloading provider site. Packaging the dependent fields keeps
||| clients from elaborating the expanded theorem's curried spine.
public export
record UnloadingSite
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (provider : name)
  (fibers : Registry name key value world error) where
  constructor MkUnloadingSite
  unloadingSiteComponent : Component key value world error
  unloadingSiteParent : Parent name
  unloadingSiteRetired : Bool
  unloadingSiteTable : OwnedTable key value
    (componentProvisions unloadingSiteComponent)
  unloadingSiteAccumulator : LocalState key value world
      (componentProvisions unloadingSiteComponent) ->
    LocalState key value world (componentProvisions unloadingSiteComponent)
  unloadingSiteView : View name (dependencies
    (componentDependencies unloadingSiteComponent))
  unloadingSiteOutcome : Maybe error
  0 unloadingSiteFound : lookupFiber @{nameEq} provider fibers = Just
    (MkFiber unloadingSiteComponent unloadingSiteParent unloadingSiteRetired
      unloadingSiteTable
      (Unloading unloadingSiteAccumulator unloadingSiteView
        unloadingSiteOutcome))

||| Pre-saturated Active consumer plus its positional reliance witness.
public export
record ActiveRelianceSite
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (provider : name)
  (fibers : Registry name key value world error) where
  constructor MkActiveRelianceSite
  activeSiteConsumer : name
  activeSiteComponent : Component key value world error
  activeSiteParent : Parent name
  activeSiteRetired : Bool
  activeSiteTable : OwnedTable key value
    (componentProvisions activeSiteComponent)
  activeSiteAccumulator : LocalState key value world
      (componentProvisions activeSiteComponent) ->
    LocalState key value world (componentProvisions activeSiteComponent)
  activeSiteView : View name (dependencies
    (componentDependencies activeSiteComponent))
  0 activeSiteFound : lookupFiber @{nameEq} activeSiteConsumer fibers = Just
    (MkFiber activeSiteComponent activeSiteParent activeSiteRetired
      activeSiteTable (Active activeSiteAccumulator activeSiteView))
  0 activeSiteOccurrence : ViewProviderOccurrence provider
    (dependencies (componentDependencies activeSiteComponent)) activeSiteView

||| Monomorphic same-module specialization of the direct Active clause.
public export
0 unloadingActiveSitesMove :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} (MkSystemState ambient fibers) = True ->
  (provider : name) ->
  UnloadingSite name key world error value nameEq provider fibers ->
  ActiveRelianceSite name key world error value nameEq provider fibers ->
  LifecycleMove {name = name} {key = key} {value = value} {world = world}
    {error = error} nameEq keyEq (MkSystemState ambient fibers)
unloadingActiveSitesMove nameEq keyEq ambient fibers wellFormed provider
  (MkUnloadingSite providerComponent providerParent providerRetired
    providerTable providerAccumulator providerView providerOutcome providerFound)
  (MkActiveRelianceSite consumer consumerComponent consumerParent
    consumerRetired consumerTable consumerAccumulator consumerView consumerFound
    occurrence) =
      the (LifecycleMove nameEq keyEq (MkSystemState ambient fibers))
        (unloadingActiveConsumerMove nameEq keyEq ambient fibers wellFormed
          provider consumer providerComponent providerParent providerRetired
          providerTable providerAccumulator providerView providerOutcome
          providerFound consumerComponent consumerParent consumerRetired
          consumerTable consumerAccumulator consumerView consumerFound occurrence)

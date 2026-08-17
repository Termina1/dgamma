module DGamma.CP4ProgressUnloadingClassify

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4ProgressReliance
import DGamma.CP4ProgressUnloadingShape
import DGamma.CP4ProgressUnloadingActive
import DGamma.CP4ProgressUnloadingActiveStep
import DGamma.CP4ProgressUnloadingReloading
import Decidable.Equality

%default total

||| Classify the concrete consumer reflected from a true unloading reliance.
||| The reflection module already rules out Inactive and records the exact
||| committed lifecycle shape, so this eliminator performs no projection search.
public export
0 classifyUnloadingConsumer :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} (MkSystemState ambient fibers) = True ->
  (provider : name) ->
  UnloadingSite name key world error value nameEq provider fibers ->
  ReliedConsumer {name = name} {key = key} {value = value} {world = world}
    {error = error} nameEq provider (MkSystemState ambient fibers) ->
  UnloadingStep name key world error value nameEq keyEq provider
    (MkSystemState ambient fibers)
classifyUnloadingConsumer nameEq keyEq ambient fibers wellFormed provider
  unloading
  (MkReliedConsumer consumer fiber found distinct view committed occurrence edge
    shape) = case shape of
      CommittedReloading component parent retiredFlag table remaining accumulator
        view =>
          the (UnloadingStep name key world error value nameEq keyEq provider
                (MkSystemState ambient fibers))
            (unloadingReloadingConsumerStep nameEq keyEq
              (MkSystemState ambient fibers) wellFormed provider consumer
              component parent retiredFlag table remaining accumulator view found)
      CommittedActive component parent retiredFlag table accumulator view =>
        let active : ActiveRelianceSite name key world error value nameEq provider
              fibers
            active = MkActiveRelianceSite consumer component parent retiredFlag
              table accumulator view found occurrence
        in the (UnloadingStep name key world error value nameEq keyEq provider
              (MkSystemState ambient fibers))
            (unloadingActiveConsumerStep nameEq keyEq ambient fibers wellFormed
              provider unloading active)
      CommittedUnloading component parent retiredFlag table accumulator view
        outcome =>
          SmallerUnloading consumer
            (MkFiber component parent retiredFlag table
              (Unloading accumulator view outcome)) found UnloadingNow edge

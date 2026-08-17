module DGamma.CP4ProgressUnloadingActiveStep

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP4ProgressUnloadingShape
import DGamma.CP4ProgressUnloadingActive
import Decidable.Equality

%default total

||| Package the saturated Active clause as an immediate descent result.
public export
0 unloadingActiveConsumerStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} (MkSystemState ambient fibers) = True ->
  (provider : name) ->
  UnloadingSite name key world error value nameEq provider fibers ->
  ActiveRelianceSite name key world error value nameEq provider fibers ->
  UnloadingStep name key world error value nameEq keyEq provider
    (MkSystemState ambient fibers)
unloadingActiveConsumerStep nameEq keyEq ambient fibers wellFormed provider
  unloading active =
    ImmediateMove
      (the (LifecycleMove {name = name} {key = key} {value = value}
          {world = world} {error = error} nameEq keyEq
          (MkSystemState ambient fibers))
        (unloadingActiveSitesMove nameEq keyEq ambient fibers wellFormed provider
          unloading active))

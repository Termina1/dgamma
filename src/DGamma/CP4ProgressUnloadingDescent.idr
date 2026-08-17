module DGamma.CP4ProgressUnloadingDescent

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4ProgressFinite
import DGamma.CP4ProgressReliance
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP4ProgressUnloadingShape
import DGamma.CP4ProgressUnloadingActive
import DGamma.CP4ProgressUnloadingClassify
import Control.WellFounded
import Decidable.Equality

%default total

||| A blocked Unloading fiber follows an actual reliance/precedence edge. The
||| accessibility proof permits recursion on the relying consumer; classified
||| non-Unloading consumers already carry an immediate evaluator move.
public export
0 unloadingLifecycleMoveAccessible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} (MkSystemState ambient fibers) = True ->
  (provider : name) -> (providerFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} provider fibers = Just providerFiber ->
  IsUnloadingFiber {value = value} providerFiber ->
  (0 accessible : Accessible
    (PrecedenceSuccessor {name = name} {key = key} {value = value}
      {world = world} {error = error} nameEq (MkSystemState ambient fibers))
    provider) ->
  LifecycleMove {name = name} {key = key} {value = value} {world = world}
    {error = error} nameEq keyEq (MkSystemState ambient fibers)
unloadingLifecycleMoveAccessible nameEq keyEq ambient fibers wellFormed provider
  (MkFiber component parent retiredFlag table
    (Unloading accumulator view outcome)) found UnloadingNow (Access smaller)
  with (the Bool (relied @{nameEq} {key = key} {value = value}
    {world = world} {error = error} provider fibers)) proof reliance
  unloadingLifecycleMoveAccessible nameEq keyEq ambient fibers wellFormed provider
    (MkFiber component parent retiredFlag table
      (Unloading accumulator view outcome)) found UnloadingNow
    (Access smaller) | False =
      unloadLifecycleMove nameEq keyEq (MkSystemState ambient fibers) wellFormed
        provider component parent retiredFlag table accumulator view outcome
        found reliance
  unloadingLifecycleMoveAccessible nameEq keyEq ambient fibers wellFormed provider
    fiber@(MkFiber component parent retiredFlag table
      (Unloading accumulator view outcome)) found UnloadingNow
    (Access smaller) | True =
      let 0 unloading : UnloadingSite name key world error value nameEq provider
            fibers
          unloading = MkUnloadingSite component parent retiredFlag table
            accumulator view outcome found
          0 consumer : ReliedConsumer {name = name} {key = key}
            {value = value} {world = world} {error = error} nameEq provider
            (MkSystemState ambient fibers)
          consumer = DGamma.CP4ProgressReliance.reliedConsumerWitness nameEq keyEq
            (MkSystemState ambient fibers) wellFormed provider
            (MkFiber component parent retiredFlag table
              (Unloading accumulator view outcome)) found reliance
          0 step : UnloadingStep name key world error value nameEq keyEq provider
            (MkSystemState ambient fibers)
          step = classifyUnloadingConsumer nameEq keyEq ambient fibers wellFormed
            provider unloading consumer
      in case step of
        ImmediateMove move => move
        SmallerUnloading next nextFiber nextFound nextShape edge =>
          unloadingLifecycleMoveAccessible nameEq keyEq ambient fibers wellFormed
            next nextFiber nextFound nextShape (smaller next edge)

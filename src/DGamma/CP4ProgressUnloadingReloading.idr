module DGamma.CP4ProgressUnloadingReloading

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP4ProgressUnloadingShape
import Decidable.Equality

%default total

||| The Reloading clause of the reliance descent: L-Advance is applicable at
||| every well-formed source, including its L-Divert/L-Raise landing cases.
public export
0 unloadingReloadingConsumerStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} state = True ->
  (provider, consumer : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world
      (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  lookupFiber @{nameEq} consumer (registry state) = Just
    (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator view)) ->
  UnloadingStep name key world error value nameEq keyEq provider state
unloadingReloadingConsumerStep nameEq keyEq state wellFormed provider consumer
  component parent retiredFlag table remaining accumulator view found =
    ImmediateMove
      (the (LifecycleMove nameEq keyEq state)
        (reloadingLifecycleMove nameEq keyEq state wellFormed consumer component
          parent retiredFlag table remaining accumulator view found))

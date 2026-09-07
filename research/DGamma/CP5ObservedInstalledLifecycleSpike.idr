module DGamma.CP5ObservedInstalledLifecycleSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Metatheory
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Runtime observation owned by an ACTUAL registry lookup and lifecycle value.
||| Callbacks are carried from that observed payload; none is reconstructed
||| from a guessed extensionally equivalent expression. Proof fields erase.
||| R181 post-B A12: distinct prerequisite, not the exhausted A11 cut tuple.
public export
record InstalledCutObservation
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (actor : name)
  (state : SystemState name key value world error) where
  constructor MkInstalledCutObservation
  observedInstalledFiber : Fiber name key value world error
  0 observedInstalledLookup : lookupFiber {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq} actor (registry state) =
      Just observedInstalledFiber
  observedInstalledLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent observedInstalledFiber)))
    (componentProvisions (fiberComponent observedInstalledFiber))
  0 observedInstalledLifecycleEquation :
    fiberLifecycle observedInstalledFiber = observedInstalledLifecycle
  0 observedLifecycleInstalled : installed observedInstalledLifecycle = True

||| Executable observer: the producer supplies lookupFiber itself and Refl.
||| Exact callback values come from the observed Fiber, never hand-written undo.
public export
inspectInstalledCutObserved :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (actor : name) ->
  (state : SystemState name key value world error) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (0 found : (lookupFiber {name = name} {key = key} {value = value} {world = world}
    {error = error} @{nameEq} actor (registry state) = observed)) ->
  Maybe (InstalledCutObservation name key world error value nameEq actor state)
inspectInstalledCutObserved name key world error value nameEq actor state Nothing found =
  Nothing
inspectInstalledCutObserved name key world error value nameEq actor state
  (Just (MkFiber component parent retiredFlag table (Inactive outcome))) found = Nothing
inspectInstalledCutObserved name key world error value nameEq actor state
  (Just (MkFiber component parent retiredFlag table (Reloading remaining accumulator view)))
  found = Just (MkInstalledCutObservation
    (MkFiber component parent retiredFlag table (Reloading remaining accumulator view))
    found (Reloading remaining accumulator view) Refl Refl)
inspectInstalledCutObserved name key world error value nameEq actor state
  (Just (MkFiber component parent retiredFlag table (Active accumulator view))) found =
    Just (MkInstalledCutObservation
      (MkFiber component parent retiredFlag table (Active accumulator view))
      found (Active accumulator view) Refl Refl)
inspectInstalledCutObserved name key world error value nameEq actor state
  (Just (MkFiber component parent retiredFlag table (Unloading accumulator view outcome)))
  found = Just (MkInstalledCutObservation
    (MkFiber component parent retiredFlag table (Unloading accumulator view outcome))
    found (Unloading accumulator view outcome) Refl Refl)

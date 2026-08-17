module DGamma.CP4ProgressUnloadingShape

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import Decidable.Equality

%default total

||| Compact indexed evidence that a fiber is in the Unloading lifecycle.
public export
data IsUnloadingFiber : {name, key, world, error : Type} ->
  {value : key -> Type} -> Fiber name key value world error -> Type where
  UnloadingNow :
    IsUnloadingFiber
      (MkFiber component parent retiredFlag table
        (Unloading accumulator view outcome))

||| Compact indexed evidence that a fiber is in the Active lifecycle.
public export
data IsActiveFiber : {name, key, world, error : Type} ->
  {value : key -> Type} -> Fiber name key value world error -> Type where
  ActiveNow :
    IsActiveFiber
      (MkFiber component parent retiredFlag table (Active accumulator view))

||| Classified successor of one blocked Unloading provider.
public export
data UnloadingStep :
  (0 name : Type) -> (0 key : Type) -> (0 world : Type) ->
  (0 error : Type) -> (0 value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (provider : name) ->
  (state : SystemState name key value world error) -> Type where
  ImmediateMove :
    LifecycleMove nameEq keyEq state ->
    UnloadingStep name key world error value nameEq keyEq provider state
  SmallerUnloading :
    (consumer : name) -> (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} consumer (registry state) = Just fiber ->
    IsUnloadingFiber fiber ->
    PrecedenceEdge nameEq provider consumer state ->
    UnloadingStep name key world error value nameEq keyEq provider state

module DGamma.L2R13InsertExtensional

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.L2R2CheckedSnapshot
import DGamma.L2R4InsertReplay
import DGamma.L2R5Extensional
import DGamma.L2R5ExtensionalRetire
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| One native observed lookup decision frames identical fresh insertions
||| over extensionally equal registries. No lookup congruence is postulated.
export
0 insertLookupExtensionalObserved : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (wanted, actor : name) ->
  (fiber : Fiber name key value world error) ->
  (left, right : SystemState name key value world error) ->
  (0 same : RegistryExtensional name key world error value nameEq left right) ->
  (0 leftAbsent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry left) = Nothing) ->
  (0 rightAbsent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry right) = Nothing) ->
  (decision : Dec (wanted = actor)) -> (0 equation : decEq @{nameEq} wanted actor = decision) ->
  lookupFiber {name} {key} {value} {world} {error} @{nameEq} wanted
    (insertBinding @{nameEq} actor fiber (registry left) leftAbsent) =
  lookupFiber {name} {key} {value} {world} {error} @{nameEq} wanted
    (insertBinding @{nameEq} actor fiber (registry right) rightAbsent)
insertLookupExtensionalObserved {name} {key} {world} {error} {value}
  nameEq wanted actor fiber left right same leftAbsent rightAbsent (Yes equal) equation =
  replace {p = \selected => lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected
      (insertBinding @{nameEq} actor fiber (registry left) leftAbsent) =
    lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected
      (insertBinding @{nameEq} actor fiber (registry right) rightAbsent)} (sym equal)
    (trans (lookupInserted {key = name} {value = FiberAt name key value world error} @{nameEq}
      actor fiber (registry left) leftAbsent)
      (sym (lookupInserted {key = name} {value = FiberAt name key value world error} @{nameEq}
        actor fiber (registry right) rightAbsent)))
insertLookupExtensionalObserved {name} {key} {world} {error} {value}
  nameEq wanted actor fiber left right same leftAbsent rightAbsent (No different) equation =
  trans (lookupInsertOther {key = name} {value = FiberAt name key value world error} @{nameEq}
    wanted actor different fiber (registry left) leftAbsent)
    (trans (extensionalLookup same wanted)
      (sym (lookupInsertOther {key = name} {value = FiberAt name key value world error} @{nameEq}
        wanted actor different fiber (registry right) rightAbsent)))

||| Extensional successor relation for a fresh binding, with right absence
||| DERIVED from the original lookup. Applicability guards are separate.
export
0 freshInsertExtensional : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) -> (fiber : Fiber name key value world error) ->
  (left, right : SystemState name key value world error) ->
  (0 same : RegistryExtensional name key world error value nameEq left right) ->
  (0 absent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry left) = Nothing) ->
  RegistryExtensional name key world error value nameEq
    (MkSystemState (worldState left) (insertBinding @{nameEq} actor fiber (registry left) absent))
    (MkSystemState (worldState right) (insertBinding @{nameEq} actor fiber (registry right)
      (trans (sym (extensionalLookup same actor)) absent)))
freshInsertExtensional nameEq actor fiber left right same absent =
  MkRegistryExtensional (extensionalWorld same)
    (\wanted => insertLookupExtensionalObserved nameEq wanted actor fiber left right same absent
      (trans (sym (extensionalLookup same actor)) absent) (decEq @{nameEq} wanted actor) Refl)

||| Erased uniqueness evidence does not enter the native inserted snapshot.
export
0 freshInsertSnapshot : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) -> (fiber : Fiber name key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (0 absent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor source = Nothing) ->
  runtimeSnapshot {name} {key} {world} {error} {value}
    (MkSystemState ambient (insertBinding @{nameEq} actor fiber source absent)) =
  MkRuntimeSnapshot ambient (Bind actor fiber :: bindings source)
freshInsertSnapshot nameEq actor fiber ambient (MkCoeffectContext entries unique) absent = Refl

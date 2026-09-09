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

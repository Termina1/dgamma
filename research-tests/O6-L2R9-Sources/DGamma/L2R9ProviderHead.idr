module DGamma.L2R9ProviderHead

import DGamma.Calculus
import DGamma.Coeffects
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| TYPE/shape copied with distinct lane names from main commit40d0d59e,
||| research/DGamma/CP5ProviderHeadObservedSpike.idr: ProviderHeadObserved.
||| Only the TYPE is copied here; no main module is edited or duplicated.
||| The observed guard and BOTH native head equations are retained exactly.
public export
record LaneProviderHeadObserved
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (wanted : key) (actor : name)
  (component : Component key value world error) (parent : Parent name) (flag : Bool)
  (table : OwnedTable key value (componentProvisions component))
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component)) (componentProvisions component))
  (rest : List (Binding name (FiberAt name key value world error))) where
  constructor MkLaneProviderHeadObserved
  laneHeadSeen : Bool
  0 laneHeadGuardEquation :
    ((isActive lifecycle && memberKey @{keyEq} wanted (ownedValues table)) = laneHeadSeen)
  0 laneBeforeHeadEquation :
    (providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted
      (Bind actor (MkFiber component parent flag table lifecycle) :: rest) =
      (if laneHeadSeen then Just actor else
        providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted rest))
  0 laneRetiredHeadEquation :
    (providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted
      (Bind actor (MkFiber component parent True table lifecycle) :: rest) =
      (if laneHeadSeen then Just actor else
        providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted rest))


||| Lane-native direct packet producer: eliminate the observed Bool BEFORE
||| constructing the guard-indexed record. Both native providerIn equations
||| are derived in that concrete branch; no projected-if consumer interface.
public export
laneHeadAtGuard :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (actor : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (flag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  (seen : Bool) ->
  (0 equation : (isActive lifecycle && memberKey @{keyEq} wanted (ownedValues table)) = seen) ->
  LaneProviderHeadObserved name key world error value nameEq keyEq wanted actor component parent flag table lifecycle rest
laneHeadAtGuard nameEq keyEq wanted actor component parent flag table lifecycle rest False equation =
  MkLaneProviderHeadObserved False equation (rewrite equation in Refl) (rewrite equation in Refl)
laneHeadAtGuard nameEq keyEq wanted actor component parent flag table lifecycle rest True equation =
  MkLaneProviderHeadObserved True equation (rewrite equation in Refl) (rewrite equation in Refl)

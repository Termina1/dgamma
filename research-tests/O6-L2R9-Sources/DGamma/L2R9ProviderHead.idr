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

||| GENERAL unrestricted observed-head producer; no supplied guard/native
||| head proof premise. The own call-site equation is generated here.
public export
laneProviderHeadObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (actor : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (flag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  LaneProviderHeadObserved name key world error value nameEq keyEq wanted actor component parent flag table lifecycle rest
laneProviderHeadObserved nameEq keyEq wanted actor component parent flag table lifecycle rest =
  laneHeadAtGuard nameEq keyEq wanted actor component parent flag table lifecycle rest
    (isActive lifecycle && memberKey @{keyEq} wanted (ownedValues table)) Refl

||| Explicit observed-Bool eliminator used by the native-head consumer.
||| There is no projected if-guard, and transitivity is applied only after
||| the condition has become a constructor (both endpoints share a value).
export
0 laneNativeAtBool : {a : Type} ->
  (seen : Bool) -> (present, absent, before, after : a) ->
  (0 beforeEquation : before = (if seen then present else absent)) ->
  (0 afterEquation : after = (if seen then present else absent)) -> before = after
laneNativeAtBool False present absent before after beforeEquation afterEquation = trans beforeEquation (sym afterEquation)
laneNativeAtBool True present absent before after beforeEquation afterEquation = trans beforeEquation (sym afterEquation)

||| Dependent elimination of the ALREADY observed Bool. Unlike D4's generic
||| conditional equality interface, the family can carry just an equality
||| from the stored observed value, avoiding reconstruction of ANY if type.
||| D4 is checked generic capital; its D5 native splice failed once.
export
0 laneObservedBoolEliminate : (0 family : Bool -> Type) ->
  (whenFalse : family False) -> (whenTrue : family True) -> (seen : Bool) -> family seen
laneObservedBoolEliminate family whenFalse whenTrue False = whenFalse
laneObservedBoolEliminate family whenFalse whenTrue True = whenTrue

||| NEW observed-head consumer (not the frozen bare R4/R5 statement). It
||| eliminates the record once, then the EXPLICIT Bool via laneObservedBoolEliminate.
||| No projected if expression appears in this consumer's interface or body.
export
0 laneProviderHeadSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (actor : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (flag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  LaneProviderHeadObserved name key world error value nameEq keyEq wanted actor component parent flag table lifecycle rest ->
  providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted
    (Bind actor (MkFiber component parent flag table lifecycle) :: rest) =
  providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted
    (Bind actor (MkFiber component parent True table lifecycle) :: rest)
laneProviderHeadSame {name} {key} {world} {error} {value} nameEq keyEq wanted actor component parent flag table lifecycle rest
  (MkLaneProviderHeadObserved seen equation before after) =
  laneObservedBoolEliminate
    (\observed => (0 shape : seen = observed) ->
      providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted
        (Bind actor (MkFiber component parent flag table lifecycle) :: rest) =
      providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted
        (Bind actor (MkFiber component parent True table lifecycle) :: rest))
    (\shape => rewrite (trans equation shape) in Refl)
    (\shape => rewrite (trans equation shape) in Refl) seen Refl

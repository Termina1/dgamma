module DGamma.CP5ProviderHeadObservedSpike

import DGamma.Calculus
import DGamma.Coeffects
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Main-lane renamed copy of the ProviderHeadObservation TYPE from
||| 94273eaab85e4edf0145027418fb0f1c387bb824:
||| research-tests/O6-L2R5-Sources/DGamma/L2R5ProviderObservation.idr.
||| It stores one observed guard with its equation and BOTH native head
||| provider equations. The flag changes to True; the lifecycle is unchanged.
public export
record ProviderHeadObserved
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (wanted : key) (actor : name)
  (component : Component key value world error) (parent : Parent name) (flag : Bool)
  (table : OwnedTable key value (componentProvisions component))
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component)) (componentProvisions component))
  (rest : List (Binding name (FiberAt name key value world error))) where
  constructor MkProviderHeadObserved
  observedHeadGuard : Bool
  0 headGuardEquation :
    ((isActive lifecycle && memberKey @{keyEq} wanted (ownedValues table)) = observedHeadGuard)
  0 beforeHeadEquation :
    (providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted
      (Bind actor (MkFiber component parent flag table lifecycle) :: rest) =
      (if observedHeadGuard then Just actor else
        providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted rest))
  0 retiredHeadEquation :
    (providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted
      (Bind actor (MkFiber component parent True table lifecycle) :: rest) =
      (if observedHeadGuard then Just actor else
        providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted rest))

||| The NATIVE library guard is observed explicitly at this head. Its own
||| equation, not a second Bool case split, transports the provider branch.
export
0 providerInHeadObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (actor : name) ->
  (fiber : Fiber name key value world error) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  (observed : Bool) ->
  ((isActive (fiberLifecycle fiber) &&
    memberKey @{keyEq} wanted (ownedValues (fiberTable fiber))) = observed) ->
  (providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted
    (Bind actor fiber :: rest) =
    (if observed then Just actor else
      providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted rest))
providerInHeadObserved {name} {key} {world} {error} {value}
  nameEq keyEq wanted actor fiber rest True equation =
  rewrite equation in Refl
providerInHeadObserved {name} {key} {world} {error} {value}
  nameEq keyEq wanted actor fiber rest False equation =
  rewrite equation in Refl

||| Constructor assembly AFTER eliminating an explicit observed native guard.
||| The equation belongs to the library guard at the concrete head fiber.
||| This is the observed-value boundary, not an assumed provider equation.
public export
providerHeadPacketAtGuard :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (actor : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (flag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  (observed : Bool) ->
  (0 equation : ((isActive (fiberLifecycle (MkFiber component parent flag table lifecycle)) &&
    memberKey @{keyEq} wanted (ownedValues (fiberTable (MkFiber component parent flag table lifecycle)))) = observed)) ->
  ProviderHeadObserved name key world error value nameEq keyEq wanted actor
    component parent flag table lifecycle rest
providerHeadPacketAtGuard nameEq keyEq wanted actor component parent flag table lifecycle rest True equation =
  MkProviderHeadObserved True equation
    (providerInHeadObserved nameEq keyEq wanted actor
      (MkFiber component parent flag table lifecycle) rest True equation)
    (providerInHeadObserved nameEq keyEq wanted actor
      (MkFiber component parent True table lifecycle) rest True equation)
providerHeadPacketAtGuard nameEq keyEq wanted actor component parent flag table lifecycle rest False equation =
  MkProviderHeadObserved False equation
    (providerInHeadObserved nameEq keyEq wanted actor
      (MkFiber component parent flag table lifecycle) rest False equation)
    (providerInHeadObserved nameEq keyEq wanted actor
      (MkFiber component parent True table lifecycle) rest False equation)

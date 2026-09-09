module DGamma.L2R5ProviderObservation

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| NEW observed-value statement: one explicit provider guard with its exact
||| native equation and BOTH head observations. Unlike exhausted L2R4 B7,
||| the producer must expose the Bool before relating any provider expressions.
public export
record ProviderHeadObservation
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (wanted : key) (actor : name)
  (component : Component key value world error) (parent : Parent name) (flag : Bool)
  (table : OwnedTable key value (componentProvisions component))
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component)) (componentProvisions component))
  (rest : List (Binding name (FiberAt name key value world error))) where
  constructor MkProviderHeadObservation
  observedHeadGuard : Bool
  0 headGuardEquation : isActive lifecycle && memberKey @{keyEq} wanted (ownedValues table) = observedHeadGuard
  0 beforeHeadEquation : providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted
    (Bind actor (MkFiber component parent flag table lifecycle) :: rest) =
    if observedHeadGuard then Just actor else providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted rest
  0 retiredHeadEquation : providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted
    (Bind actor (MkFiber component parent True table lifecycle) :: rest) =
    if observedHeadGuard then Just actor else providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted rest

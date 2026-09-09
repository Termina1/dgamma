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

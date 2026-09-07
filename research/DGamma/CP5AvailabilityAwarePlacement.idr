module DGamma.CP5AvailabilityAwarePlacement

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Declaration occupancy, exactly as in O-Insert: neither retirement nor
||| lifecycle inactivity makes a present provider's declared keys available.
public export
rootDeclaredProvisionsFree :
  (name, key, world, error : Type) -> (value : key -> Type) -> (keyEq : DecEq key) ->
  Component key value world error -> SystemState name key value world error -> Bool
rootDeclaredProvisionsFree name key world error value keyEq component state =
  provisionsDisjointFrom {name = name} {key = key} {value = value} {world = world} {error = error} @{keyEq}
    (componentProvisions component)
    (registryFibers {name = name} {key = key} {value = value} {world = world} {error = error} (registry state))

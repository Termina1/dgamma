module DGamma.L2R5Extensional

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4RuntimeBindings
import Decidable.Equality

%default total
%unbound_implicits off

||| Normalizer-only endpoint relation, authorized by the L2R5 semantic gate.
||| Exact world and every fiber lookup; binding-list order is not required.
||| This neither changes RuntimeSnapshot nor assumes evaluator congruence.
public export
record RegistryExtensional
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name)
  (0 left, right : SystemState name key value world error) where
  constructor MkRegistryExtensional
  0 extensionalWorld : worldState left = worldState right
  0 extensionalLookup : (wanted : name) ->
    lookupFiber {name} {key} {value} {world} {error} @{nameEq} wanted (registry left) =
    lookupFiber {name} {key} {value} {world} {error} @{nameEq} wanted (registry right)

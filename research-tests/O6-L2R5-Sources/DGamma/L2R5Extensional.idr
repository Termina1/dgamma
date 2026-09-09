module DGamma.L2R5Extensional

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4RuntimeBindings
import Data.List.Elem
import Data.Maybe
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

||| Every existing exact-snapshot square embeds without any weakening of its
||| own statement. Pointwise lookup follows by congruence on ordered entries.
export
0 snapshotIntoExtensional :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (left, right : SystemState name key value world error) ->
  (0 same : runtimeSnapshot left = runtimeSnapshot right) ->
  RegistryExtensional name key world error value nameEq left right
snapshotIntoExtensional {name} {key} {world} {error} {value} nameEq
  (MkSystemState ambient (MkCoeffectContext entries unique))
  (MkSystemState otherAmbient (MkCoeffectContext otherEntries otherUnique)) same =
    MkRegistryExtensional (cong snapshotWorld same)
      (\wanted => cong (lookupEntries {key = name} {value = FiberAt name key value world error} @{nameEq} wanted)
        (cong snapshotBindings same))

||| Name-domain membership agrees as a DERIVED equation, not a relation field.
export
0 extensionalMemberKey :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (left, right : SystemState name key value world error) ->
  (0 same : RegistryExtensional name key world error value nameEq left right) ->
  (wanted : name) ->
  memberKey {key = name} {value = FiberAt name key value world error} @{nameEq} wanted (registry left) =
  memberKey {key = name} {value = FiberAt name key value world error} @{nameEq} wanted (registry right)
extensionalMemberKey nameEq left right same wanted = cong isJust (extensionalLookup same wanted)

||| Actual installed declaration occupying a key, regardless of activity or
||| retirement. Runtime witness data, erased lookup/declaration specifications.
||| This is existential declaration occupancy, not the executable scan Bool.
public export
record DeclaredOccupancy
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (wanted : key)
  (0 state : SystemState name key value world error) where
  constructor MkDeclaredOccupancy
  occupyingName : name
  occupyingFiber : Fiber name key value world error
  0 occupyingLookup : lookupFiber {name} {key} {value} {world} {error} @{nameEq}
    occupyingName (registry state) = Just occupyingFiber
  0 occupyingDeclaration : Elem wanted
    (dependencies (componentProvisions (fiberComponent occupyingFiber)))

||| Declaration occupancy agrees in BOTH directions, derived solely from the
||| exact pointwise fiber lookup field. No availability/occupancy oracle field.
||| Equivalence with provisionsDisjointFrom's finite Bool scan is still separate.
export
0 extensionalDeclaredOccupancy :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (left, right : SystemState name key value world error) ->
  (0 same : RegistryExtensional name key world error value nameEq left right) ->
  (wanted : key) ->
  (DeclaredOccupancy name key world error value nameEq wanted left ->
     DeclaredOccupancy name key world error value nameEq wanted right,
   DeclaredOccupancy name key world error value nameEq wanted right ->
     DeclaredOccupancy name key world error value nameEq wanted left)
extensionalDeclaredOccupancy nameEq left right same wanted =
  (\occupied => MkDeclaredOccupancy (occupyingName occupied) (occupyingFiber occupied)
      (trans (sym (extensionalLookup same (occupyingName occupied))) (occupyingLookup occupied))
      (occupyingDeclaration occupied),
   \occupied => MkDeclaredOccupancy (occupyingName occupied) (occupyingFiber occupied)
      (trans (extensionalLookup same (occupyingName occupied)) (occupyingLookup occupied))
      (occupyingDeclaration occupied))

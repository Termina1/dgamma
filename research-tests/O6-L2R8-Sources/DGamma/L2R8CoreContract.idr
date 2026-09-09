module DGamma.L2R8CoreContract

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.L2R5Extensional
import DGamma.L2R6Iteration
import Data.List
import Decidable.Equality

%default total
%unbound_implicits off

||| A physically located contiguous extended actor core. All three native
||| subtraces and their availability trails are authentic, not word labels.
||| Core start/end states need not agree before/after an external root hoist.
public export
record LocatedExtendedCore
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (actor : name)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState) where
  constructor MkLocatedExtendedCore
  coreStart : SystemState name key value world error
  coreEnd : SystemState name key value world error
  beforeCore : Transitions initial coreStart
  nativeCore : Transitions coreStart coreEnd
  afterCore : Transitions coreEnd finalState
  beforeCoreTrail : AvailabilityTrace name key world error value beforeCore
  coreTrail : AvailabilityTrace name key world error value nativeCore
  afterCoreTrail : AvailabilityTrace name key world error value afterCore
  0 coreActorOnly : ActorLifecycleOnlyExtended nameEq actor nativeCore
  0 corePhysicalSplit : appendTransitions beforeCore (appendTransitions nativeCore afterCore) = global

||| Precise GENERAL coreContiguityRestored obligation TYPE ONLY. Both runs
||| are native from one origin; a single foreign root moves from just after
||| the old core to just before it, preserving the exact surrounding word.
||| The conclusion PRODUCES a located, source-aware extended core at +1 and
||| exact core ACTION-WORD equality, plus extensional WHOLE-run endpoints.
||| No equality of incompatible core endpoint states is requested or assumed.
||| No native fixture/general proof is supplied: B3 normalization is deferred.
public export
GeneralCoreContiguityRestored : {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, oldFinal, newFinal : SystemState name key value world error} ->
  {oldTrace : Transitions initial oldFinal} -> {newTrace : Transitions initial newFinal} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  AvailabilityTrace name key world error value oldTrace ->
  AvailabilityTrace name key world error value newTrace -> Type
GeneralCoreContiguityRestored {name} {key} {world} {error} {value} {initial} {oldFinal} {newFinal}
  {oldTrace} {newTrace} nameEq keyEq oldTrail newTrail =
  (0 valid : registryWellFormed @{nameEq} @{keyEq} initial = True) ->
  (actor, root : name) -> (component : Component key value world error) ->
  (0 foreign : root = actor -> Void) ->
  (oldCore : LocatedExtendedCore name key world error value nameEq actor oldTrace) ->
  (suffix : List (Action name key value world error)) ->
  (0 afterExact : nativeActionWord (afterCoreTrail oldCore) = OInsert root Root component :: suffix) ->
  (0 newWordExact : nativeActionWord newTrail = nativeActionWord (beforeCoreTrail oldCore) ++
    OInsert root Root component :: (nativeActionWord (coreTrail oldCore) ++ suffix)) ->
  (restored : LocatedExtendedCore name key world error value nameEq actor newTrace **
    (nativeActionWord (coreTrail restored) = nativeActionWord (coreTrail oldCore),
     transitionCount (beforeCore restored) = S (transitionCount (beforeCore oldCore)),
     RegistryExtensional name key world error value nameEq oldFinal newFinal))

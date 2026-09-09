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

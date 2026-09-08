module DGamma.L2R2ForeignReplay

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2CheckedSnapshot
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| A genuinely replayed native trace, including early child retirement and
||| every foreign edge. The runtime endpoint equals the original endpoint
||| after child retirement at the world/ordered-binding level. This result
||| package alone supplies no commutation or normalization oracle.
public export
record RetirementReplay
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (child : name)
  (fiber : Fiber name key value world error)
  {first, finalState : SystemState name key value world error}
  (original : Transitions first finalState) where
  constructor MkRetirementReplay
  relocatedFinal : SystemState name key value world error
  relocatedTrace : Transitions first relocatedFinal
  0 relocatedCount : transitionCount relocatedTrace = S (transitionCount original)
  0 relocatedSnapshot : runtimeSnapshot relocatedFinal =
    runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState finalState)
        (replaceBinding @{nameEq} child (retireFiber fiber) (registry finalState)))

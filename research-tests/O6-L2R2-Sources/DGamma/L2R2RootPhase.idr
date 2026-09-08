module DGamma.L2R2RootPhase

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5L2R1RootExchange
import DGamma.L2R2RootSnapshot
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R2SmallPlacement
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| CP3:577 supportSet depends only on ordered runtime bindings. Therefore a
||| snapshot-preserving root exchange preserves the ENTIRE executable support
||| set, without postulating equality of erased UniqueKeys witnesses.
export
0 supportSetAcrossSnapshot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (left, right : SystemState name key value world error) ->
  (0 same : runtimeSnapshot left = runtimeSnapshot right) ->
  supportSet @{nameEq} @{keyEq} left = supportSet @{nameEq} @{keyEq} right
supportSetAcrossSnapshot {name} {key} {world} {error} {value} nameEq keyEq left right same =
  cong (\snapshot => supportFuel {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (length (snapshotBindings snapshot)) (snapshotBindings snapshot) []) same

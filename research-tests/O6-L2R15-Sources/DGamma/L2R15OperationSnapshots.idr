module DGamma.L2R15OperationSnapshots

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP4RuntimeBindings
import Data.List
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Arbitrary-registry replacement has its exact raw binding snapshot.
||| The erased uniqueness certificate is never compared across constructions.
||| This single operation lemma serves actor updates and child retirement.
export
0 nativeReplaceSnapshot : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) -> (fiber : Fiber name key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  runtimeSnapshot {name} {key} {world} {error} {value}
    (MkSystemState ambient (replaceBinding @{nameEq} actor fiber source)) =
  MkRuntimeSnapshot ambient (replaceEntries @{nameEq} actor fiber (bindings source))
nativeReplaceSnapshot nameEq actor fiber ambient (MkCoeffectContext entries unique) = Refl

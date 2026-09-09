module DGamma.L2R3Separation

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.L2R3Attached
import DGamma.L2R3AttachedGap
import DGamma.L2R3FixtureCoverage
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| A genuine all-bundle no-straddling proof would discharge the unchanged
||| interval-separation obligation at an empty residual gap. Observe the
||| end<=cut decision ONCE; if false, no-straddling forces cut<=start.
||| This is CONDITIONAL: NoBundleStraddlesCut is not produced for either
||| fixture here. Selected catalog endpoints cannot replace that premise.
export
0 separateBundleObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, finalState : SystemState name key value world error} ->
  {global : Transitions initial finalState} ->
  (cut : Nat) -> (action : Action name key value world error) -> (ordinal : Nat) ->
  (member : AttachedBundleOccurrence name key world error value nameEq keyEq global action ordinal) ->
  (0 noStraddling : NoBundleStraddlesCut nameEq keyEq global cut) ->
  Dec (LTE (bundleOffset member + transitionCount (memberBundle member)) cut) ->
  Either (LTE (bundleOffset member + transitionCount (memberBundle member)) cut)
    (LTE cut (bundleOffset member))
separateBundleObserved cut action ordinal member noStraddling (Yes endsBefore) = Left endsBefore
separateBundleObserved cut action ordinal member noStraddling (No endsAfter) =
  Right (notLTImpliesGTE (\startsBefore =>
    noStraddling action ordinal member startsBefore (notLTEImpliesGT endsAfter)))

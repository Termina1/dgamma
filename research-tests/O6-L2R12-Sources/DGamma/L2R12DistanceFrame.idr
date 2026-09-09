module DGamma.L2R12DistanceFrame

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.Num
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R6Anchors
import DGamma.L2R6DistanceDecrease
import Data.List
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Derive EXACT-ONE total decrease from a stable target, a below-cut bound,
||| and authenticated decomposition of the two ACTUAL totalDistance scans.
||| The global decomposition/untouched-root transport equations are explicit
||| premises, NOT produced here or disguised as an AdmittedDistanceMove.
export
0 totalDistanceOneLeftFromFrame : {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, oldFinal, newFinal : SystemState name key value world error} ->
  {oldTrace : Transitions initial oldFinal} -> {newTrace : Transitions initial newFinal} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (oldTrail : AvailabilityTrace name key world error value oldTrace) ->
  (newTrail : AvailabilityTrace name key world error value newTrace) ->
  (position, target, untouched : Nat) -> (0 bounded : LTE target position) ->
  (0 oldFrame : totalDistance nameEq keyEq oldTrail = minus (S position) target + untouched) ->
  (0 newFrame : totalDistance nameEq keyEq newTrail = minus position target + untouched) ->
  totalDistance nameEq keyEq oldTrail = S (totalDistance nameEq keyEq newTrail)
totalDistanceOneLeftFromFrame nameEq keyEq oldTrail newTrail position target untouched bounded oldFrame newFrame =
  trans oldFrame (trans (cong (\distance => distance + untouched)
    (distanceOneLeft {position} {target} bounded)) (sym (cong S newFrame)))

module DGamma.L2R8IterationArithmetic

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R6Iteration
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Count a GIVEN finite native iteration. Not normalization; move/phase
||| producers open. The iteration proof and this specification count erase.
public export
0 iterationSteps : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, oldFinal, newFinal : SystemState name key value world error} ->
  {oldTrace : Transitions initial oldFinal} -> {newTrace : Transitions initial newFinal} ->
  {oldTrail : AvailabilityTrace name key world error value oldTrace} ->
  {newTrail : AvailabilityTrace name key world error value newTrace} ->
  DistanceIteration nameEq keyEq oldTrail newTrail -> Nat
iterationSteps (IterationDone trail) = 0
iterationSteps (IterationMove move later) = S (iterationSteps later)

||| Exact physical-distance balance for ANY given finite native iteration.
||| Not normalization; move/phase producers open. No per-step oracle is used:
||| this consumes actual AdmittedDistanceMove evidence in the finite chain.
export
0 iterationDistanceBalance : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, oldFinal, newFinal : SystemState name key value world error} ->
  {oldTrace : Transitions initial oldFinal} -> {newTrace : Transitions initial newFinal} ->
  {oldTrail : AvailabilityTrace name key world error value oldTrace} ->
  {newTrail : AvailabilityTrace name key world error value newTrace} ->
  (iteration : DistanceIteration nameEq keyEq oldTrail newTrail) ->
  totalDistance nameEq keyEq oldTrail = iterationSteps iteration + totalDistance nameEq keyEq newTrail
iterationDistanceBalance (IterationDone trail) = Refl
iterationDistanceBalance (IterationMove move later) =
  trans (beforeDistanceEquation move)
    (trans (dropsExactlyOne move)
      (cong S (trans (sym (afterDistanceEquation move)) (iterationDistanceBalance later))))

||| A supplied zero-distance terminal chain has EXACTLY the initial distance
||| many steps. Not normalization; move/phase producers open. This does not
||| produce the chain, its terminal zero, placement, or AttachedNormalForm.
export
0 iterationStepsAtZero : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, oldFinal, newFinal : SystemState name key value world error} ->
  {oldTrace : Transitions initial oldFinal} -> {newTrace : Transitions initial newFinal} ->
  {oldTrail : AvailabilityTrace name key world error value oldTrace} ->
  {newTrail : AvailabilityTrace name key world error value newTrace} ->
  (iteration : DistanceIteration nameEq keyEq oldTrail newTrail) ->
  (0 zero : totalDistance nameEq keyEq newTrail = 0) ->
  iterationSteps iteration = totalDistance nameEq keyEq oldTrail
iterationStepsAtZero iteration zero = sym
  (trans (iterationDistanceBalance iteration)
    (trans (cong (iterationSteps iteration +) zero) (plusZeroRightNeutral (iterationSteps iteration))))

||| Every given finite iteration is bounded by its initial physical distance.
||| Not normalization; move/phase producers open. No accessibility recursion
||| or chain-existence claim is smuggled into this arithmetic consequence.
export
0 iterationLengthBound : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, oldFinal, newFinal : SystemState name key value world error} ->
  {oldTrace : Transitions initial oldFinal} -> {newTrace : Transitions initial newFinal} ->
  {oldTrail : AvailabilityTrace name key world error value oldTrace} ->
  {newTrail : AvailabilityTrace name key world error value newTrace} ->
  (iteration : DistanceIteration nameEq keyEq oldTrail newTrail) ->
  LTE (iterationSteps iteration) (totalDistance nameEq keyEq oldTrail)
iterationLengthBound {nameEq} {keyEq} {newTrail} iteration =
  replace {p = \n => LTE (iterationSteps iteration) n} (sym (iterationDistanceBalance iteration))
    (lteAddRight {m = totalDistance nameEq keyEq newTrail} (iterationSteps iteration))

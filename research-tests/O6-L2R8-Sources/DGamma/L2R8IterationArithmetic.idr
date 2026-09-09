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

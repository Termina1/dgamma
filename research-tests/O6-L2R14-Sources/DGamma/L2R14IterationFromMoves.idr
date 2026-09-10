module DGamma.L2R14IterationFromMoves

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R6Iteration
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| The numerical witnesses of ANY two actual moves over the SAME trails
||| agree, by their producer-owned exact equations. This is not proof-record
||| equality and does not identify arbitrary move roots or crossing locations.
export
0 admittedMoveMeasuresUnique : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, oldFinal, newFinal : SystemState name key value world error} ->
  {oldTrace : Transitions initial oldFinal} -> {newTrace : Transitions initial newFinal} ->
  {oldTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value oldTrace} ->
  {newTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value newTrace} ->
  (left, right : AdmittedDistanceMove name key world error value nameEq keyEq oldTrail newTrail) ->
  (beforeDistance left = beforeDistance right, afterDistance left = afterDistance right)
admittedMoveMeasuresUnique left right =
  (trans (sym (beforeDistanceEquation left)) (beforeDistanceEquation right),
   trans (sym (afterDistanceEquation left)) (afterDistanceEquation right))

module DGamma.L2R8NativeWords

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R6Iteration
import Data.List

%default total
%unbound_implicits off

||| General physical count of the full native action word. Unlike an external
||| root-only projection, this retains child controls and every lifecycle.
export
0 nativeWordCount : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (trail : AvailabilityTrace name key world error value trace) ->
  length (nativeActionWord trail) = transitionCount trace
nativeWordCount (AvailabilityEnd state) = Refl
nativeWordCount (AvailabilityStep source (Fired ne ke action tag checked) rest later) =
  cong S (nativeWordCount later)

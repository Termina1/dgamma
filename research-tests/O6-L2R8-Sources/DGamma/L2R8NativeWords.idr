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

||| Executable native trail concatenation. No transition is replayed or
||| invented: the shared middle state is literally the same index.
public export
appendAvailability : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, middle, finalState : SystemState name key value world error} ->
  {0 left : Transitions first middle} -> {0 right : Transitions middle finalState} ->
  AvailabilityTrace name key world error value left ->
  AvailabilityTrace name key world error value right ->
  AvailabilityTrace name key world error value (appendTransitions left right)
appendAvailability (AvailabilityEnd state) rightTrail = rightTrail
appendAvailability {right} (AvailabilityStep source step rest later) rightTrail =
  AvailabilityStep source step (appendTransitions rest right) (appendAvailability later rightTrail)

||| GENERAL action-word transport through native concatenation. This proves
||| the physical decomposition connector, not core restoration after a swap.
export
0 nativeWordAppend : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {left : Transitions first middle} -> {right : Transitions middle finalState} ->
  (leftTrail : AvailabilityTrace name key world error value left) ->
  (rightTrail : AvailabilityTrace name key world error value right) ->
  nativeActionWord (appendAvailability leftTrail rightTrail) =
    nativeActionWord leftTrail ++ nativeActionWord rightTrail
nativeWordAppend (AvailabilityEnd state) rightTrail = Refl
nativeWordAppend (AvailabilityStep source (Fired ne ke action tag checked) rest later) rightTrail =
  cong (action ::) (nativeWordAppend later rightTrail)

module DGamma.L2R4OrdinalObservation

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Data.Nat
import Data.Maybe

%default total
%unbound_implicits off

||| One Nat elimination for a finite trace observation; zero observes the
||| supplied head, successor delegates to the structurally smaller tail.
public export
observeOrdinalHead : {a : Type} -> a -> (Nat -> Maybe a) -> Nat -> Maybe a
observeOrdinalHead head later Z = Just head
observeOrdinalHead head later (S n) = later n

||| Total action-lookup specification in the actual checked trace. Out of
||| bounds returns Nothing; recursion consumes one Transition. Erased because
||| inherited transitionAction requires endpoint indices erased by Transitions.
public export
0 nativeActionAt :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Nat -> Maybe (Action name key value world error)
nativeActionAt NoTransitions = \ordinal => Nothing
nativeActionAt (MoreTransitions step rest) =
  observeOrdinalHead (transitionAction step) (nativeActionAt rest)

||| The action immediately after any checked prefix is found at its count.
||| Structural prefix induction, independent of endpoint representation.
export
0 nativeActionAfterPrefix :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, before, afterState, finalState : SystemState name key value world error} ->
  (front : Transitions first before) -> (step : Transition before afterState) ->
  (rest : Transitions afterState finalState) ->
  nativeActionAt (appendTransitions front (MoreTransitions step rest)) (transitionCount front) =
    Just (transitionAction step)
nativeActionAfterPrefix NoTransitions step rest = Refl
nativeActionAfterPrefix (MoreTransitions previous tail) step rest =
  nativeActionAfterPrefix tail step rest

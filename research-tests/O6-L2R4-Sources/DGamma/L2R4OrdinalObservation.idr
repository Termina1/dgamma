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

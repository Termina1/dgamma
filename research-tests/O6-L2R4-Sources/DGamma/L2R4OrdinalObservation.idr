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

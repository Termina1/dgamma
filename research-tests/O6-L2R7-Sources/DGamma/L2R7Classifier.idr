module DGamma.L2R7Classifier

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3ForcedClosure
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R7ObservedAny
import Data.Bool
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Extract both true factors by one Bool elimination. Call sites pass the
||| actual two observations; no equality of reconstructed dependent records.
export
0 acceptedConjunction : (left, right : Bool) -> (0 accepted : left && right = True) ->
  (left = True, right = True)
acceptedConjunction False right accepted = absurd accepted
acceptedConjunction True right accepted = (Refl, accepted)

||| The Ord Nat zero comparison agrees with Data.Nat.lte.
export
0 leZero : (n : Nat) -> (Z <= n) = True
leZero Z = Refl
leZero (S n) = Refl

||| Right-argument elimination for the successor bridge, separate from the
||| recursive left-argument elimination in leToLte.
export
0 leSuccessorBridge : (n : Nat) ->
  (0 earlier : (m : Nat) -> (n <= m) = lte n m) -> (m : Nat) ->
  (S n <= m) = lte (S n) m
leSuccessorBridge n earlier Z = Refl
leSuccessorBridge n earlier (S m) = earlier m

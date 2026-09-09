module DGamma.L2R13ForcedAnchor

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.EqOrd
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R7ObservedAny
import DGamma.L2R7PlacedCoverage
import DGamma.L2R12PhaseAccepted
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Zero branch of reflection for the actual library Nat equality.
export
0 phaseNatZero : (right : Nat) -> (0 accepted : (Z == right) = True) -> Z = right
phaseNatZero Z accepted = Refl
phaseNatZero (S right) accepted = absurd accepted

||| Successor reflection consumes only the right Nat and recursive premise.
export
0 phaseNatSuccessor : (left : Nat) ->
  (0 recursive : (right : Nat) -> (left == right) = True -> left = right) ->
  (right : Nat) -> (0 accepted : (S left == right) = True) -> S left = right
phaseNatSuccessor left recursive Z accepted = absurd accepted
phaseNatSuccessor left recursive (S right) accepted = cong S (recursive right accepted)

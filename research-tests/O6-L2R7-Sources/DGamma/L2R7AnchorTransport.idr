module DGamma.L2R7AnchorTransport

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R6Iteration
import Data.List
import Data.List.Elem
import Data.Nat
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Physical action-ordinal map for an adjacent interchange at cut: the
||| crossed step moves RIGHT one, the selected root LEFT one; others stay.
||| A release cut must be transported through its preceding action ordinal,
||| not asserted literally equal on both traces. General semantic proof OPEN.
public export
adjacentOrdinalMap : (cut, ordinal : Nat) -> Nat
adjacentOrdinalMap cut ordinal = if ordinal == cut then S cut
  else if ordinal == S cut then cut else ordinal

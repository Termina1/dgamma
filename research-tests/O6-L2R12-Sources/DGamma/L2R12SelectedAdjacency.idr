module DGamma.L2R12SelectedAdjacency

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.Num
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6Anchors
import DGamma.L2R7CatalogBirth
import DGamma.L2R10MoveCutObservation
import DGamma.L2R11LocatedCut
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Zero physical position cannot have a positive saturating distance,
||| regardless of the observed anchor guard and the computed target.
export
0 zeroDistanceAtGuard : (seen : Bool) -> (target : Nat) ->
  (the Nat (if seen then minus Z target else Z)) = Z
zeroDistanceAtGuard False target = Refl
zeroDistanceAtGuard True target = Refl

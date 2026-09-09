module DGamma.L2R7CoverageFixtures

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R3Attached
import DGamma.L2R3AttachedGap
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R6PlacementFixtures
import DGamma.L2R7PlacedCoverage
import Data.List
import Data.List.Elem
import Data.Nat
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| GENERAL placed-catalog coverage applied to BOTH original fixtures and
||| both barrier roots. These are fresh decoded occurrences, not inherited
||| fixture NF values or the representative root reused as the S occurrence.
public export
record PlacedCoverageFixtures where
  constructor MkPlacedCoverageFixtures
  coveredSingleR : AttachedBundleOccurrence Nat Bool Unit String (\key => Unit) %search %search smallTrace (OInsert 3 Root (smallComponent True)) 4
  coveredBarrierR : AttachedBundleOccurrence Nat Bool Unit String (\key => Unit) %search %search barrierTrace (OInsert 3 Root (smallComponent True)) 4
  coveredBarrierS : AttachedBundleOccurrence Nat Bool Unit String (\key => Unit) %search %search barrierTrace (OInsert 4 Root (smallComponent False)) 5

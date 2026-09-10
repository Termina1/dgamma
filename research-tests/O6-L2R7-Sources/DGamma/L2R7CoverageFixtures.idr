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
  coveredSingleR : DGamma.L2R3AttachedGap.AttachedBundleOccurrence Nat Bool Unit String (\key => Unit) %search %search smallTrace (OInsert 3 Root (smallComponent True)) 4
  coveredBarrierR : DGamma.L2R3AttachedGap.AttachedBundleOccurrence Nat Bool Unit String (\key => Unit) %search %search barrierTrace (OInsert 3 Root (smallComponent True)) 4
  coveredBarrierS : DGamma.L2R3AttachedGap.AttachedBundleOccurrence Nat Bool Unit String (\key => Unit) %search %search barrierTrace (OInsert 4 Root (smallComponent False)) 5

||| All three actual native occurrences come from the GENERAL catalog
||| equality/decoder theorem, with exact original ordinals4/4/5. No fixture
||| AttachedNormalForm is used or silently promoted to a general NF proof.
public export
0 placedCoverageFixtures : PlacedCoverageFixtures
placedCoverageFixtures = MkPlacedCoverageFixtures
  (placedCatalogCoverage (singlePlaced placementDistanceFixtures) (MkRootCatalogEntry 4 3 (smallComponent True)) Here)
  (placedCatalogCoverage (barrierPlaced placementDistanceFixtures) (MkRootCatalogEntry 4 3 (smallComponent True)) Here)
  (placedCatalogCoverage (barrierPlaced placementDistanceFixtures) (MkRootCatalogEntry 5 4 (smallComponent False)) (There Here))

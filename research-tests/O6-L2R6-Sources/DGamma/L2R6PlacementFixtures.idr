module DGamma.L2R6PlacementFixtures

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R3BundlePhaseStates
import DGamma.L2R3BundlePhase
import DGamma.L2R3AttachedGap
import DGamma.L2R3FixtureCoverage
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Original full7/8 and alternate prefix6/7 traces, observed anchors and
||| physical distances. Original placed bundles contain EXACTLY the computed
||| same-anchor catalog; the producer uses the inherited L2R3 actual bundles.
||| This does not normalize the alternate traces or supply a general placement.
public export
record PlacementDistanceFixtures where
  constructor MkPlacementDistanceFixtures
  originalSingleTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) smallTrace
  originalBarrierTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) barrierTrace
  alternateSingleTrace : Transitions (smallState 0) (smallState 9)
  alternateSingleTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) alternateSingleTrace
  alternateBarrierTrace : Transitions (smallState 0) (bundlePhaseState 3)
  alternateBarrierTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) alternateBarrierTrace
  singleAnchorObserved : Maybe Nat
  barrierRAnchorObserved : Maybe Nat
  barrierSAnchorObserved : Maybe Nat
  0 singleAnchorEquation : anchorOf %search %search originalSingleTrail 4 = singleAnchorObserved
  0 barrierRAnchorEquation : anchorOf %search %search originalBarrierTrail 4 = barrierRAnchorObserved
  0 barrierSAnchorEquation : anchorOf %search %search originalBarrierTrail 5 = barrierSAnchorObserved
  0 anchorsExpected : (singleAnchorObserved, barrierRAnchorObserved, barrierSAnchorObserved) = (Just 4, Just 4, Just 4)
  originalSingleDistance : Nat
  originalBarrierDistance : Nat
  alternateSingleDistance : Nat
  alternateBarrierDistance : Nat
  0 originalSingleDistanceEquation : totalDistance %search %search originalSingleTrail = originalSingleDistance
  0 originalBarrierDistanceEquation : totalDistance %search %search originalBarrierTrail = originalBarrierDistance
  0 alternateSingleDistanceEquation : totalDistance %search %search alternateSingleTrail = alternateSingleDistance
  0 alternateBarrierDistanceEquation : totalDistance %search %search alternateBarrierTrail = alternateBarrierDistance
  0 distancesExpected : (originalSingleDistance, originalBarrierDistance, alternateSingleDistance, alternateBarrierDistance) = (0, 0, 1, 2)
  singlePlaced : PlacedBundle Nat Bool Unit String (\key => Unit) %search %search originalSingleTrail 4
  barrierPlaced : PlacedBundle Nat Bool Unit String (\key => Unit) %search %search originalBarrierTrail 4

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
import DGamma.L2R3Attached
import DGamma.L2R3SmallAttached
import DGamma.L2R3BarrierBlocks
import DGamma.L2R3AttachedGap
import DGamma.L2R3FixtureCoverage
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import Data.List
import Data.Maybe
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

||| Simultaneous actual trails and numerical observations. PlacedBundle uses
||| c12CatalogR/barrierCatalogR L2R3 witnesses literally, with inherited offset
||| equations (also the L2R4 catalog anchors), not new projected-record equality.
public export
0 placementDistanceFixtures : PlacementDistanceFixtures
placementDistanceFixtures = MkPlacementDistanceFixtures
  (AvailabilityStep (smallState 0)
    (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) _
    (AvailabilityStep (smallState 1)
    (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) _
    (AvailabilityStep (smallState 2)
    (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) _
    (AvailabilityStep (smallState 3)
    (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) _
    (AvailabilityStep (smallState 4)
    (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) _
    (AvailabilityStep (smallState 5)
    (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) _
    (AvailabilityStep (smallState 6)
    (Fired {before = smallState 6} {afterState = smallState 7} %search %search (LAdvance 2) LFinishTag (smallFinish2 smallNativeExecution)) _
    (AvailabilityEnd (smallState 7)))))))))
  (AvailabilityStep (barrierState 0)
    (Fired {before = barrierState 0} {afterState = barrierState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) _
    (AvailabilityStep (barrierState 1)
    (Fired {before = barrierState 1} {afterState = barrierState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) _
    (AvailabilityStep (barrierState 2)
    (Fired {before = barrierState 2} {afterState = barrierState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) _
    (AvailabilityStep (barrierState 3)
    (Fired {before = barrierState 3} {afterState = barrierState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) _
    (AvailabilityStep (barrierState 4)
    (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) _
    (AvailabilityStep (barrierState 5)
    (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) _
    (AvailabilityStep (barrierState 6)
    (Fired {before = barrierState 6} {afterState = barrierState 7} %search %search (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution)) _
    (AvailabilityStep (barrierState 7)
    (Fired {before = barrierState 7} {afterState = barrierState 8} %search %search (LAdvance 2) LFinishTag (finishFollowing barrierNativeExecution)) _
    (AvailabilityEnd (barrierState 8))))))))))
  (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 8} %search %search (LBegin 2) LBeginTag (smallEarlyBegin2 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 8} {afterState = smallState 9} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution))
    NoTransitions))))))
  (AvailabilityStep (smallState 0) (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) _
    (AvailabilityStep (smallState 1) (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) _
    (AvailabilityStep (smallState 2) (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) _
    (AvailabilityStep (smallState 3) (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) _
    (AvailabilityStep (smallState 4) (Fired {before = smallState 4} {afterState = smallState 8} %search %search (LBegin 2) LBeginTag (smallEarlyBegin2 smallNativeExecution)) _
    (AvailabilityStep (smallState 8) (Fired {before = smallState 8} {afterState = smallState 9} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution)) _
    (AvailabilityEnd (smallState 9))))))))
  (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 8} %search %search (LBegin 2) LBeginTag (smallEarlyBegin2 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 8} {afterState = smallState 9} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution))
    (MoreTransitions (Fired {before = bundlePhaseState 2} {afterState = bundlePhaseState 3} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (sAfterBeginR bundlePhaseNative))
    NoTransitions)))))))
  (AvailabilityStep (smallState 0) (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) _
    (AvailabilityStep (smallState 1) (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) _
    (AvailabilityStep (smallState 2) (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) _
    (AvailabilityStep (smallState 3) (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) _
    (AvailabilityStep (smallState 4) (Fired {before = smallState 4} {afterState = smallState 8} %search %search (LBegin 2) LBeginTag (smallEarlyBegin2 smallNativeExecution)) _
    (AvailabilityStep (smallState 8) (Fired {before = smallState 8} {afterState = smallState 9} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution)) _
    (AvailabilityStep (bundlePhaseState 2) (Fired {before = bundlePhaseState 2} {afterState = bundlePhaseState 3} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (sAfterBeginR bundlePhaseNative)) _
    (AvailabilityEnd (bundlePhaseState 3)))))))))
  (Just 4) (Just 4) (Just 4) Refl Refl Refl Refl
  0 0 1 2 Refl Refl Refl Refl Refl
  (MkPlacedBundle (OInsert 3 Root (smallComponent True)) 4 (c12CatalogR fixtureCoverage)
    (AvailabilityStep (smallState 4) (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) _
    (AvailabilityEnd (smallState 5)))
    (cong fst (c12CatalogInterval fixtureCoverage))
    (trans (cong (\offset => scanRootCatalog offset (AvailabilityStep (smallState 4) (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) _
    (AvailabilityEnd (smallState 5))))
      (cong fst (c12CatalogInterval fixtureCoverage))) Refl))
  (MkPlacedBundle (OInsert 3 Root (smallComponent True)) 4 (barrierCatalogR fixtureCoverage)
    (AvailabilityStep (smallState 4) (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) _
    (AvailabilityStep (barrierState 5) (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) _
    (AvailabilityEnd (barrierState 6))))
    (cong fst (barrierCatalogRInterval fixtureCoverage))
    (trans (cong (\offset => scanRootCatalog offset (AvailabilityStep (smallState 4) (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) _
    (AvailabilityStep (barrierState 5) (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) _
    (AvailabilityEnd (barrierState 6)))))
      (cong fst (barrierCatalogRInterval fixtureCoverage))) Refl))

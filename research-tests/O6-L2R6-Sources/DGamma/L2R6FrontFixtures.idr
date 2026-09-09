module DGamma.L2R6FrontFixtures

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
import DGamma.L2R6FrontNormal
import Decidable.Decidable
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Accepted front-normal/no-forced-control observations on both full actual
||| fixtures. Residual NF fields are inherited honest EMPTY-gap instances,
||| not the missing general placed-bundle-to-inter-block-coverage producer.
public export
record FrontDispositionFixtures
  (0 singleGap : Transitions (smallState 5) (smallState 5))
  (0 bundleGap : Transitions (barrierState 6) (barrierState 6)) where
  constructor MkFrontDispositionFixtures
  singleFrontTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) smallTrace
  barrierFrontTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) barrierTrace
  singleFrontNormal : FrontNormal Nat Bool Unit String (\key => Unit) %search %search singleFrontTrail
  barrierFrontNormal : FrontNormal Nat Bool Unit String (\key => Unit) %search %search barrierFrontTrail
  singleNeverRetired : ForcedRootNeverRetired Nat Bool Unit String (\key => Unit) %search %search singleFrontTrail
  barrierNeverRetired : ForcedRootNeverRetired Nat Bool Unit String (\key => Unit) %search %search barrierFrontTrail
  0 singleResidualNormalForm : AttachedNormalForm Nat Bool Unit String (\key => Unit) %search %search smallTrace singleGap 5
  0 barrierResidualNormalForm : AttachedNormalForm Nat Bool Unit String (\key => Unit) %search %search barrierTrace bundleGap 6

||| Simultaneously produce both true/true actual scans and reuse exact empty
||| residual-gap NF proofs. No forced-control disposition is chosen globally,
||| and no general NF producer is claimed by these fixture applications.
public export
0 frontDispositionFixtures : FrontDispositionFixtures
  (attachedBetweenBlocks (DGamma.L2R3SmallAttached.SmallAttachedBlocks.physicalOrder smallAttachedBlocks))
  (attachedBetweenBlocks (DGamma.L2R3BarrierBlocks.BarrierAttachedBlocks.physicalOrder barrierAttachedBlocks))
frontDispositionFixtures = MkFrontDispositionFixtures
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
  (MkFrontNormal True Refl Refl) (MkFrontNormal True Refl Refl)
  (MkForcedRootNeverRetired True Refl Refl) (MkForcedRootNeverRetired True Refl Refl)
  (c12ResidualNF fixtureCoverage) (barrierResidualNF fixtureCoverage)

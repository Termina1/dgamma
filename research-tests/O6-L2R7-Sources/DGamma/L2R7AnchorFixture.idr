module DGamma.L2R7AnchorFixture

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
import DGamma.L2R6Iteration
import DGamma.L2R3ForcedClosure
import DGamma.L2R5Extensional
import DGamma.L2R5ExtensionalRetire
import DGamma.CP4RuntimeBindings
import Data.List.Elem
import Decidable.Decidable
import DGamma.L2R6IterationFixtures
import DGamma.L2R7AnchorTransport
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Actual admitted R-over-Begin2 instance of the transport CONTRACT. Both
||| release witnesses locate the SAME own-child Remove1 at3, so the ordinal
||| map fixes its ending anchor4 while moving Root3 from5 to4. This does not
||| prove general anchor transport or other-root distance invariance.
public export
0 anchorTransportFixture : AnchorTransport Nat Bool Unit String (\key => Unit) %search %search
  (singleBeforeTrace iterationFixtures) (singleAfterTrace iterationFixtures)
anchorTransportFixture = MkAnchorTransport
  (AvailabilityStep (smallState 0) (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) _
    (AvailabilityStep (smallState 1) (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) _
    (AvailabilityStep (smallState 2) (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) _
    (AvailabilityStep (smallState 3) (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) _
    (AvailabilityStep (smallState 4) (Fired {before = smallState 4} {afterState = smallState 8} %search %search (LBegin 2) LBeginTag (smallEarlyBegin2 smallNativeExecution)) _
    (AvailabilityStep (smallState 8) (Fired {before = smallState 8} {afterState = smallState 9} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution)) _
    (AvailabilityEnd (smallState 9))))))))
  (AvailabilityStep (smallState 0) (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) _
    (AvailabilityStep (smallState 1) (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) _
    (AvailabilityStep (smallState 2) (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) _
    (AvailabilityStep (smallState 3) (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) _
    (AvailabilityStep (smallState 4) (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) _
    (AvailabilityStep (smallState 5) (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) _
    (AvailabilityEnd (smallState 6))))))))
  (singleAdmitted iterationFixtures) 4 Refl
  (MkRootCatalogEntry 5 3 (smallComponent True)) (MkRootCatalogEntry 4 3 (smallComponent True)) Here Here Refl Refl
  (MkRootCatalogEntry 5 3 (smallComponent True)) (MkRootCatalogEntry 4 3 (smallComponent True)) Here Here Refl Refl
  (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))) (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))) 1 0
  (MkLocatedActionOccurrence (smallState 3) (smallState 4) (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) NoTransitions))) (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 8} %search %search (LBegin 2) LBeginTag (smallEarlyBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 8} {afterState = smallState 9} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution)) NoTransitions)) Refl Refl)
  (MkLocatedActionOccurrence (smallState 3) (smallState 4) (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) NoTransitions))) (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) NoTransitions)) Refl Refl)
  Refl (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))) (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))
  (retireFiber (freshFiber (smallComponent True) (ChildOf 0))) (retireFiber (freshFiber (smallComponent True) (ChildOf 0)))
  Refl Refl Refl Refl True Here Here Here Here
  4 4 Refl Refl Refl Refl Refl

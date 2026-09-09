module DGamma.L2R6IterationFixtures

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
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Five real full-prefix traces on inherited one-origin states. The three
||| actual admitted steps own located adjacency, native applicability/current
||| cuts, key/barrier forcing, exact-one total distance, and extensional ends.
||| Source fronts are accepted; target prefixes are distance zero, not full
||| Finish2 executions or a general attached-NF/terminal-earliest theorem.
public export
record IterationFixtures where
  constructor MkIterationFixtures
  singleBeforeTrace : Transitions (smallState 0) (smallState 9)
  singleBeforeTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) singleBeforeTrace
  singleAfterTrace : Transitions (smallState 0) (smallState 6)
  singleAfterTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) singleAfterTrace
  bundleBeforeTrace : Transitions (smallState 0) (bundlePhaseState 3)
  bundleBeforeTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) bundleBeforeTrace
  bundleMiddleTrace : Transitions (smallState 0) (bundlePhaseState 6)
  bundleMiddleTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) bundleMiddleTrace
  bundleAfterTrace : Transitions (smallState 0) (barrierState 7)
  bundleAfterTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) bundleAfterTrace
  0 singleAdmitted : AdmittedDistanceMove Nat Bool Unit String (\key => Unit) %search %search singleBeforeTrail singleAfterTrail
  0 firstBundleAdmitted : AdmittedDistanceMove Nat Bool Unit String (\key => Unit) %search %search bundleBeforeTrail bundleMiddleTrail
  0 secondBundleAdmitted : AdmittedDistanceMove Nat Bool Unit String (\key => Unit) %search %search bundleMiddleTrail bundleAfterTrail
  singleInputFront : FrontNormal Nat Bool Unit String (\key => Unit) %search %search singleBeforeTrail
  bundleInputFront : FrontNormal Nat Bool Unit String (\key => Unit) %search %search bundleBeforeTrail
  0 singleZero : totalDistance %search %search singleAfterTrail = 0
  0 bundleZero : totalDistance %search %search bundleAfterTrail = 0

||| Construct the three real moves simultaneously from native inherited
||| edges: R across Begin2, then ordered R/S across Begin2 one at a time.
||| Entire prefixes/suffixes are checked, including S replay after R moves.
||| Current cuts, located adjacency and total distance 1->0 / 2->1->0 are
||| observed here, not inferred from the predecessor endpoint embeddings.
public export
0 iterationFixtures : IterationFixtures
iterationFixtures = MkIterationFixtures
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
    (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution))
    NoTransitions))))))
  (AvailabilityStep (smallState 0) (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) _
    (AvailabilityStep (smallState 1) (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) _
    (AvailabilityStep (smallState 2) (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) _
    (AvailabilityStep (smallState 3) (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) _
    (AvailabilityStep (smallState 4) (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) _
    (AvailabilityStep (smallState 5) (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) _
    (AvailabilityEnd (smallState 6))))))))
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
  (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution))
    (MoreTransitions (Fired {before = bundlePhaseState 5} {afterState = bundlePhaseState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (sAfterRBegin bundlePhaseNative))
    NoTransitions)))))))
  (AvailabilityStep (smallState 0) (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) _
    (AvailabilityStep (smallState 1) (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) _
    (AvailabilityStep (smallState 2) (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) _
    (AvailabilityStep (smallState 3) (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) _
    (AvailabilityStep (smallState 4) (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) _
    (AvailabilityStep (smallState 5) (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) _
    (AvailabilityStep (bundlePhaseState 5) (Fired {before = bundlePhaseState 5} {afterState = bundlePhaseState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (sAfterRBegin bundlePhaseNative)) _
    (AvailabilityEnd (bundlePhaseState 6)))))))))
  (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution))
    (MoreTransitions (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution))
    (MoreTransitions (Fired {before = barrierState 6} {afterState = barrierState 7} %search %search (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution))
    NoTransitions)))))))
  (AvailabilityStep (smallState 0) (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) _
    (AvailabilityStep (smallState 1) (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) _
    (AvailabilityStep (smallState 2) (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) _
    (AvailabilityStep (smallState 3) (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) _
    (AvailabilityStep (smallState 4) (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) _
    (AvailabilityStep (barrierState 5) (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) _
    (AvailabilityStep (barrierState 6) (Fired {before = barrierState 6} {afterState = barrierState 7} %search %search (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution)) _
    (AvailabilityEnd (barrierState 7)))))))))
  (MkAdmittedDistanceMove 3 (smallComponent True) [LBegin 0, LAdvance 0, ORetire 1, ORemove 1] (LBegin 2) []
    (MkLocatedActionOccurrence (smallState 4) (smallState 8) (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution))
    NoTransitions))))
    (Fired {before = smallState 4} {afterState = smallState 8} %search %search (LBegin 2) LBeginTag (smallEarlyBegin2 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 8} {afterState = smallState 9} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution))
    NoTransitions) Refl Refl)
    (MkLocatedActionOccurrence (smallState 4) (smallState 5) (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution))
    NoTransitions))))
    (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution))
    NoTransitions) Refl Refl)
    Refl Refl (CrossLifecycle True Refl Refl (\same => case same of Refl impossible))
    (KeyForces Here Refl) Refl Refl Refl Refl 1 0 Refl Refl Refl
    (snapshotIntoExtensional %search (smallState 9) (smallState 6) (smallAlternateSnapshot smallNativeExecution)))
  (MkAdmittedDistanceMove 3 (smallComponent True) [LBegin 0, LAdvance 0, ORetire 1, ORemove 1] (LBegin 2) [OInsert 4 Root (smallComponent False)]
    (MkLocatedActionOccurrence (smallState 4) (smallState 8) (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution))
    NoTransitions))))
    (Fired {before = smallState 4} {afterState = smallState 8} %search %search (LBegin 2) LBeginTag (smallEarlyBegin2 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 8} {afterState = smallState 9} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution))
    (MoreTransitions (Fired {before = bundlePhaseState 2} {afterState = bundlePhaseState 3} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (sAfterBeginR bundlePhaseNative))
    NoTransitions)) Refl Refl)
    (MkLocatedActionOccurrence (smallState 4) (smallState 5) (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution))
    NoTransitions))))
    (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution))
    (MoreTransitions (Fired {before = bundlePhaseState 5} {afterState = bundlePhaseState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (sAfterRBegin bundlePhaseNative))
    NoTransitions)) Refl Refl)
    Refl Refl (CrossLifecycle True Refl Refl (\same => case same of Refl impossible))
    (KeyForces Here Refl) Refl Refl Refl Refl 2 1 Refl Refl Refl
    (snapshotIntoExtensional %search (bundlePhaseState 3) (bundlePhaseState 6) (firstMoveSnapshot bundlePhaseNative)))
  (MkAdmittedDistanceMove 4 (smallComponent False) [LBegin 0, LAdvance 0, ORetire 1, ORemove 1, OInsert 3 Root (smallComponent True)] (LBegin 2) []
    (MkLocatedActionOccurrence (smallState 5) (smallState 6) (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution))
    NoTransitions)))))
    (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution))
    (MoreTransitions (Fired {before = bundlePhaseState 5} {afterState = bundlePhaseState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (sAfterRBegin bundlePhaseNative))
    NoTransitions) Refl Refl)
    (MkLocatedActionOccurrence (barrierState 5) (barrierState 6) (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution))
    NoTransitions)))))
    (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution))
    (MoreTransitions (Fired {before = barrierState 6} {afterState = barrierState 7} %search %search (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution))
    NoTransitions) Refl Refl)
    Refl Refl (CrossLifecycle True Refl Refl (\same => case same of Refl impossible))
    (OrderForces (KeyForces Here Refl) (There Here) (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))))) Refl Refl Refl Refl 1 0 Refl Refl Refl
    (snapshotIntoExtensional %search (bundlePhaseState 6) (barrierState 7) (secondMoveSnapshot bundlePhaseNative)))
  (MkFrontNormal True Refl Refl) (MkFrontNormal True Refl Refl) Refl Refl

||| FIRST actual one-/two-step iteration instances, using the same middle
||| trail and applying iterationEndpoint. D7 owns native adjacency/current
||| cuts and exact-one distances, with final zero proofs singleZero/bundleZero.
||| This is not a generic fold advertised as arbitrary move existence.
public export
0 fixtureIterations :
  ((DistanceIteration %search %search (singleBeforeTrail iterationFixtures) (singleAfterTrail iterationFixtures),
    RegistryExtensional Nat Bool Unit String (\key => Unit) %search (smallState 9) (smallState 6)),
   (DistanceIteration %search %search (bundleBeforeTrail iterationFixtures) (bundleAfterTrail iterationFixtures),
    RegistryExtensional Nat Bool Unit String (\key => Unit) %search (bundlePhaseState 3) (barrierState 7)))
fixtureIterations =
  ((IterationMove (singleAdmitted iterationFixtures) (IterationDone (singleAfterTrail iterationFixtures)),
    iterationEndpoint (IterationMove (singleAdmitted iterationFixtures) (IterationDone (singleAfterTrail iterationFixtures)))),
   (IterationMove (firstBundleAdmitted iterationFixtures)
      (IterationMove (secondBundleAdmitted iterationFixtures) (IterationDone (bundleAfterTrail iterationFixtures))),
    iterationEndpoint (IterationMove (firstBundleAdmitted iterationFixtures)
      (IterationMove (secondBundleAdmitted iterationFixtures) (IterationDone (bundleAfterTrail iterationFixtures))))))

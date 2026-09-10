module DGamma.L2R3BundlePhase

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5L2R1RootExchange
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R2RootSnapshot
import DGamma.L2R2RootPhase
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R3BundlePhaseStates
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Two additional checked S edges complete the three physical permutations.
||| All original/alternate endpoints have the same world and ordered bindings;
||| no equality of independently generated erased uniqueness proofs is needed.
public export
record BundlePhaseNative where
  constructor MkBundlePhaseNative
  0 sAfterBeginR : checkedApplyAction @{%search} @{%search} (OInsert 4 Root (smallComponent False)) (bundlePhaseState 2) = Just (OInsertTag, bundlePhaseState 3)
  0 sAfterRBegin : checkedApplyAction @{%search} @{%search} (OInsert 4 Root (smallComponent False)) (bundlePhaseState 5) = Just (OInsertTag, bundlePhaseState 6)
  0 firstMoveSnapshot : runtimeSnapshot (bundlePhaseState 3) = runtimeSnapshot (bundlePhaseState 6)
  0 secondMoveSnapshot : runtimeSnapshot (bundlePhaseState 6) = runtimeSnapshot (bundlePhaseState 8)

||| Authenticate both S edges by the native raw evaluator plus inherited
||| Preservation. Exact snapshots are simultaneous observations of explicit
||| state expressions, not reconstructed literal SystemState equality.
public export
0 bundlePhaseNative : BundlePhaseNative
bundlePhaseNative = MkBundlePhaseNative
  (checkedFromRaw %search %search (OInsert 4 Root (smallComponent False))
    (bundlePhaseState 2) (bundlePhaseState 3) OInsertTag
    (checkedActionTargetValid %search %search (OInsert 3 Root (smallComponent True))
      (smallState 8) (smallState 9) OInsertTag (smallLateInsert3 smallNativeExecution)) Refl)
  (checkedFromRaw %search %search (OInsert 4 Root (smallComponent False))
    (bundlePhaseState 5) (bundlePhaseState 6) OInsertTag
    (checkedActionTargetValid %search %search (LBegin 2)
      (smallState 5) (smallState 6) LBeginTag (smallBegin2 smallNativeExecution)) Refl)
  Refl Refl

||| Second authenticated availability-aware root phase: S crosses Begin2 only
||| after R is already in its ordered place. Early S and late Begin are the
||| actual barrier fixture edges; empty provisions make both crossed cuts free.
public export
0 sRootSnapshotSquare : AvailabilityRootSnapshotExchange Nat Bool Unit String (\key => Unit)
  %search %search 4 (smallComponent False)
  (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution))
  (Fired {before = smallState 6} {afterState = bundlePhaseState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (sAfterRBegin bundlePhaseNative))
sRootSnapshotSquare = MkAvailabilityRootSnapshotExchange
  (\same => case same of Refl impossible) Refl Refl (barrierState 6) (barrierState 7)
  (insertS barrierNativeExecution) (beginFollowing barrierNativeExecution) (secondMoveSnapshot bundlePhaseNative)

||| Two actual availability-aware phase steps, in original R/S bundle order,
||| plus the native old/middle runs and the second step's OWN moved trail.
||| Inversion counts are LOCAL to the post-release cut4: 2 -> 1 -> 0.
||| The single-R moved trail also has count0. Full pre-release prefixes retain
||| blocked inversions (2 for R, 4 for R/S); no global raw-count-zero claim.
public export
record BundlePhaseEvidence where
  constructor MkBundlePhaseEvidence
  rPhase : SnapshotRootPhaseStep Nat Bool Unit String (\key => Unit) %search %search
    2 3 (smallComponent True) (NoTransitions {state = smallState 4})
    (smallEarlyBegin2 smallNativeExecution) (smallLateInsert3 smallNativeExecution)
  sPhase : SnapshotRootPhaseStep Nat Bool Unit String (\key => Unit) %search %search
    2 4 (smallComponent False) (MoreTransitions (Fired {before = bundlePhaseState 0} {afterState = bundlePhaseState 4} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) NoTransitions)
    (smallBegin2 smallNativeExecution) (sAfterRBegin bundlePhaseNative)
  originalRun : Transitions (bundlePhaseState 0) (bundlePhaseState 3)
  middleRun : Transitions (bundlePhaseState 0) (bundlePhaseState 6)
  originalTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace Nat Bool Unit String (\key => Unit) originalRun
  middleTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace Nat Bool Unit String (\key => Unit) middleRun
  singleMovedTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace Nat Bool Unit String (\key => Unit) (rootPhaseTrace rPhase)
  movedTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace Nat Bool Unit String (\key => Unit) (rootPhaseTrace sPhase)
  0 originalPhysical : originalRun = (MoreTransitions (Fired {before = bundlePhaseState 0} {afterState = bundlePhaseState 1} %search %search (LBegin 2) LBeginTag (smallEarlyBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 1} {afterState = bundlePhaseState 2} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 2} {afterState = bundlePhaseState 3} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (sAfterBeginR bundlePhaseNative)) NoTransitions)))
  0 middlePhysical : middleRun = (MoreTransitions (Fired {before = bundlePhaseState 0} {afterState = bundlePhaseState 4} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 4} {afterState = bundlePhaseState 5} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 5} {afterState = bundlePhaseState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (sAfterRBegin bundlePhaseNative)) NoTransitions)))
  0 originalCount : rootBirthInversions 0 originalTrail = 2
  0 middleCount : rootBirthInversions 0 middleTrail = 1
  0 singleMovedCount : rootBirthInversions 0 singleMovedTrail = 0
  0 movedCount : rootBirthInversions 0 movedTrail = 0
  0 firstExactlyOne : rootBirthInversions 0 originalTrail = S (rootBirthInversions 0 middleTrail)
  0 secondExactlyOne : rootBirthInversions 0 middleTrail = S (rootBirthInversions 0 movedTrail)
  0 firstPrefixRuntime : runtimeSnapshot (snapshotRootFinal (rootPhaseSquare rPhase)) = runtimeSnapshot (bundlePhaseState 5)
  0 originalToMovedRuntime : runtimeSnapshot (bundlePhaseState 3) = runtimeSnapshot (snapshotRootFinal (rootPhaseSquare sPhase))
  0 originalToMovedSupport : supportSet @{%search} @{%search} (bundlePhaseState 3) = supportSet @{%search} @{%search} (snapshotRootFinal (rootPhaseSquare sPhase))

||| Construct two SnapshotRootPhaseSteps, first R then S, using the exact
||| constructor recipe of L2R2RootPhase.rootPhaseFromSnapshot (its function
||| body is export-opaque here). Squares and decreasing proofs are reused.
||| The original and middle suffix S edges are both native checked edges, so
||| the first move is physically replayed through S rather than just counted.
||| The second phase owns the final moved trail. Runtime/support preservation
||| is exact; the zero is post-release-local, not a rewritten global measure.
public export
0 bundlePhaseEvidence : BundlePhaseEvidence
bundlePhaseEvidence = MkBundlePhaseEvidence
  (MkSnapshotRootPhaseStep smallRootSnapshotSquare
    (MoreTransitions (Fired {before = bundlePhaseState 0} {afterState = bundlePhaseState 4} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 4} {afterState = bundlePhaseState 5} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) NoTransitions))
    Refl (smallAlternateSnapshot smallNativeExecution)
    (supportSetAcrossSnapshot %search %search (smallState 9) (smallState 6) (smallAlternateSnapshot smallNativeExecution))
    (beginSnapshotRootDecreases %search %search 2 3 (smallComponent True)
      (smallEarlyBegin2 smallNativeExecution) (smallLateInsert3 smallNativeExecution) smallRootSnapshotSquare))
  (MkSnapshotRootPhaseStep sRootSnapshotSquare
    (MoreTransitions (Fired {before = bundlePhaseState 0} {afterState = bundlePhaseState 4} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 4} {afterState = bundlePhaseState 7} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 7} {afterState = bundlePhaseState 8} %search %search (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution)) NoTransitions)))
    Refl (secondMoveSnapshot bundlePhaseNative)
    (supportSetAcrossSnapshot %search %search (bundlePhaseState 6) (bundlePhaseState 8) (secondMoveSnapshot bundlePhaseNative))
    (beginSnapshotRootDecreases %search %search 2 4 (smallComponent False)
      (smallBegin2 smallNativeExecution) (sAfterRBegin bundlePhaseNative) sRootSnapshotSquare))
  (MoreTransitions (Fired {before = bundlePhaseState 0} {afterState = bundlePhaseState 1} %search %search (LBegin 2) LBeginTag (smallEarlyBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 1} {afterState = bundlePhaseState 2} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 2} {afterState = bundlePhaseState 3} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (sAfterBeginR bundlePhaseNative)) NoTransitions)))
  (MoreTransitions (Fired {before = bundlePhaseState 0} {afterState = bundlePhaseState 4} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 4} {afterState = bundlePhaseState 5} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 5} {afterState = bundlePhaseState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (sAfterRBegin bundlePhaseNative)) NoTransitions)))
  (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (bundlePhaseState 0) (Fired {before = bundlePhaseState 0} {afterState = bundlePhaseState 1} %search %search (LBegin 2) LBeginTag (smallEarlyBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 1} {afterState = bundlePhaseState 2} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 2} {afterState = bundlePhaseState 3} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (sAfterBeginR bundlePhaseNative)) NoTransitions)) (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (bundlePhaseState 1) (Fired {before = bundlePhaseState 1} {afterState = bundlePhaseState 2} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 2} {afterState = bundlePhaseState 3} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (sAfterBeginR bundlePhaseNative)) NoTransitions) (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (bundlePhaseState 2) (Fired {before = bundlePhaseState 2} {afterState = bundlePhaseState 3} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (sAfterBeginR bundlePhaseNative)) NoTransitions (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd (bundlePhaseState 3)))))
  (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (bundlePhaseState 0) (Fired {before = bundlePhaseState 0} {afterState = bundlePhaseState 4} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 4} {afterState = bundlePhaseState 5} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 5} {afterState = bundlePhaseState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (sAfterRBegin bundlePhaseNative)) NoTransitions)) (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (bundlePhaseState 4) (Fired {before = bundlePhaseState 4} {afterState = bundlePhaseState 5} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 5} {afterState = bundlePhaseState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (sAfterRBegin bundlePhaseNative)) NoTransitions) (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (bundlePhaseState 5) (Fired {before = bundlePhaseState 5} {afterState = bundlePhaseState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (sAfterRBegin bundlePhaseNative)) NoTransitions (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd (bundlePhaseState 6)))))
  (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (bundlePhaseState 0) (Fired {before = bundlePhaseState 0} {afterState = bundlePhaseState 4} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 4} {afterState = bundlePhaseState 5} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) NoTransitions) (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (bundlePhaseState 4) (Fired {before = bundlePhaseState 4} {afterState = bundlePhaseState 5} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) NoTransitions (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd (bundlePhaseState 5))))
  (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (bundlePhaseState 0) (Fired {before = bundlePhaseState 0} {afterState = bundlePhaseState 4} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 4} {afterState = bundlePhaseState 7} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 7} {afterState = bundlePhaseState 8} %search %search (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution)) NoTransitions)) (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (bundlePhaseState 4) (Fired {before = bundlePhaseState 4} {afterState = bundlePhaseState 7} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) (MoreTransitions (Fired {before = bundlePhaseState 7} {afterState = bundlePhaseState 8} %search %search (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution)) NoTransitions) (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (bundlePhaseState 7) (Fired {before = bundlePhaseState 7} {afterState = bundlePhaseState 8} %search %search (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution)) NoTransitions (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd (bundlePhaseState 8)))))
  Refl Refl Refl Refl Refl Refl Refl Refl Refl
  (trans (firstMoveSnapshot bundlePhaseNative) (secondMoveSnapshot bundlePhaseNative))
  (supportSetAcrossSnapshot %search %search (bundlePhaseState 3) (bundlePhaseState 8)
    (trans (firstMoveSnapshot bundlePhaseNative) (secondMoveSnapshot bundlePhaseNative)))

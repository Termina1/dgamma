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

||| Two actual availability-aware phase calls, in original R/S bundle order,
||| plus the native old/middle runs and the second call's OWN moved trail.
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
  originalTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) originalRun
  middleTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) middleRun
  singleMovedTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) (rootPhaseTrace rPhase)
  movedTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) (rootPhaseTrace sPhase)
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

module DGamma.L2R13DistanceFixtures

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.Num
import Prelude.EqOrd
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R3Attached
import DGamma.L2R3SmallAttached
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R6Phase
import DGamma.L2R7CatalogBirth
import DGamma.L2R9OrdinalTrails
import DGamma.L2R10OrdinalData
import DGamma.L2R10PhaseScan
import DGamma.L2R11PhaseDecode
import DGamma.L2R8CoreContract
import DGamma.L2R12PhaseNativeFixtures
import DGamma.L2R13ForcedAnchor
import DGamma.L2R13PhaseEntry
import DGamma.L2R3BundlePhaseStates
import DGamma.L2R3BundlePhase
import DGamma.L2R3ForcedClosure
import DGamma.L2R6Iteration
import DGamma.L2R6IterationFixtures
import DGamma.L2R8NativeWords
import DGamma.L2R11ClassifierSquare
import DGamma.L2R13ExtendMove
import DGamma.L2R13InsertExtensional
import DGamma.L2R13TerminalMove
import DGamma.L2R5Extensional
import DGamma.L2R5CurrentCut
import DGamma.CP4RuntimeBindings
import DGamma.CP4ProgressNoDeadlock
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core
import Decidable.Decidable

%default total
%unbound_implicits off

||| Both native terminal Begin/root squares used by D8, built from checked
||| early/late edges and snapshot endpoints, NOT from hand-built moves.
export
0 distanceFixtureSquares :
  (ClassifierSquare Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
    3 (smallComponent True) (smallState 4) (LBegin 2) LBeginTag (smallState 9),
   ClassifierSquare Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
    4 (smallComponent False) (smallState 5) (LBegin 2) LBeginTag (bundlePhaseState 6))
distanceFixtureSquares =
  (MkClassifierSquare (smallState 5) (smallState 6)
    (smallInsert3 smallNativeExecution) (smallBegin2 smallNativeExecution)
    (CrossLifecycle True Refl Refl (\same => case same of Refl impossible)) Refl
    (snapshotIntoExtensional (fst fixtureDictionaries) (smallState 9) (smallState 6)
      (smallAlternateSnapshot smallNativeExecution)),
   MkClassifierSquare (barrierState 6) (barrierState 7)
    (insertS barrierNativeExecution) (beginFollowing barrierNativeExecution)
    (CrossLifecycle True Refl Refl (\same => case same of Refl impossible)) Refl
    (snapshotIntoExtensional (fst fixtureDictionaries) (bundlePhaseState 6) (barrierState 7)
      (secondMoveSnapshot bundlePhaseNative)))

||| D8 single 1->0 and the bundle's terminal 1->0 move FROM the general
||| terminal-square producer. Native prefixes, forcing and scan frames compute;
||| no singleAdmitted/secondBundleAdmitted field of iterationFixtures is used.
public export
0 terminalFixtureMoves :
  (AdmittedDistanceMove Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
    (singleBeforeTrail iterationFixtures) (singleAfterTrail iterationFixtures),
   AdmittedDistanceMove Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
    (bundleMiddleTrail iterationFixtures) (bundleAfterTrail iterationFixtures))
terminalFixtureMoves =
  (terminalSquareAdmittedMove (fst fixtureDictionaries) (snd fixtureDictionaries) 3 (smallComponent True)
    (smallState 4) (smallState 8) (smallState 9) (LBegin 2) LBeginTag (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions)))) (appendAvailability (nativePairTrail (fst fixtureDictionaries) (snd fixtureDictionaries) (smallState 0) (smallState 1) (smallState 2) (LBegin 0) (LAdvance 0) LBeginTag LFinishTag (smallBegin0 smallNativeExecution) (smallFinish0 smallNativeExecution)) (nativePairTrail (fst fixtureDictionaries) (snd fixtureDictionaries) (smallState 2) (smallState 3) (smallState 4) (ORetire 1) (ORemove 1) ORetireTag ORemoveTag (smallRetire1 smallNativeExecution) (smallRemove1 smallNativeExecution)))
    (smallEarlyBegin2 smallNativeExecution) (smallLateInsert3 smallNativeExecution)
    (fst distanceFixtureSquares) (KeyForces Here Refl) 4 0 (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))) Refl Refl,
   terminalSquareAdmittedMove (fst fixtureDictionaries) (snd fixtureDictionaries) 4 (smallComponent False)
    (smallState 5) (smallState 6) (bundlePhaseState 6) (LBegin 2) LBeginTag (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) NoTransitions))))) (appendAvailability (appendAvailability (nativePairTrail (fst fixtureDictionaries) (snd fixtureDictionaries) (smallState 0) (smallState 1) (smallState 2) (LBegin 0) (LAdvance 0) LBeginTag LFinishTag (smallBegin0 smallNativeExecution) (smallFinish0 smallNativeExecution)) (nativePairTrail (fst fixtureDictionaries) (snd fixtureDictionaries) (smallState 2) (smallState 3) (smallState 4) (ORetire 1) (ORemove 1) ORetireTag ORemoveTag (smallRetire1 smallNativeExecution) (smallRemove1 smallNativeExecution))) (AvailabilityStep (smallState 4) (Fired {before = smallState 4} {afterState = smallState 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) NoTransitions (AvailabilityEnd (smallState 5))))
    (smallBegin2 smallNativeExecution) (sAfterRBegin bundlePhaseNative)
    (snd distanceFixtureSquares)
    (OrderForces (KeyForces Here Refl) (There Here) (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))))) 5 0 (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))) Refl Refl)

||| D8 bundle FIRST 2->1 move FROM the general terminal producer followed
||| by the native root-extension producer. Its following S endpoint relation
||| comes from B7, not firstMoveSnapshot or firstBundleAdmitted projections.
export
0 firstBundleFromProducer : AdmittedDistanceMove Nat Bool Unit String (\key => Unit)
  (fst fixtureDictionaries) (snd fixtureDictionaries)
  (bundleBeforeTrail iterationFixtures) (bundleMiddleTrail iterationFixtures)
firstBundleFromProducer = extendAdmittedMoveByRoot (fst fixtureDictionaries) (snd fixtureDictionaries)
  (singleBeforeTrail iterationFixtures) (singleAfterTrail iterationFixtures) (fst terminalFixtureMoves)
  4 (smallComponent False) (bundlePhaseState 3) (bundlePhaseState 6)
  (sAfterBeginR bundlePhaseNative) (sAfterRBegin bundlePhaseNative) Refl Refl
  (KeyForces Here Refl) 4 1 (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))) Refl Refl

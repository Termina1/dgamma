module DGamma.L2R6ForcedFixtures

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
import DGamma.L2R3ForcedClosure
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Three actual trails with simultaneous observed classifier results. The
||| third starts at smallState4: a native root insertion BEFORE Begin2, no
||| earlier release in that trace. R is key-forced in the full traces; S has
||| no key release and is independently derived by the least barrier closure.
public export
record ForcedClassifierFixtures where
  constructor MkForcedClassifierFixtures
  singleForcedTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace Nat Bool Unit String (\key => Unit) smallTrace
  barrierForcedTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace Nat Bool Unit String (\key => Unit) barrierTrace
  frontRootTrace : Transitions (smallState 4) (smallState 6)
  frontRootTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace Nat Bool Unit String (\key => Unit) frontRootTrace
  singleClassified : List (Nat, Bool)
  barrierClassified : List (Nat, Bool)
  frontClassified : List (Nat, Bool)
  0 singleClassificationEquation : classifyForced %search %search singleForcedTrail (scanRootCatalog 0 singleForcedTrail) Refl = singleClassified
  0 barrierClassificationEquation : classifyForced %search %search barrierForcedTrail (scanRootCatalog 0 barrierForcedTrail) Refl = barrierClassified
  0 frontClassificationEquation : classifyForced %search %search frontRootTrail (scanRootCatalog 0 frontRootTrail) Refl = frontClassified
  0 singleClassificationExpected : singleClassified = [(3, True)]
  0 barrierClassificationExpected : barrierClassified = [(3, True), (4, True)]
  0 frontClassificationExpected : frontClassified = [(3, False)]
  0 singleReleaseComputed : scanReleaseOrdinals %search %search (smallComponent True) 0 4 singleForcedTrail = [3]
  0 barrierReleaseComputed : scanReleaseOrdinals %search %search (smallComponent True) 0 4 barrierForcedTrail = [3]
  0 sNotKeyForced : keyForcedOrdinal %search %search barrierForcedTrail 5 = False
  0 singleClosure : ForcedOnTrace %search %search singleForcedTrail 4
  0 barrierClosure : ForcedOnTrace %search %search barrierForcedTrail 5

||| Simultaneous native annotations, computed classifications/release lists,
||| and genuine least-closure derivations. No scalar observer theorem over a
||| nested fixture builder, supplied seed list, or supplied classifier flags.
public export
0 forcedClassifierFixtures : ForcedClassifierFixtures
forcedClassifierFixtures = MkForcedClassifierFixtures
  (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 0)
    (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) _
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 1)
    (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) _
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 2)
    (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) _
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 3)
    (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) _
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 4)
    (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) _
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 5)
    (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) _
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 6)
    (Fired {before = smallState 6} {afterState = smallState 7} %search %search (LAdvance 2) LFinishTag (smallFinish2 smallNativeExecution)) _
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd (smallState 7)))))))))
  (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (barrierState 0)
    (Fired {before = barrierState 0} {afterState = barrierState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) _
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (barrierState 1)
    (Fired {before = barrierState 1} {afterState = barrierState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) _
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (barrierState 2)
    (Fired {before = barrierState 2} {afterState = barrierState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) _
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (barrierState 3)
    (Fired {before = barrierState 3} {afterState = barrierState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) _
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (barrierState 4)
    (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) _
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (barrierState 5)
    (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) _
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (barrierState 6)
    (Fired {before = barrierState 6} {afterState = barrierState 7} %search %search (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution)) _
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (barrierState 7)
    (Fired {before = barrierState 7} {afterState = barrierState 8} %search %search (LAdvance 2) LFinishTag (finishFollowing barrierNativeExecution)) _
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd (barrierState 8))))))))))
  (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search
    (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 5} {afterState = smallState 6} %search %search
      (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) NoTransitions))
  (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 4)
    (Fired {before = smallState 4} {afterState = smallState 5} %search %search
      (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) _
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 5)
      (Fired {before = smallState 5} {afterState = smallState 6} %search %search
        (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) _ (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd (smallState 6))))
  [(3, True)] [(3, True), (4, True)] [(3, False)]
  Refl Refl Refl Refl Refl Refl Refl Refl Refl
  (DGamma.L2R3ForcedClosure.KeyForces Here Refl)
  (DGamma.L2R3ForcedClosure.OrderForces (DGamma.L2R3ForcedClosure.KeyForces Here Refl) (There Here) (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))))

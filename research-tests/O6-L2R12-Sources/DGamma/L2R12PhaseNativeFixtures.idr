module DGamma.L2R12PhaseNativeFixtures

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

||| Authentic Finish0/Retire1/Remove1 fragment and its source-aware trail.
||| Data only: no phase, ownership or interval property is assumed.
public export
phaseFixtureCore : (core : Transitions (smallState 1) (smallState 4) **
  DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace Nat Bool Unit String (\key => Unit) core)
phaseFixtureCore = ((MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions))) ** (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 1) (Fired {before = smallState 1} {afterState = smallState 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions)) (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 2) (Fired {before = smallState 2} {afterState = smallState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions) (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 3) (Fired {before = smallState 3} {afterState = smallState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd (smallState 4))))))

||| The actual lifecycle head of the public three-edge native fragment.
export
0 phaseFixtureLife : LocatedActionOccurrence (LAdvance 0) (fst phaseFixtureCore)
phaseFixtureLife = MkLocatedActionOccurrence (smallState 1) (smallState 2)
  NoTransitions (Fired {before = smallState 1} {afterState = smallState 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions)) Refl Refl

||| Concrete ForcedRootPhase FROM native fragment, release and phase owner
||| decoder. Every seed/anchor/count fact computes on explicit fixture data.
||| This is a fixed certificate, not the general acceptance-to-phase producer.
export
0 singleForcedPhaseDecoded : ForcedRootPhase Nat Bool Unit String (\key => Unit)
  (fst fixtureDictionaries) (snd fixtureDictionaries) (fst ordinalFixtureTrails) (MkRootCatalogEntry 4 3 (smallComponent True))
singleForcedPhaseDecoded = MkForcedRootPhase
  (MkRootCatalogEntry 4 3 (smallComponent True)) Here (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))) Refl
  0 (smallState 1) (smallState 4)
  (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) NoTransitions) (fst phaseFixtureCore) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 5} {afterState = smallState 6} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 6} {afterState = smallState 7} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 2) LFinishTag (smallFinish2 smallNativeExecution)) NoTransitions)))
  (phaseEventsExtended (fst fixtureDictionaries) 0 (snd phaseFixtureCore)
    [Refl, Refl, Refl]) Refl
  smallRelease (LAdvance 0) phaseFixtureLife True Refl Refl
  (phaseLifeOwnerDecoded (fst fixtureDictionaries) 0 (smallState 1) (LAdvance 0) Refl Refl)
  (LTESucc LTEZero) Refl Refl (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))

||| Concrete ForcedRootPhase FROM native fragment, release and phase owner
||| decoder. Every seed/anchor/count fact computes on explicit fixture data.
||| This is a fixed certificate, not the general acceptance-to-phase producer.
export
0 barrierRootPhaseDecoded : ForcedRootPhase Nat Bool Unit String (\key => Unit)
  (fst fixtureDictionaries) (snd fixtureDictionaries) (snd ordinalFixtureTrails) (MkRootCatalogEntry 4 3 (smallComponent True))
barrierRootPhaseDecoded = MkForcedRootPhase
  (MkRootCatalogEntry 4 3 (smallComponent True)) Here (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))) Refl
  0 (smallState 1) (smallState 4)
  (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) NoTransitions) (fst phaseFixtureCore) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 5} {afterState = barrierState 6} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) (MoreTransitions (Fired {before = barrierState 6} {afterState = barrierState 7} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution)) (MoreTransitions (Fired {before = barrierState 7} {afterState = barrierState 8} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 2) LFinishTag (finishFollowing barrierNativeExecution)) NoTransitions))))
  (phaseEventsExtended (fst fixtureDictionaries) 0 (snd phaseFixtureCore)
    [Refl, Refl, Refl]) Refl
  smallRelease (LAdvance 0) phaseFixtureLife True Refl Refl
  (phaseLifeOwnerDecoded (fst fixtureDictionaries) 0 (smallState 1) (LAdvance 0) Refl Refl)
  (LTESucc LTEZero) Refl Refl (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))

||| Concrete ForcedRootPhase FROM native fragment, release and phase owner
||| decoder. Every seed/anchor/count fact computes on explicit fixture data.
||| This is a fixed certificate, not the general acceptance-to-phase producer.
export
0 barrierSuccessorPhaseDecoded : ForcedRootPhase Nat Bool Unit String (\key => Unit)
  (fst fixtureDictionaries) (snd fixtureDictionaries) (snd ordinalFixtureTrails) (MkRootCatalogEntry 5 4 (smallComponent False))
barrierSuccessorPhaseDecoded = MkForcedRootPhase
  (MkRootCatalogEntry 4 3 (smallComponent True)) Here (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))) Refl
  0 (smallState 1) (smallState 4)
  (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) NoTransitions) (fst phaseFixtureCore) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 5} {afterState = barrierState 6} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) (MoreTransitions (Fired {before = barrierState 6} {afterState = barrierState 7} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution)) (MoreTransitions (Fired {before = barrierState 7} {afterState = barrierState 8} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 2) LFinishTag (finishFollowing barrierNativeExecution)) NoTransitions))))
  (phaseEventsExtended (fst fixtureDictionaries) 0 (snd phaseFixtureCore)
    [Refl, Refl, Refl]) Refl
  smallRelease (LAdvance 0) phaseFixtureLife True Refl Refl
  (phaseLifeOwnerDecoded (fst fixtureDictionaries) 0 (smallState 1) (LAdvance 0) Refl Refl)
  (LTESucc LTEZero) Refl Refl (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))

||| Actual located root births accompany all three new phase certificates.
||| Constructed by the catalog decoder, not supplied fixture occurrences.
export
0 phaseFixtureBirths :
  (CatalogBirthAt Nat Bool Unit String (\key => Unit)
    (MkRootCatalogEntry 4 3 (smallComponent True)) 0 smallTrace,
   CatalogBirthAt Nat Bool Unit String (\key => Unit)
    (MkRootCatalogEntry 4 3 (smallComponent True)) 0 barrierTrace,
   CatalogBirthAt Nat Bool Unit String (\key => Unit)
    (MkRootCatalogEntry 5 4 (smallComponent False)) 0 barrierTrace)
phaseFixtureBirths =
  (scanCatalogBirth 0 (fst ordinalFixtureTrails) (MkRootCatalogEntry 4 3 (smallComponent True)) Here,
   scanCatalogBirth 0 (snd ordinalFixtureTrails) (MkRootCatalogEntry 4 3 (smallComponent True)) Here,
   scanCatalogBirth 0 (snd ordinalFixtureTrails) (MkRootCatalogEntry 5 4 (smallComponent False)) (There Here))

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
  AvailabilityTrace Nat Bool Unit String (\key => Unit) core)
phaseFixtureCore = ((MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions))) ** (AvailabilityStep (smallState 1) (Fired {before = smallState 1} {afterState = smallState 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions)) (AvailabilityStep (smallState 2) (Fired {before = smallState 2} {afterState = smallState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions) (AvailabilityStep (smallState 3) (Fired {before = smallState 3} {afterState = smallState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions (AvailabilityEnd (smallState 4))))))

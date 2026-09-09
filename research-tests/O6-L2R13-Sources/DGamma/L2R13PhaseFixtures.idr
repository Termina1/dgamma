module DGamma.L2R13PhaseFixtures

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

||| The GENERAL forced-to-Just producer reproduces all THREE anchors of the
||| L2R12 phase inhabitants, including the unseeded barrier successor.
||| Equality is transported through native equations, not phase proof equality.
export
0 forcedAnchorsReproducePhases :
  (fst (forcedAnchorJust (fst fixtureDictionaries) (snd fixtureDictionaries) (fst ordinalFixtureTrails) 4 True Refl Refl) = transitionCount (phasePrefix singleForcedPhaseDecoded) + S (locatedActionOrdinal (releaseOccurrence (phaseRelease singleForcedPhaseDecoded))),
   fst (forcedAnchorJust (fst fixtureDictionaries) (snd fixtureDictionaries) (snd ordinalFixtureTrails) 4 True Refl Refl) = transitionCount (phasePrefix barrierRootPhaseDecoded) + S (locatedActionOrdinal (releaseOccurrence (phaseRelease barrierRootPhaseDecoded))),
   fst (forcedAnchorJust (fst fixtureDictionaries) (snd fixtureDictionaries) (snd ordinalFixtureTrails) 5 True Refl Refl) = transitionCount (phasePrefix barrierSuccessorPhaseDecoded) + S (locatedActionOrdinal (releaseOccurrence (phaseRelease barrierSuccessorPhaseDecoded))))
forcedAnchorsReproducePhases =
  (cong (fromMaybe 0) (trans (sym (snd (forcedAnchorJust (fst fixtureDictionaries) (snd fixtureDictionaries) (fst ordinalFixtureTrails) 4 True Refl Refl))) (phaseAnchorEquation singleForcedPhaseDecoded)),
   cong (fromMaybe 0) (trans (sym (snd (forcedAnchorJust (fst fixtureDictionaries) (snd fixtureDictionaries) (snd ordinalFixtureTrails) 4 True Refl Refl))) (phaseAnchorEquation barrierRootPhaseDecoded)),
   cong (fromMaybe 0) (trans (sym (snd (forcedAnchorJust (fst fixtureDictionaries) (snd fixtureDictionaries) (snd ordinalFixtureTrails) 5 True Refl Refl))) (phaseAnchorEquation barrierSuccessorPhaseDecoded)))

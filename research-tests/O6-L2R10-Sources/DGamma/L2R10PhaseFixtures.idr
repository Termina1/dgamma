module DGamma.L2R10PhaseFixtures

import Prelude.Types
import Prelude.Interfaces
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R6ForcedScan
import DGamma.L2R9OrdinalScan
import DGamma.L2R9OrdinalTrails
import DGamma.L2R10OrdinalData
import DGamma.L2R10PhaseScan
import DGamma.L2R5RootCatalog
import DGamma.L2R6Anchors
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core
import Decidable.Decidable

%default total
%unbound_implicits off

||| Both observed phase acceptance Booleans are True on public native data.
||| The explicit observations own their native equations simultaneously.
||| These are scanner fixtures, NOT produced ForcedRootPhase certificates.
export
0 phaseScanFixtureObservations :
  ((seen : Bool **
     (phaseScanOk (fst fixtureDictionaries) (snd fixtureDictionaries)
        (fst ordinalFixtureTrails) = seen, seen = True)),
   (seen : Bool **
     (phaseScanOk (fst fixtureDictionaries) (snd fixtureDictionaries)
        (snd ordinalFixtureTrails) = seen, seen = True)))
phaseScanFixtureObservations = ((True ** (Refl, Refl)), (True ** (Refl, Refl)))

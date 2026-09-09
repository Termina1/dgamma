module DGamma.L2R10MoveCutFixtures

import Prelude.Types
import Prelude.Interfaces
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R7CatalogBirth
import DGamma.L2R8DistanceSearch
import DGamma.L2R9ControlClass
import DGamma.L2R9PredecessorClass
import DGamma.L2R9NativeSelection
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core
import Decidable.Decidable
import DGamma.CP4ProgressNoDeadlock
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
import DGamma.L2R6FrontNormal
import DGamma.L2R6Iteration
import DGamma.L2R3ForcedClosure
import DGamma.L2R5Extensional
import DGamma.L2R5ExtensionalRetire
import DGamma.CP4RuntimeBindings
import DGamma.L2R10OrdinalData
import DGamma.L2R10MoveCutObservation
import DGamma.L2R6IterationFixtures

%default total
%unbound_implicits off

||| ACTUAL single-prefix observation FROM the new request producer: native
||| first-positive R, its actual Begin2 predecessor and native early-root
||| applicability. Does NOT project singleAdmitted or reproduce its move.
export
0 singleSelectedCutObservation :
  Prelude.map {f = Maybe}
    (\cut => (catalogRoot (cutEntry cut), catalogOrdinal (cutEntry cut), cutAction cut, isJust (earlyRootResult cut)))
    (observeSelectedMoveCut (fst fixtureDictionaries) (snd fixtureDictionaries) (singleBeforeTrail iterationFixtures)) =
  Just (3, 5, LBegin 2, True)
singleSelectedCutObservation = Refl

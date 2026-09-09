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
import DGamma.L2R13TerminalMove
import DGamma.L2R5Extensional
import DGamma.L2R5CurrentCut
import DGamma.CP4RuntimeBindings
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

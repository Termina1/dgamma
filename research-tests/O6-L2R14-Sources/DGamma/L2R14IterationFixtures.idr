module DGamma.L2R14IterationFixtures

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

import DGamma.L2R13DistanceFixtures
import DGamma.L2R14IterationFromMoves

%default total
%unbound_implicits off

||| Fixed 1->0 and 2->1->0 ITERATIONS FROM the GENERAL local terminal/root-
||| extension move producers. WHOLE endpoints follow from iterationEndpoint;
||| final zero is the unchanged native scalar scan fact. No old admitted move
||| or fixtureIterations is projected to construct either iteration.
||| This is not the missing generic existence/phase-preserving normalizer.
export
0 fixtureIterationsFromProducers :
  ((DistanceIteration (fst fixtureDictionaries) (snd fixtureDictionaries)
      (singleBeforeTrail iterationFixtures) (singleAfterTrail iterationFixtures),
    RegistryExtensional Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (smallState 9) (smallState 6),
    totalDistance (fst fixtureDictionaries) (snd fixtureDictionaries) (singleAfterTrail iterationFixtures) = 0),
   (DistanceIteration (fst fixtureDictionaries) (snd fixtureDictionaries)
      (bundleBeforeTrail iterationFixtures) (bundleAfterTrail iterationFixtures),
    RegistryExtensional Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (bundlePhaseState 3) (barrierState 7),
    totalDistance (fst fixtureDictionaries) (snd fixtureDictionaries) (bundleAfterTrail iterationFixtures) = 0))
fixtureIterationsFromProducers =
  (((IterationMove (fst terminalFixtureMoves) (IterationDone (singleAfterTrail iterationFixtures))), iterationEndpoint (IterationMove (fst terminalFixtureMoves) (IterationDone (singleAfterTrail iterationFixtures))), singleZero iterationFixtures),
   ((IterationMove firstBundleFromProducer (IterationMove (snd terminalFixtureMoves) (IterationDone (bundleAfterTrail iterationFixtures)))), iterationEndpoint (IterationMove firstBundleFromProducer (IterationMove (snd terminalFixtureMoves) (IterationDone (bundleAfterTrail iterationFixtures)))), bundleZero iterationFixtures))

||| All THREE producer moves have exactly the same before/after DISTANCE
||| witnesses as D8. Old records are used ONLY for this comparison, never
||| to construct the new moves or iterations. This is not proof-record equality.
export
0 fixtureProducedMeasuresAgree :
  ((beforeDistance (fst terminalFixtureMoves) = beforeDistance (singleAdmitted iterationFixtures),
    afterDistance (fst terminalFixtureMoves) = afterDistance (singleAdmitted iterationFixtures)),
   (beforeDistance firstBundleFromProducer = beforeDistance (firstBundleAdmitted iterationFixtures),
    afterDistance firstBundleFromProducer = afterDistance (firstBundleAdmitted iterationFixtures)),
   (beforeDistance (snd terminalFixtureMoves) = beforeDistance (secondBundleAdmitted iterationFixtures),
    afterDistance (snd terminalFixtureMoves) = afterDistance (secondBundleAdmitted iterationFixtures)))
fixtureProducedMeasuresAgree =
  (admittedMoveMeasuresUnique (fst terminalFixtureMoves) (singleAdmitted iterationFixtures),
   admittedMoveMeasuresUnique firstBundleFromProducer (firstBundleAdmitted iterationFixtures),
   admittedMoveMeasuresUnique (snd terminalFixtureMoves) (secondBundleAdmitted iterationFixtures))

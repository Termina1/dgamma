module DGamma.L2R6IterationFixtures

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
import DGamma.L2R3BundlePhaseStates
import DGamma.L2R3BundlePhase
import DGamma.L2R3Attached
import DGamma.L2R3SmallAttached
import DGamma.L2R3BarrierBlocks
import DGamma.L2R3AttachedGap
import DGamma.L2R3FixtureCoverage
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R6FrontNormal
import DGamma.L2R6Iteration
import DGamma.L2R3ForcedClosure
import DGamma.L2R5Extensional
import DGamma.L2R5ExtensionalRetire
import DGamma.CP4RuntimeBindings
import Data.List.Elem
import Decidable.Decidable
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Five real full-prefix traces on inherited one-origin states. The three
||| actual admitted steps own located adjacency, native applicability/current
||| cuts, key/barrier forcing, exact-one total distance, and extensional ends.
||| Source fronts are accepted; target prefixes are distance zero, not full
||| Finish2 executions or a general attached-NF/terminal-earliest theorem.
public export
record IterationFixtures where
  constructor MkIterationFixtures
  singleBeforeTrace : Transitions (smallState 0) (smallState 9)
  singleBeforeTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) singleBeforeTrace
  singleAfterTrace : Transitions (smallState 0) (smallState 6)
  singleAfterTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) singleAfterTrace
  bundleBeforeTrace : Transitions (smallState 0) (bundlePhaseState 3)
  bundleBeforeTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) bundleBeforeTrace
  bundleMiddleTrace : Transitions (smallState 0) (bundlePhaseState 6)
  bundleMiddleTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) bundleMiddleTrace
  bundleAfterTrace : Transitions (smallState 0) (barrierState 7)
  bundleAfterTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) bundleAfterTrace
  0 singleAdmitted : AdmittedDistanceMove Nat Bool Unit String (\key => Unit) %search %search singleBeforeTrail singleAfterTrail
  0 firstBundleAdmitted : AdmittedDistanceMove Nat Bool Unit String (\key => Unit) %search %search bundleBeforeTrail bundleMiddleTrail
  0 secondBundleAdmitted : AdmittedDistanceMove Nat Bool Unit String (\key => Unit) %search %search bundleMiddleTrail bundleAfterTrail
  singleInputFront : FrontNormal Nat Bool Unit String (\key => Unit) %search %search singleBeforeTrail
  bundleInputFront : FrontNormal Nat Bool Unit String (\key => Unit) %search %search bundleBeforeTrail
  0 singleZero : totalDistance %search %search singleAfterTrail = 0
  0 bundleZero : totalDistance %search %search bundleAfterTrail = 0

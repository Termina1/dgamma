module DGamma.L2R6FrontFixtures

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
import Decidable.Decidable
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Accepted front-normal/no-forced-control observations on both full actual
||| fixtures. Residual NF fields are inherited honest EMPTY-gap instances,
||| not the missing general placed-bundle-to-inter-block-coverage producer.
public export
record FrontDispositionFixtures
  (0 singleGap : Transitions (smallState 5) (smallState 5))
  (0 bundleGap : Transitions (barrierState 6) (barrierState 6)) where
  constructor MkFrontDispositionFixtures
  singleFrontTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) smallTrace
  barrierFrontTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) barrierTrace
  singleFrontNormal : FrontNormal Nat Bool Unit String (\key => Unit) %search %search singleFrontTrail
  barrierFrontNormal : FrontNormal Nat Bool Unit String (\key => Unit) %search %search barrierFrontTrail
  singleNeverRetired : ForcedRootNeverRetired Nat Bool Unit String (\key => Unit) %search %search singleFrontTrail
  barrierNeverRetired : ForcedRootNeverRetired Nat Bool Unit String (\key => Unit) %search %search barrierFrontTrail
  0 singleResidualNormalForm : AttachedNormalForm Nat Bool Unit String (\key => Unit) %search %search smallTrace singleGap 5
  0 barrierResidualNormalForm : AttachedNormalForm Nat Bool Unit String (\key => Unit) %search %search barrierTrace bundleGap 6

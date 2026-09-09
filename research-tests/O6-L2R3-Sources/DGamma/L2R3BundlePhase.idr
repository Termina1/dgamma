module DGamma.L2R3BundlePhase

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5L2R1RootExchange
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R2RootSnapshot
import DGamma.L2R2RootPhase
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R3BundlePhaseStates
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Two additional checked S edges complete the three physical permutations.
||| All original/alternate endpoints have the same world and ordered bindings;
||| no equality of independently generated erased uniqueness proofs is needed.
public export
record BundlePhaseNative where
  constructor MkBundlePhaseNative
  0 sAfterBeginR : checkedApplyAction @{%search} @{%search} (OInsert 4 Root (smallComponent False)) (bundlePhaseState 2) = Just (OInsertTag, bundlePhaseState 3)
  0 sAfterRBegin : checkedApplyAction @{%search} @{%search} (OInsert 4 Root (smallComponent False)) (bundlePhaseState 5) = Just (OInsertTag, bundlePhaseState 6)
  0 firstMoveSnapshot : runtimeSnapshot (bundlePhaseState 3) = runtimeSnapshot (bundlePhaseState 6)
  0 secondMoveSnapshot : runtimeSnapshot (bundlePhaseState 6) = runtimeSnapshot (bundlePhaseState 8)

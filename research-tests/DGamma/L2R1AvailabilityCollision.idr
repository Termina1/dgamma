module DGamma.L2R1AvailabilityCollision

import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.Metatheory
import DGamma.Section3Example
import DGamma.Unified
import DGamma.R174O17ProvisionCollisionCandidate
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Reify one observed ACTUAL action into its physical trace occurrence.
||| Fixture-local helper; no scheduling or availability conclusion is assumed.
public export
0 l2r1ObservedAction :
  {first, finalState : SystemState Nat ToyKey ToyValue ToyRuntime String} ->
  (trace : Transitions first finalState) -> (wanted : Action Nat ToyKey ToyValue ToyRuntime String) -> (position : Nat) ->
  (rawClosingActionAt Nat ToyKey ToyRuntime String ToyValue position trace = Just wanted) -> LocatedActionOccurrence wanted trace
l2r1ObservedAction NoTransitions wanted position observed = case observed of Refl impossible
l2r1ObservedAction (MoreTransitions (Fired nameEq keyEq action tag checked) rest) wanted Z observed =
  MkLocatedActionOccurrence _ _ NoTransitions (Fired nameEq keyEq action tag checked) rest (justInjective observed) Refl
l2r1ObservedAction (MoreTransitions step rest) wanted (S position) observed =
  currentBirthPrependLocation Nat ToyKey ToyRuntime String ToyValue step rest wanted (l2r1ObservedAction rest wanted position observed)


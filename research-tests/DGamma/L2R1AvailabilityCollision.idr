module DGamma.L2R1AvailabilityCollision

import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4SupportQuiescence
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

||| Exact actual-state annotations; this erased proof reification does not
||| invent earlier availability. The underlying R178 predicate is executable.
public export
0 l2r1Annotate :
  {first, finalState : SystemState Nat ToyKey ToyValue ToyRuntime String} ->
  (trace : Transitions first finalState) -> AvailabilityTrace Nat ToyKey ToyRuntime String ToyValue trace
l2r1Annotate {first} NoTransitions = AvailabilityEnd first
l2r1Annotate {first} (MoreTransitions step rest) = AvailabilityStep first step rest (l2r1Annotate rest)

||| Executable research fixture copy of R174's eight actions. The inherited
||| exported r174ProvisionExecution does not unfold externally, so that exact
||| original occurrence claim is parked (C6), NOT assumed. This independently
||| checked fixture retains the actual provision collision and all guards.
public export
0 l2r1CollisionExecution : CertifiedActionTrace Nat ToyKey ToyRuntime String ToyValue %search %search
  (MkSystemState (MkToyRuntime False False) emptyContext)
l2r1CollisionExecution = fromMaybe
  (MkCertifiedActionTrace (MkSystemState (MkToyRuntime False False) emptyContext)
    NoTransitions TraceComponentsTotalEnd)
  (buildCertifiedActionTrace %search %search
    [OInsert 0 Root r174ProvisionParent, LBegin 0,
     OInsert 1 (ChildOf 0) providerComponent, ORetire 1, ORemove 1,
     OInsert 2 Root providerComponent, ORetire 2, LAdvance 0]
    (MkSystemState (MkToyRuntime False False) emptyContext))
||| Excludes the fallback: all eight native checked actions actually ran.
||| The original R174 scalar shape is NOT used as an applicability premise.
export
0 l2r1CollisionRan : transitionCount (certifiedTrace l2r1CollisionExecution) = 8
l2r1CollisionRan = Refl

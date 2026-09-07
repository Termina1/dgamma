module DGamma.R174O17ProvisionCollisionCandidate

import DGamma.Core
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4SupportQuiescence
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5RawClosingRankSpike
import DGamma.Metatheory
import DGamma.Section3Example
import DGamma.Unified
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| The parent has no provision; its tagged iterator can license a child.
||| This does not by itself construct a RegistrationProtocol/Discipline.
public export
r174ProvisionParentStep : StepEffect ToyKey ToyValue ToyRuntime String [] DGamma.CalculusChecks.toyEmptySpec
r174ProvisionParentStep = MkStepEffect (Just 0)
  (\NoDepValues, before => Right (before, Prelude.id))
  (\NoDepValues, before, after, undo, returned, canonical =>
    replace {p = \outcome => case outcome of
      Left _ => Unit
      Right (next, inverse) => inverse (normalizeLocal DGamma.CalculusChecks.toyEmptySpec next) = before}
      returned canonical)

public export
r174ProvisionParent : Component ToyKey ToyValue ToyRuntime String
r174ProvisionParent = MkComponent DGamma.CalculusChecks.toyEmptySpec
  DGamma.CalculusChecks.toyEmptySpec [r174ProvisionParentStep]

||| Execute all eight ACTUAL checked actions, certifying transition totality
||| simultaneously. Names 1 and 2 use the genuine installing provider program.
||| The next count equation must exclude this empty fallback before any claim
||| of input inhabitation. The production builder is proof-erased.
export
0 r174ProvisionExecution : CertifiedActionTrace Nat ToyKey ToyRuntime String ToyValue %search %search
  (MkSystemState (MkToyRuntime False False) emptyContext)
r174ProvisionExecution = fromMaybe
  (MkCertifiedActionTrace (MkSystemState (MkToyRuntime False False) emptyContext)
    NoTransitions TraceComponentsTotalEnd)
  (buildCertifiedActionTrace %search %search
    [OInsert 0 Root r174ProvisionParent, LBegin 0,
     OInsert 1 (ChildOf 0) providerComponent, ORetire 1, ORemove 1,
     OInsert 2 Root providerComponent, ORetire 2, LAdvance 0]
    (MkSystemState (MkToyRuntime False False) emptyContext))

||| Genuine checked execution, NOT the empty fallback. Every insertion passed
||| the live single-source guard; final support is the open parent alone.
export
0 r174ProvisionExecutionChecks :
  ((transitionCount (certifiedTrace r174ProvisionExecution),
    quiet {name = Nat} {key = ToyKey} {value = ToyValue} {world = ToyRuntime} {error = String}
      (certifiedFinal r174ProvisionExecution),
    noFailedFibers (certifiedFinal r174ProvisionExecution),
    allFibersTotalOnProvision (certifiedFinal r174ProvisionExecution),
    supportSet {name = Nat} {key = ToyKey} {value = ToyValue} {world = ToyRuntime} {error = String}
      (certifiedFinal r174ProvisionExecution)) = (8, True, True, True, [0]))
r174ProvisionExecutionChecks = Refl

||| The actual built trace has raw births 0 at 0, 1 at 2, and 2 at 5 only.
||| The formula merely names those three positions for the uniqueness proof.
export
0 r174ProvisionBirthPosition :
  (selected, ordinal : Nat) ->
  (rawInsertionNameAt Nat ToyKey ToyRuntime String ToyValue ordinal
    (certifiedTrace r174ProvisionExecution) = Just selected) ->
  (ordinal = selected + selected + (minus selected 1))
r174ProvisionBirthPosition selected Z observed = case observed of Refl => Refl
r174ProvisionBirthPosition selected (S Z) observed = case observed of Refl impossible
r174ProvisionBirthPosition selected (S (S Z)) observed = case observed of Refl => Refl
r174ProvisionBirthPosition selected (S (S (S Z))) observed = case observed of Refl impossible
r174ProvisionBirthPosition selected (S (S (S (S Z)))) observed = case observed of Refl impossible
r174ProvisionBirthPosition selected (S (S (S (S (S Z))))) observed = case observed of Refl => Refl
r174ProvisionBirthPosition selected (S (S (S (S (S (S Z)))))) observed = case observed of Refl impossible
r174ProvisionBirthPosition selected (S (S (S (S (S (S (S Z))))))) observed = case observed of Refl impossible
r174ProvisionBirthPosition selected (S (S (S (S (S (S (S (S later)))))))) observed = case observed of Refl impossible

||| Fixture-only observation reification: exact actual actions, no placement
||| producer or O17 capital. Kept here so the checked R174 builder can reduce.
0 r178R174ObservedAction :
  {first, finalState : SystemState Nat ToyKey ToyValue ToyRuntime String} ->
  (trace : Transitions first finalState) -> (wanted : Action Nat ToyKey ToyValue ToyRuntime String) -> (position : Nat) ->
  (rawClosingActionAt Nat ToyKey ToyRuntime String ToyValue position trace = Just wanted) -> LocatedActionOccurrence wanted trace
r178R174ObservedAction NoTransitions wanted position observed = case observed of Refl impossible
r178R174ObservedAction (MoreTransitions (Fired nameEq keyEq action tag checked) rest) wanted Z observed =
  MkLocatedActionOccurrence _ _ NoTransitions (Fired nameEq keyEq action tag checked) rest (justInjective observed) Refl
r178R174ObservedAction (MoreTransitions step rest) wanted (S position) observed =
  currentBirthPrependLocation Nat ToyKey ToyRuntime String ToyValue step rest wanted (r178R174ObservedAction rest wanted position observed)

||| Fixture-only erased reconstruction of explicit actual-state annotations.
||| The runtime observer itself remains executable; no sorting proof is built.
0 r178R174Annotate :
  {first, finalState : SystemState Nat ToyKey ToyValue ToyRuntime String} ->
  (trace : Transitions first finalState) -> AvailabilityTrace Nat ToyKey ToyRuntime String ToyValue trace
r178R174Annotate {first} NoTransitions = AvailabilityEnd first
r178R174Annotate {first} (MoreTransitions step rest) = AvailabilityStep first step rest (r178R174Annotate rest)

||| Authorized independent scalar-fixture route: the returned annotations own
||| an ACTUAL prefix/suffix decomposition, with no located-root packet.
0 r178R174AnnotatedPrefix :
  {first, finalState : SystemState Nat ToyKey ToyValue ToyRuntime String} ->
  (count : Nat) -> (trace : Transitions first finalState) ->
  (middle : SystemState Nat ToyKey ToyValue ToyRuntime String **
   prior : Transitions first middle ** later : Transitions middle finalState **
   (appendTransitions prior later = trace, AvailabilityTrace Nat ToyKey ToyRuntime String ToyValue prior))
r178R174AnnotatedPrefix {first} Z trace = (first ** NoTransitions ** trace ** (Refl, AvailabilityEnd first))
r178R174AnnotatedPrefix {first} (S count) NoTransitions = (first ** NoTransitions ** NoTransitions ** (Refl, AvailabilityEnd first))
r178R174AnnotatedPrefix {first} (S count) (MoreTransitions step rest) =
  case r178R174AnnotatedPrefix count rest of
    (middle ** prior ** later ** (decomposition, annotations)) =>
      (middle ** MoreTransitions step prior ** later **
        (cong (MoreTransitions step) decomposition, AvailabilityStep first step prior annotations))

||| Scalar observations over the ACTUAL root action and authenticated prefix:
||| root=2; prefix length=5; lifecycle at1; removal of1 at4; snapshot free at1;
||| then compatible cuts0..5. No EarliestAvailableRootBirth is claimed here.
export
0 r178R174ScalarIntervalShape :
  ((case rawClosingActionAt Nat ToyKey ToyRuntime String ToyValue 5 (certifiedTrace r174ProvisionExecution) of
    Just (OInsert root Root component) =>
      case r178R174AnnotatedPrefix 5 (certifiedTrace r174ProvisionExecution) of
        (middle ** prior ** later ** (decomposition, annotations)) =>
          [root == 2, transitionCount prior == 5,
           (case rawClosingActionAt Nat ToyKey ToyRuntime String ToyValue 1 prior of Just action => isLifecycleAction action; Nothing => False),
           (case rawClosingActionAt Nat ToyKey ToyRuntime String ToyValue 4 prior of Just (ORemove 1) => True; _ => False),
           (case annotations of AvailabilityStep _ _ _ (AvailabilityStep early _ _ _) => rootDeclaredProvisionsFree Nat ToyKey ToyRuntime String ToyValue %search component early; _ => False),
           rootCutCompatible Nat ToyKey ToyRuntime String ToyValue %search %search component 0 annotations,
           rootCutCompatible Nat ToyKey ToyRuntime String ToyValue %search %search component 1 annotations,
           rootCutCompatible Nat ToyKey ToyRuntime String ToyValue %search %search component 2 annotations,
           rootCutCompatible Nat ToyKey ToyRuntime String ToyValue %search %search component 3 annotations,
           rootCutCompatible Nat ToyKey ToyRuntime String ToyValue %search %search component 4 annotations,
           rootCutCompatible Nat ToyKey ToyRuntime String ToyValue %search %search component 5 annotations]
    _ => []) =
    [True, True, True, True, True, False, False, False, False, False, True])
r178R174ScalarIntervalShape = Refl

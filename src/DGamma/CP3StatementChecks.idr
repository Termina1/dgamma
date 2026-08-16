module DGamma.CP3StatementChecks

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Decidable.Equality
import Data.List.Elem

%default total

||| Regression guard for Erratum #3's three independent child-registration
||| obligations: Reloading parent, no later rebirth, and retirement provenance.
public export
0 childRegistrationDisciplineGuard :
  {before, afterState, finalState : SystemState name key value world error} ->
  {rest : Transitions afterState finalState} ->
  RegistrationStepDiscipline nameEq
    (OInsert child (ChildOf parent) component) before rest ->
  (ParentActivationPhase nameEq parent before,
   NoLaterInsertion child rest,
   ChildRetirementProvenance parent child rest)
childRegistrationDisciplineGuard evidence = evidence

||| Regression guard for round-1 blocker 1: Lemma 70 cannot be applied without
||| a checked reachability witness from an empty, well-formed registry and the
||| separate Erratum-3 trace discipline.
public export
0 supportLemma70Guard :
  supportAtQuiescenceTheorem name key value world error ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  (reached : ReachedFromEmpty name key world error value nameEq keyEq state) ->
  RegistrationDiscipline nameEq (reachTrace reached) ->
  PrecedenceAcyclic nameEq state ->
  quiet @{nameEq} @{keyEq} state = True ->
  noFailedFibers state = True ->
  ComponentsTotalOnProvision @{nameEq} @{keyEq} state ->
  SupportMatchesActive nameEq keyEq state
supportLemma70Guard claim nameEq keyEq state reached discipline acyclic
  quietState noFailures totality =
    claim nameEq keyEq state reached discipline acyclic quietState noFailures
      totality

||| Real Lemma-68 regression projections: the guard applies the theorem only
||| after reachability and registration provenance, then extracts each result.
public export
0 supportLemma68Guard :
  supportWellFoundedTheorem name key value world error ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  (reached : ReachedFromEmpty name key world error value nameEq keyEq state) ->
  RegistrationDiscipline nameEq (reachTrace reached) ->
  PrecedenceAcyclic nameEq state ->
  SupportWellFounded nameEq state
supportLemma68Guard claim nameEq keyEq state reached discipline acyclic =
  combinedWellFounded
    (claim nameEq keyEq state reached discipline acyclic)

public export
0 supportLemma68UniqueGuard :
  supportWellFoundedTheorem name key value world error ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  (reached : ReachedFromEmpty name key world error value nameEq keyEq state) ->
  RegistrationDiscipline nameEq (reachTrace reached) ->
  PrecedenceAcyclic nameEq state ->
  (candidate : name -> Bool) ->
  SupportSolution @{nameEq} @{keyEq} candidate state ->
  (n : name) -> candidate n = isSupported @{nameEq} @{keyEq} n state
supportLemma68UniqueGuard claim nameEq keyEq state reached discipline acyclic =
  uniqueSupportSolution
    (claim nameEq keyEq state reached discipline acyclic)

||| Regression guards for Equation 62 and Theorem 73's canonical fields.
public export
0 canonicalOrderUniqueGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value nameEq keyEq trace) ->
  UniqueKeys (supportOrder schedule)
canonicalOrderUniqueGuard schedule = orderUnique (supportLinearization schedule)

public export
0 canonicalCombinedOrderGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value nameEq keyEq trace) ->
  (lower, upper : name) ->
  SupportPath nameEq originalFinal lower upper ->
  Elem lower (supportOrder schedule) -> Elem upper (supportOrder schedule) ->
  BeforeIn lower upper (supportOrder schedule)
canonicalCombinedOrderGuard schedule =
  supportPathsOrdered (supportLinearization schedule)

public export
0 canonicalCoverageGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value nameEq keyEq trace) ->
  LifecycleActorsCovered (supportOrder schedule) (canonicalTrace schedule)
canonicalCoverageGuard schedule = lifecycleCoverage schedule

public export
0 canonicalInputPlacementGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value nameEq keyEq trace) ->
  CanonicalInputPlacement name key world error value nameEq keyEq originalFinal
    (supportOrder schedule) (canonicalTrace schedule)
canonicalInputPlacementGuard schedule = inputPlacement schedule

public export
0 canonicalAllRootInputsGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value nameEq keyEq trace) ->
  RootInputsBeforeLifecycle nameEq (canonicalTrace schedule)
canonicalAllRootInputsGuard schedule =
  allRootInputsFirst (inputPlacement schedule)

public export
0 canonicalExternalInputsGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value nameEq keyEq trace) ->
  SameExternalOrchestration nameEq trace (canonicalTrace schedule)
canonicalExternalInputsGuard schedule = sameInputs schedule

public export
0 canonicalBlockGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value nameEq keyEq trace) ->
  (n : name) -> (present : Elem n (supportOrder schedule)) ->
  LocatedOpenEpisodeBlock name key world error value nameEq keyEq n
    (canonicalTrace schedule)
canonicalBlockGuard schedule = canonicalBlock schedule

public export
0 canonicalBlockOrderGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value nameEq keyEq trace) ->
  (earlier, later : name) ->
  (earlierIn : Elem earlier (supportOrder schedule)) ->
  (laterIn : Elem later (supportOrder schedule)) ->
  BeforeIn earlier later (supportOrder schedule) ->
  BlockBefore name key world error value nameEq keyEq (canonicalTrace schedule)
    earlier later (canonicalBlock schedule earlier earlierIn)
    (canonicalBlock schedule later laterIn)
canonicalBlockOrderGuard schedule = blocksFollowOrder schedule

||| Regression guard for Equation 53 modulo the explicitly withdrawn endpoint
||| names. Outside that set the relation is the complete fiber control relation.
public export
0 canonicalFullControlGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value nameEq keyEq trace) ->
  ControlEquivalentOutside nameEq
    (endpointWithdrawnNames (canonicalEndpoint schedule)) originalFinal
    (canonicalFinal schedule)
canonicalFullControlGuard schedule =
  endpointControlsOutside (canonicalEndpoint schedule)

public export
0 canonicalWithdrawalGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value nameEq keyEq trace) ->
  RegisteredNamesWithdrawn nameEq
    (endpointWithdrawnNames (canonicalEndpoint schedule)) originalFinal
    (canonicalFinal schedule)
canonicalWithdrawalGuard schedule = endpointNamesWithdrawn (canonicalEndpoint schedule)

||| Regression guards for Lemma 72's selected-episode deletion and outside-R
||| control/withdrawal conclusions.
public export
0 deletionSubsequenceGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} -> {selected : name} ->
  {episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected original} -> {registered : List name} ->
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered) ->
  ActionSubsequence (EpisodeDeletedActor selected registered)
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode)))
    (survivingEpisode result)
deletionSubsequenceGuard result = episodeDeletion result

public export
0 deletionBeforeGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} -> {selected : name} ->
  {episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected original} -> {registered : List name} ->
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered) ->
  ActionSubsequence (RegisteredActor registered) (traceBeforeOpening episode)
    (survivingBefore result)
deletionBeforeGuard result = beforeDeletion result

public export
0 deletionAfterGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} -> {selected : name} ->
  {episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected original} -> {registered : List name} ->
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered) ->
  ActionSubsequence (RegisteredActor registered) (traceAfterClosing episode)
    (survivingAfter result)
deletionAfterGuard result = afterDeletion result

public export
0 deletionEffectsGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} -> {selected : name} ->
  {episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected original} -> {registered : List name} ->
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} originalFinal)
    (projectEffectState @{nameEq} (survivingFinal result))
deletionEffectsGuard result = effectsPreserved result

public export
0 deletionOutsideControlGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} -> {selected : name} ->
  {episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected original} -> {registered : List name} ->
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered) ->
  ControlEquivalentOutside nameEq registered originalFinal (survivingFinal result)
deletionOutsideControlGuard result = controlsPreservedOutside result

public export
0 deletionWithdrawnGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} -> {selected : name} ->
  {episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected original} -> {registered : List name} ->
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered) ->
  RegisteredNamesWithdrawn nameEq registered originalFinal (survivingFinal result)
deletionWithdrawnGuard result = registeredWithdrawn result

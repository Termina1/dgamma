module DGamma.CP3StatementChecks

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Decidable.Equality
import Data.List.Elem

%default total

||| Every externally inserted component is enrolled in the shared rank protocol;
||| legal name reissue is not forbidden.
public export
0 rootRegistrationRankGuard :
  {before, afterState, finalState : SystemState name key value world error} ->
  {rest : Transitions afterState finalState} ->
  RegistrationStepDiscipline protocol nameEq
    (OInsert root Root component) before rest ->
  (rank : Nat ** registrationRank protocol component = Just rank)
rootRegistrationRankGuard evidence = evidence

||| Regression guard for the yielded-registration source and inverse fields.
public export
0 childRegistrationDisciplineGuard :
  {before, afterState, finalState : SystemState name key value world error} ->
  {rest : Transitions afterState finalState} ->
  RegistrationStepDiscipline protocol nameEq
    (OInsert child (ChildOf parent) component) before rest ->
  (ParentRegistrationYield protocol nameEq parent component before,
   ChildRetirementProvenance parent child rest)
childRegistrationDisciplineGuard evidence = evidence

||| The round-3 arbitrary-child attack used `Reloading []`; source membership
||| makes a yielded child from an empty program impossible.
public export
0 emptyParentCannotRegisterGuard :
  (evidence : ParentRegistrationYield protocol nameEq parent component state) ->
  componentProgram (fiberComponent (parentFiberAtYield evidence)) = [] -> Void
emptyParentCannotRegisterGuard evidence emptyProgram =
  case replace
    {p = \program => Elem (sourceStep evidence) program}
    emptyProgram (sourceBelongsToProgram evidence) of
      Here impossible
      There later impossible

||| Regression guard for round-1 blocker 1: Lemma 70 cannot be applied without
||| a checked reachability witness from an empty, well-formed registry and the
||| separate Erratum-3 trace discipline.
public export
0 supportLemma70Guard :
  supportAtQuiescenceTheorem name key value world error ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (state : SystemState name key value world error) ->
  (reached : ReachedFromEmpty name key world error value nameEq keyEq state) ->
  RegistrationDiscipline protocol nameEq (reachTrace reached) ->
  PrecedenceAcyclic nameEq state ->
  quiet @{nameEq} @{keyEq} state = True ->
  noFailedFibers state = True ->
  ComponentsTotalOnProvision @{nameEq} @{keyEq} state ->
  SupportMatchesActive nameEq keyEq state
supportLemma70Guard claim nameEq keyEq protocol state reached discipline acyclic
  quietState noFailures totality =
    claim nameEq keyEq protocol state reached discipline acyclic quietState noFailures
      totality

||| Real Lemma-68 regression projections: the guard applies the theorem only
||| after reachability and registration provenance, then extracts each result.
public export
0 supportLemma68Guard :
  supportWellFoundedTheorem name key value world error ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (state : SystemState name key value world error) ->
  (reached : ReachedFromEmpty name key world error value nameEq keyEq state) ->
  RegistrationProvenance protocol nameEq (reachTrace reached) ->
  PrecedenceAcyclic nameEq state ->
  SupportWellFounded nameEq state
supportLemma68Guard claim nameEq keyEq protocol state reached discipline acyclic =
  combinedWellFounded
    (claim nameEq keyEq protocol state reached discipline acyclic)

public export
0 supportLemma68UniqueGuard :
  supportWellFoundedTheorem name key value world error ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (state : SystemState name key value world error) ->
  (reached : ReachedFromEmpty name key world error value nameEq keyEq state) ->
  RegistrationProvenance protocol nameEq (reachTrace reached) ->
  PrecedenceAcyclic nameEq state ->
  (candidate : name -> Bool) ->
  SupportSolution @{nameEq} @{keyEq} candidate state ->
  (n : name) -> candidate n = isSupported @{nameEq} @{keyEq} n state
supportLemma68UniqueGuard claim nameEq keyEq protocol state reached discipline acyclic =
  uniqueSupportSolution
    (claim nameEq keyEq protocol state reached discipline acyclic)

||| Regression guards for Equation 62 and Theorem 73's canonical fields.
public export
0 canonicalOrderUniqueGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value protocol nameEq keyEq trace) ->
  UniqueKeys (supportOrder schedule)
canonicalOrderUniqueGuard schedule = orderUnique (supportLinearization schedule)

public export
0 canonicalCombinedOrderGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value protocol nameEq keyEq trace) ->
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
  (schedule : CanonicalSchedule name key world error value protocol nameEq keyEq trace) ->
  LifecycleActorsCovered (supportOrder schedule) (canonicalTrace schedule)
canonicalCoverageGuard schedule = lifecycleCoverage schedule

public export
0 canonicalInputPlacementGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value protocol nameEq keyEq trace) ->
  CanonicalInputPlacement name key world error value nameEq keyEq originalFinal
    (supportOrder schedule) (canonicalTrace schedule)
canonicalInputPlacementGuard schedule = inputPlacement schedule

public export
0 canonicalAllRootInputsGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value protocol nameEq keyEq trace) ->
  RootInputsBeforeLifecycle nameEq (canonicalTrace schedule)
canonicalAllRootInputsGuard schedule =
  allRootInputsFirst (inputPlacement schedule)

public export
0 canonicalExternalInputsGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value protocol nameEq keyEq trace) ->
  SameExternalOrchestration nameEq trace (canonicalTrace schedule)
canonicalExternalInputsGuard schedule = sameInputs schedule

public export
0 canonicalRegistrationDisciplineGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value protocol nameEq keyEq
    trace) ->
  RegistrationDiscipline protocol nameEq (canonicalTrace schedule)
canonicalRegistrationDisciplineGuard schedule =
  canonicalRegistrationDiscipline schedule

public export
0 canonicalRegistrationTreeGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value protocol nameEq keyEq
    trace) ->
  CanonicalRegistrationCorrespondence trace (canonicalTrace schedule)
    (endpointWithdrawnNames (canonicalEndpoint schedule))
canonicalRegistrationTreeGuard schedule = canonicalRegistrationTree schedule

public export
0 canonicalWithdrawnRegistrationGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value protocol nameEq keyEq
    trace) ->
  (child : name) ->
  Elem child (endpointWithdrawnNames (canonicalEndpoint schedule)) ->
  (parent : name **
   component : Component key value world error **
    (ActionOccurs (OInsert child (ChildOf parent) component) trace,
     ActionOccurs (OInsert child (ChildOf parent) component)
       (canonicalTrace schedule) -> Void))
canonicalWithdrawnRegistrationGuard schedule =
  withdrawnRegistrationRemoved (canonicalRegistrationTree schedule)

public export
0 canonicalBlockGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value protocol nameEq keyEq trace) ->
  (n : name) -> (present : Elem n (supportOrder schedule)) ->
  LocatedOpenEpisodeBlock name key world error value nameEq keyEq n
    (canonicalTrace schedule)
canonicalBlockGuard schedule = canonicalBlock schedule

public export
0 canonicalBlockOrderGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value protocol nameEq keyEq trace) ->
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
  (schedule : CanonicalSchedule name key world error value protocol nameEq keyEq trace) ->
  ControlEquivalentOutside nameEq
    (endpointWithdrawnNames (canonicalEndpoint schedule)) originalFinal
    (canonicalFinal schedule)
canonicalFullControlGuard schedule =
  endpointControlsOutside (canonicalEndpoint schedule)

public export
0 canonicalWithdrawalGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value protocol nameEq keyEq trace) ->
  RegisteredNamesWithdrawn nameEq
    (endpointWithdrawnNames (canonicalEndpoint schedule)) originalFinal
    (canonicalFinal schedule)
canonicalWithdrawalGuard schedule = endpointNamesWithdrawn (canonicalEndpoint schedule)

||| Lemma-56 guards: the same-input package exports both the bijection and the
||| transported registration-tree correspondence.
public export
0 orchestrationRenamingGuard :
  {leftFirst, leftFinal, rightFirst, rightFinal :
    SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} ->
  {right : Transitions rightFirst rightFinal} ->
  (same : SameOrchestrationModuloGenerated nameEq left right) ->
  NameBijection name
orchestrationRenamingGuard same = generatedNameBijection same

public export
0 registrationRenamingGuard :
  (same : SameOrchestrationModuloGenerated nameEq left right) ->
  RegistrationCorrespondenceByRenaming (generatedNameBijection same) left right
registrationRenamingGuard same = generatedRegistrationTree same

public export
0 confluenceRenamedEndpointGuard :
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {left : Transitions initial leftFinal} ->
  {right : Transitions initial rightFinal} ->
  (result : ConfluenceResult name key world error value protocol nameEq keyEq
    left right renaming) ->
  SystemEquivalentByRenaming name key world error value nameEq keyEq renaming
    leftFinal rightFinal
confluenceRenamedEndpointGuard result = finalEndpointsEquivalent result

||| Semantic guard for the round-3 retirement blocker: outside R, an action of
||| the selected actor is deletable only through the lifecycle constructor.
public export
0 selectedDeletionLifecycleGuard :
  (evidence : EpisodeDeletedActor selected registered action) ->
  Not (Elem (actionOwner action) registered) ->
  actionOwner action = selected ->
  isLifecycleAction action = True
selectedDeletionLifecycleGuard (DeleteEpisodeLifecycle owner lifecycle)
  outside selectedOwner = lifecycle
selectedDeletionLifecycleGuard (DeleteRegisteredActor present)
  outside selectedOwner = void (outside present)

public export
0 selectedRetireSurvivesGuard :
  EpisodeDeletedActor selected [] (ORetire selected) -> Void
selectedRetireSurvivesGuard
  (DeleteEpisodeLifecycle Refl lifecycle) = case lifecycle of Refl impossible
selectedRetireSurvivesGuard (DeleteRegisteredActor present) = absurd present

public export
0 selectedRemoveSurvivesGuard :
  EpisodeDeletedActor selected [] (ORemove selected) -> Void
selectedRemoveSurvivesGuard
  (DeleteEpisodeLifecycle Refl lifecycle) = case lifecycle of Refl impossible
selectedRemoveSurvivesGuard (DeleteRegisteredActor present) = absurd present

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

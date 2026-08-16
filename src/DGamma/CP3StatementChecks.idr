module DGamma.CP3StatementChecks

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Decidable.Equality
import Data.List.Elem
import Data.Nat

%default total

||| A concrete nonrecursive tagged registration instance. It prevents the
||| source/rank API checks below from passing only because their premise is
||| empty, as happened in round 4.
public export
data RegistrationTestKey : Type where

public export
RegistrationTestValue : RegistrationTestKey -> Type
RegistrationTestValue key impossible

registrationTestSpec : CoeffectSpec RegistrationTestKey
registrationTestSpec = MkCoeffectSpec [] UniqueNil

registrationTestStep : StepEffect RegistrationTestKey RegistrationTestValue
  Unit String [] DGamma.CP3StatementChecks.registrationTestSpec
registrationTestStep = MkStepEffect (Just 0)
  (\NoDepValues, before => Right (before, id))
  (\NoDepValues, before, after, undo, returned =>
    replace
      {p = \outcome => case outcome of
        Left _ => Unit
        Right (next, inverse) => inverse next = before}
      returned Refl)

registrationTestChild : Component RegistrationTestKey RegistrationTestValue
  Unit String
registrationTestChild = MkComponent registrationTestSpec registrationTestSpec []

registrationTestParent : Component RegistrationTestKey RegistrationTestValue
  Unit String
registrationTestParent = MkComponent registrationTestSpec registrationTestSpec
  [registrationTestStep]

registrationTestCatalog : Nat -> Maybe
  (Component RegistrationTestKey RegistrationTestValue Unit String)
registrationTestCatalog Z = Just registrationTestChild
registrationTestCatalog (S later) = Nothing

registrationTestRank : Component RegistrationTestKey RegistrationTestValue
  Unit String -> Maybe Nat
registrationTestRank (MkComponent deps provision []) = Just 1
registrationTestRank (MkComponent deps provision (step :: rest)) = Just 0

0 registrationTestYieldRanks :
  (parent, child : Component RegistrationTestKey RegistrationTestValue Unit String) ->
  (step : StepEffect RegistrationTestKey RegistrationTestValue Unit String
    (dependencies (componentDependencies parent))
    (componentProvisions parent)) ->
  (tag, parentRank, childRank : Nat) ->
  Elem step (componentProgram parent) ->
  registrationTestRank parent = Just parentRank ->
  registrationTestRank child = Just childRank ->
  registrationYieldTag step = Just tag ->
  registrationTestCatalog tag = Just child ->
  LT parentRank childRank
registrationTestYieldRanks (MkComponent deps provision []) child step tag
  parentRank childRank source parentRanked childRanked stepTag cataloged =
    case source of Here impossible; There later impossible
registrationTestYieldRanks
  (MkComponent deps provision (first :: rest)) child step Z
  parentRank childRank source parentRanked childRanked stepTag cataloged =
    case cataloged of
      Refl => case parentRanked of
        Refl => case childRanked of
          Refl => LTESucc LTEZero
registrationTestYieldRanks
  (MkComponent deps provision (first :: rest)) child step (S tag)
  parentRank childRank source parentRanked childRanked stepTag cataloged =
    case cataloged of Refl impossible

0 registrationTestPrecedenceRanks :
  (provider, consumer : Component RegistrationTestKey RegistrationTestValue
    Unit String) ->
  (providerRank, consumerRank : Nat) ->
  registrationTestRank provider = Just providerRank ->
  registrationTestRank consumer = Just consumerRank ->
  (k : RegistrationTestKey) ->
  Elem k (dependencies (componentProvisions provider)) ->
  Elem k (dependencies (componentDependencies consumer)) ->
  LT providerRank consumerRank
registrationTestPrecedenceRanks provider consumer providerRank consumerRank
  providerRanked consumerRanked k provides depends impossible

registrationTestProtocol : RegistrationProtocol RegistrationTestKey
  RegistrationTestValue Unit String
registrationTestProtocol = MkRegistrationProtocol registrationTestCatalog
  registrationTestRank registrationTestYieldRanks registrationTestPrecedenceRanks

registrationTestParentFiber : Fiber Nat RegistrationTestKey RegistrationTestValue
  Unit String
registrationTestParentFiber = MkFiber registrationTestParent Root False emptyOwned
  (Reloading [registrationTestStep] id EmptyView)

registrationTestState : SystemState Nat RegistrationTestKey RegistrationTestValue
  Unit String
registrationTestState = MkSystemState ()
  (MkCoeffectContext [Bind 0 registrationTestParentFiber]
    (UniqueCons zeroNotInEmpty UniqueNil))
  where
  zeroNotInEmpty : Not (Elem (the Nat 0) [])
  zeroNotInEmpty present = absurd present

registrationTestNameEq : DecEq Nat
registrationTestNameEq = %search

implementation DecEq RegistrationTestKey where
  decEq key impossible

registrationTestKeyEq : DecEq RegistrationTestKey
registrationTestKeyEq = %search

registrationTestInitial : SystemState Nat RegistrationTestKey
  RegistrationTestValue Unit String
registrationTestInitial = MkSystemState () emptyContext

registrationTestInactiveParent : Fiber Nat RegistrationTestKey
  RegistrationTestValue Unit String
registrationTestInactiveParent = MkFiber registrationTestParent Root False
  emptyOwned (Inactive Nothing)

registrationTestInserted : SystemState Nat RegistrationTestKey
  RegistrationTestValue Unit String
registrationTestInserted = MkSystemState ()
  (MkCoeffectContext [Bind 0 registrationTestInactiveParent]
    (UniqueCons zeroNotInEmpty UniqueNil))
  where
  zeroNotInEmpty : Not (Elem (the Nat 0) [])
  zeroNotInEmpty present = absurd present

registrationTestChildFiber : Fiber Nat RegistrationTestKey
  RegistrationTestValue Unit String
registrationTestChildFiber = MkFiber registrationTestChild (ChildOf 0) False
  emptyOwned (Inactive Nothing)

registrationTestChildInserted : SystemState Nat RegistrationTestKey
  RegistrationTestValue Unit String
registrationTestChildInserted = MkSystemState ()
  (MkCoeffectContext
    [Bind 1 registrationTestChildFiber, Bind 0 registrationTestParentFiber]
    (UniqueCons oneNotZero (UniqueCons zeroNotInEmpty UniqueNil)))
  where
  oneNotZero : Not (Elem (the Nat 1) [the Nat 0])
  oneNotZero Here impossible
  oneNotZero (There later) = absurd later
  zeroNotInEmpty : Not (Elem (the Nat 0) [])
  zeroNotInEmpty present = absurd present

||| Positive inhabitant of the exact child-registration premise.
public export
0 positiveParentRegistrationYield : ParentRegistrationYield
  DGamma.CP3StatementChecks.registrationTestProtocol
  DGamma.CP3StatementChecks.registrationTestNameEq 0
  DGamma.CP3StatementChecks.registrationTestChild
  DGamma.CP3StatementChecks.registrationTestState
positiveParentRegistrationYield = MkParentRegistrationYield
  registrationTestParentFiber Refl registrationTestStep [] id EmptyView Refl Here
  0 1 Refl Refl 0 Refl Refl

roleChangingApply :
  Action Nat RegistrationTestKey RegistrationTestValue Unit String ->
  SystemState Nat RegistrationTestKey RegistrationTestValue Unit String ->
  Maybe (SystemState Nat RegistrationTestKey RegistrationTestValue Unit String)
roleChangingApply action before = case checkedApplyAction
  @{registrationTestNameEq} @{registrationTestKeyEq} action before of
    Nothing => Nothing
    Just (tag, afterState) => Just afterState

||| The round-5 counterexample trace is retained as an executable positive
||| regression. Raw name 1 is born as a yielded child, retired and removed,
||| then legally born again as a live external root.
public export
roleChangingRun : Maybe
  (SystemState Nat RegistrationTestKey RegistrationTestValue Unit String)
roleChangingRun = do
  s1 <- roleChangingApply (OInsert 0 Root registrationTestParent)
    registrationTestInitial
  s2 <- roleChangingApply (LBegin 0) s1
  s3 <- roleChangingApply
    (OInsert 1 (ChildOf 0) registrationTestChild) s2
  s4 <- roleChangingApply (ORetire 1) s3
  s5 <- roleChangingApply (ORemove 1) s4
  s6 <- roleChangingApply (OInsert 1 Root registrationTestChild) s5
  s7 <- roleChangingApply (LAdvance 0) s6
  s8 <- roleChangingApply (LBegin 1) s7
  roleChangingApply (LAdvance 1) s8

public export
roleChangingRuntimeCheck : Bool
roleChangingRuntimeCheck = case roleChangingRun of
  Nothing => False
  Just finalState =>
    quiet @{registrationTestNameEq} @{registrationTestKeyEq} finalState &&
    noFailedFibers finalState &&
    isSupported @{registrationTestNameEq} @{registrationTestKeyEq} 0 finalState &&
    isSupported @{registrationTestNameEq} @{registrationTestKeyEq} 1 finalState &&
    case lookupFiber @{registrationTestNameEq} 1 (registry finalState) of
      Nothing => False
      Just fiber => case fiberParent fiber of
        Root => True
        ChildOf parent => False

||| Proof-indexed form of the same nine checked transitions. It is assembled by
||| `fire`, so every stored edge is accepted by the checked evaluator.
public export
record RoleChangingCheckedTrace where
  constructor MkRoleChangingCheckedTrace
  roleChangingFinal : SystemState Nat RegistrationTestKey RegistrationTestValue
    Unit String
  roleChangingTrace : Transitions
    DGamma.CP3StatementChecks.registrationTestInitial roleChangingFinal

public export
roleChangingCheckedTrace : Maybe RoleChangingCheckedTrace
roleChangingCheckedTrace = do
  r1 <- fire registrationTestNameEq registrationTestKeyEq
    (OInsert 0 Root registrationTestParent) registrationTestInitial
  r2 <- fire registrationTestNameEq registrationTestKeyEq (LBegin 0)
    (transitionAfter r1)
  r3 <- fire registrationTestNameEq registrationTestKeyEq
    (OInsert 1 (ChildOf 0) registrationTestChild) (transitionAfter r2)
  r4 <- fire registrationTestNameEq registrationTestKeyEq (ORetire 1)
    (transitionAfter r3)
  r5 <- fire registrationTestNameEq registrationTestKeyEq (ORemove 1)
    (transitionAfter r4)
  r6 <- fire registrationTestNameEq registrationTestKeyEq
    (OInsert 1 Root registrationTestChild) (transitionAfter r5)
  r7 <- fire registrationTestNameEq registrationTestKeyEq (LAdvance 0)
    (transitionAfter r6)
  r8 <- fire registrationTestNameEq registrationTestKeyEq (LBegin 1)
    (transitionAfter r7)
  r9 <- fire registrationTestNameEq registrationTestKeyEq (LAdvance 1)
    (transitionAfter r8)
  let trace = MoreTransitions (checkedTransition r1)
        (MoreTransitions (checkedTransition r2)
          (MoreTransitions (checkedTransition r3)
            (MoreTransitions (checkedTransition r4)
              (MoreTransitions (checkedTransition r5)
                (MoreTransitions (checkedTransition r6)
                  (MoreTransitions (checkedTransition r7)
                    (MoreTransitions (checkedTransition r8)
                      (MoreTransitions (checkedTransition r9)
                        NoTransitions))))))))
  Just (MkRoleChangingCheckedTrace (transitionAfter r9) trace)

public export
roleChangingProofTraceCheck : Bool
roleChangingProofTraceCheck = case roleChangingCheckedTrace of
  Nothing => False
  Just checked => True

||| The generation-stamped accounting branch is constructively available for
||| every located child birth while the same raw name remains outside the raw
||| endpoint-withdrawal list. This is the proposition-shape regression paired
||| with `roleChangingRuntimeCheck`.
public export
0 roleChangingGenerationAccountingGuard :
  (occurrence : LocatedGeneratedRegistration child parent component original) ->
  (Elem (registrationGeneration occurrence)
     [registrationGeneration occurrence],
   Not (Elem child []))
roleChangingGenerationAccountingGuard occurrence = (Here, notInRawEmpty)
  where
  notInRawEmpty : Not (Elem child [])
  notInRawEmpty Here impossible
  notInRawEmpty (There later) impossible

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

||| Canonical parent blocks explicitly admit their yielded child O-Insert.
public export
0 canonicalBlockRegistrationGuard :
  (transition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  transitionAction transition =
    OInsert child (ChildOf selected) childComponent ->
  ActorLifecycleOnly selected rest ->
  ActorLifecycleOnly selected (MoreTransitions transition rest)
canonicalBlockRegistrationGuard = ActorYieldedRegistrationStep

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
0 canonicalRootGenerationFreshGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value protocol nameEq keyEq
    trace) ->
  {root : name} -> {component : Component key value world error} ->
  (birth : LocatedActionOccurrence (OInsert root Root component)
    (canonicalTrace schedule)) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} root (registry (actionBeforeState birth)) = Nothing
canonicalRootGenerationFreshGuard schedule =
  rootGenerationFresh (inputPlacement schedule)

public export
0 canonicalRootGenerationPlacementGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value protocol nameEq keyEq
    trace) ->
  {root : name} -> {component : Component key value world error} ->
  (birth : LocatedActionOccurrence (OInsert root Root component)
    (canonicalTrace schedule)) ->
  {action : Action name key value world error} ->
  (lifecycle : LocatedActionOccurrence action (canonicalTrace schedule)) ->
  isLifecycleAction action = True ->
  LT (locatedActionOrdinal birth) (locatedActionOrdinal lifecycle)
canonicalRootGenerationPlacementGuard schedule =
  rootGenerationBeforeLifecycle (inputPlacement schedule)

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
    (endpointWithdrawnGenerations (canonicalEndpoint schedule))
canonicalRegistrationTreeGuard schedule = canonicalRegistrationTree schedule

public export
0 canonicalWithdrawnRegistrationGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value protocol nameEq keyEq
    trace) ->
  (generation : RegistrationGeneration name) ->
  Elem generation (endpointWithdrawnGenerations (canonicalEndpoint schedule)) ->
  (parent : name **
   component : Component key value world error **
   occurrence : LocatedGeneratedRegistration (generationName generation)
     parent component trace **
   (registrationGeneration occurrence = generation,
    (canonicalParent : name) ->
    (canonicalComponent : Component key value world error) ->
    (canonicalOccurrence : LocatedGeneratedRegistration
      (generationName generation) canonicalParent canonicalComponent
      (canonicalTrace schedule)) ->
    registrationGeneration
      (canonicalToOriginal (canonicalRegistrationTree schedule)
        canonicalOccurrence) = generation -> Void))
canonicalWithdrawnRegistrationGuard schedule =
  withdrawnRegistrationRemoved (canonicalRegistrationTree schedule)

||| A withdrawn historical generation need not withdraw the current raw-name
||| endpoint. This is the key role-changing-reissue distinction: a child birth
||| can be deleted while a later root birth of the same raw name stays live.
public export
0 generationWithdrawalIndependentOfRawEndpoint :
  {originalFinal, canonicalFinal : SystemState name key value world error} ->
  {endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal canonicalFinal} ->
  (generation : RegistrationGeneration name) ->
  Elem generation (endpointWithdrawnGenerations endpoint) ->
  Not (Elem (generationName generation) (endpointWithdrawnNames endpoint)) ->
  (Elem generation (endpointWithdrawnGenerations endpoint),
   Not (Elem (generationName generation) (endpointWithdrawnNames endpoint)))
generationWithdrawalIndependentOfRawEndpoint generation withdrawn rawLive =
  (withdrawn, rawLive)

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

||| Lemma-56 guards: the same-input package exports a generation bijection for
||| historical registrations and a separate raw-name bijection for the current
||| endpoint only.
public export
0 orchestrationGenerationRenamingGuard :
  {leftFirst, leftFinal, rightFirst, rightFinal :
    SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} ->
  {right : Transitions rightFirst rightFinal} ->
  (same : SameOrchestrationModuloGenerated nameEq left right) ->
  RegistrationGenerationBijection name
orchestrationGenerationRenamingGuard same = generatedGenerationBijection same

public export
0 orchestrationCurrentRenamingGuard :
  {leftFirst, leftFinal, rightFirst, rightFinal :
    SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} ->
  {right : Transitions rightFirst rightFinal} ->
  (same : SameOrchestrationModuloGenerated nameEq left right) ->
  NameBijection name
orchestrationCurrentRenamingGuard same =
  currentNameBijection (endpointRenaming same)

public export
0 registrationGenerationGuard :
  (same : SameOrchestrationModuloGenerated nameEq left right) ->
  RegistrationCorrespondenceByGeneration nameEq
    (generatedGenerationBijection same) left right
registrationGenerationGuard same = generatedRegistrationTree same

public export
0 registrationMultiplicityGuard :
  (same : SameOrchestrationModuloGenerated nameEq left right) ->
  RegistrationTraceCorrespondence nameEq (generatedGenerationBijection same)
    0 [] left (leftFinalGenerations (generatedRegistrationTree same))
    0 [] right (rightFinalGenerations (generatedRegistrationTree same))
registrationMultiplicityGuard same =
  generationTraceCorrespondence (generatedRegistrationTree same)

public export
0 confluenceRenamedEndpointGuard :
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {left : Transitions initial leftFinal} ->
  {right : Transitions initial rightFinal} ->
  (result : ConfluenceResult name key world error value protocol nameEq keyEq
    left right generationRenaming currentRenaming) ->
  SystemEquivalentByRenaming name key world error value nameEq keyEq
    currentRenaming leftFinal rightFinal
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

||| Positive guard for the paper-permitted already-removed R endpoint case.
public export
0 alreadyAbsentWithdrawalGuard :
  {originalFinal, survivingState : SystemState name key value world error} ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} child (registry originalFinal) = Nothing ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} child (registry survivingState) = Nothing ->
  WithdrawnNameResult nameEq child originalFinal survivingState
alreadyAbsentWithdrawalGuard = NameAlreadyAbsent

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

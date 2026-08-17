module DGamma.CP3StatementChecks

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4SupportSolution
import DGamma.CalculusChecks
import DGamma.Section3Example
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

||| Executable six-action canonical replay for the nine-action role-changing
||| history: both external roots are inserted before either lifecycle block and
||| the withdrawn historical child birth is absent.
public export
roleChangingCanonicalRun : Maybe
  (SystemState Nat RegistrationTestKey RegistrationTestValue Unit String)
roleChangingCanonicalRun = do
  s1 <- roleChangingApply (OInsert 0 Root registrationTestParent)
    registrationTestInitial
  s2 <- roleChangingApply (OInsert 1 Root registrationTestChild) s1
  s3 <- roleChangingApply (LBegin 0) s2
  s4 <- roleChangingApply (LAdvance 0) s3
  s5 <- roleChangingApply (LBegin 1) s4
  roleChangingApply (LAdvance 1) s5

public export
roleChangingCanonicalRuntimeCheck : Bool
roleChangingCanonicalRuntimeCheck = case (roleChangingRun, roleChangingCanonicalRun) of
  (Just originalFinal, Just canonicalFinal) =>
    quiet @{registrationTestNameEq} @{registrationTestKeyEq} canonicalFinal &&
    noFailedFibers canonicalFinal &&
    isSupported @{registrationTestNameEq} @{registrationTestKeyEq} 0 canonicalFinal &&
    isSupported @{registrationTestNameEq} @{registrationTestKeyEq} 1 canonicalFinal &&
    case (lookupFiber @{registrationTestNameEq} 1 (registry originalFinal),
          lookupFiber @{registrationTestNameEq} 1 (registry canonicalFinal)) of
      (Just originalFiber, Just canonicalFiber) =>
        case (fiberParent originalFiber, fiberParent canonicalFiber) of
          (Root, Root) => isActive (fiberLifecycle originalFiber) &&
            isActive (fiberLifecycle canonicalFiber)
          _ => False
      _ => False
  _ => False

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

||| A checked transition retaining the requested action in its type.  `fire`
||| intentionally hides that equality in `TransitionResult`; the registration-
||| generation regressions below need it to assemble structural trace evidence.
public export
record CheckedNamedTransition
  (nameEq : DecEq name) (keyEq : DecEq key)
  (action : Action name key value world error)
  (before : SystemState name key value world error) where
  constructor MkCheckedNamedTransition
  namedAfter : SystemState name key value world error
  namedRule : RuleTag
  0 namedChecked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (namedRule, namedAfter)
  namedTransition : Transition before namedAfter
  0 namedAction : transitionAction namedTransition = action

public export
checkedNamedFire : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (before : SystemState name key value world error) ->
  Maybe (CheckedNamedTransition nameEq keyEq action before)
checkedNamedFire nameEq keyEq action before
  with (checkedApplyAction @{nameEq} @{keyEq} action before) proof fired
    checkedNamedFire nameEq keyEq action before | Nothing = Nothing
    checkedNamedFire nameEq keyEq action before | Just (tag, afterState) =
      Just (MkCheckedNamedTransition afterState tag fired
        (Fired nameEq keyEq action tag fired) Refl)

0 namedTransitionNotUnload :
  (step : CheckedNamedTransition nameEq keyEq action before) ->
  (action = LUnload parent -> Void) ->
  transitionAction (namedTransition step) = LUnload parent -> Void
namedTransitionNotUnload step actionNotUnload observed =
  actionNotUnload (trans (sym (namedAction step)) observed)

swapFreshRaw : Nat -> Nat
swapFreshRaw (S Z) = S (S Z)
swapFreshRaw (S (S Z)) = S Z
swapFreshRaw n = n

0 swapFreshRawInvolutive : (n : Nat) -> swapFreshRaw (swapFreshRaw n) = n
swapFreshRawInvolutive Z = Refl
swapFreshRawInvolutive (S Z) = Refl
swapFreshRawInvolutive (S (S Z)) = Refl
swapFreshRawInvolutive (S (S (S later))) = Refl

swapFreshGeneration : RegistrationGeneration Nat -> RegistrationGeneration Nat
swapFreshGeneration (MkRegistrationGeneration name (S (S Z))) =
  MkRegistrationGeneration (swapFreshRaw name) (S (S Z))
swapFreshGeneration generation = generation

0 swapFreshGenerationInvolutive : (generation : RegistrationGeneration Nat) ->
  swapFreshGeneration (swapFreshGeneration generation) = generation
swapFreshGenerationInvolutive (MkRegistrationGeneration name Z) = Refl
swapFreshGenerationInvolutive (MkRegistrationGeneration name (S Z)) = Refl
swapFreshGenerationInvolutive
  (MkRegistrationGeneration name (S (S Z))) =
    cong (\mapped => MkRegistrationGeneration mapped (S (S Z)))
      (swapFreshRawInvolutive name)
swapFreshGenerationInvolutive
  (MkRegistrationGeneration name (S (S (S later)))) = Refl

||| The generation bijection for the reviewer's pair swaps only the historical
||| birth-at-ordinal-2 generations `(1,2)` and `(2,2)`.  In particular the
||| later live root generation `(1,5)` remains fixed.
public export
freshChoiceGenerationBijection : RegistrationGenerationBijection Nat
freshChoiceGenerationBijection = MkRegistrationGenerationBijection
  swapFreshGeneration swapFreshGeneration swapFreshGenerationInvolutive
  swapFreshGenerationInvolutive

swapHistoricalRootGeneration : RegistrationGeneration Nat ->
  RegistrationGeneration Nat
swapHistoricalRootGeneration (MkRegistrationGeneration 0 0) =
  MkRegistrationGeneration 1 3
swapHistoricalRootGeneration (MkRegistrationGeneration 1 3) =
  MkRegistrationGeneration 0 0
swapHistoricalRootGeneration generation = generation

0 swapHistoricalRootGenerationInvolutive :
  (generation : RegistrationGeneration Nat) ->
  swapHistoricalRootGeneration (swapHistoricalRootGeneration generation) = generation
swapHistoricalRootGenerationInvolutive (MkRegistrationGeneration Z Z) = Refl
swapHistoricalRootGenerationInvolutive
  (MkRegistrationGeneration Z (S ordinal)) = Refl
swapHistoricalRootGenerationInvolutive
  (MkRegistrationGeneration (S Z) Z) = Refl
swapHistoricalRootGenerationInvolutive
  (MkRegistrationGeneration (S Z) (S Z)) = Refl
swapHistoricalRootGenerationInvolutive
  (MkRegistrationGeneration (S Z) (S (S Z))) = Refl
swapHistoricalRootGenerationInvolutive
  (MkRegistrationGeneration (S Z) (S (S (S Z)))) = Refl
swapHistoricalRootGenerationInvolutive
  (MkRegistrationGeneration (S Z) (S (S (S (S ordinal))))) = Refl
swapHistoricalRootGenerationInvolutive
  (MkRegistrationGeneration (S (S name)) ordinal) = Refl

public export
historicalRootPermutationBijection : RegistrationGenerationBijection Nat
historicalRootPermutationBijection = MkRegistrationGenerationBijection
  swapHistoricalRootGeneration swapHistoricalRootGeneration
  swapHistoricalRootGenerationInvolutive
  swapHistoricalRootGenerationInvolutive

||| Concrete removed-root history used by the round-8 negative guard.  Both
||| external roots are gone at the endpoint, so current-name constraints cannot
||| mask historical generation reassignment.
record RemovedRootTrace where
  constructor MkRemovedRootTrace
  removedInsert0 : CheckedNamedTransition DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (OInsert 0 Root DGamma.CP3StatementChecks.registrationTestChild)
    DGamma.CP3StatementChecks.registrationTestInitial
  removedRetire0 : CheckedNamedTransition DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (ORetire 0) (namedAfter removedInsert0)
  removedRemove0 : CheckedNamedTransition DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (ORemove 0) (namedAfter removedRetire0)
  removedInsert1 : CheckedNamedTransition DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (OInsert 1 Root DGamma.CP3StatementChecks.registrationTestChild)
    (namedAfter removedRemove0)
  removedRetire1 : CheckedNamedTransition DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (ORetire 1) (namedAfter removedInsert1)
  removedRemove1 : CheckedNamedTransition DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (ORemove 1) (namedAfter removedRetire1)

removedRootTrace : (trace : RemovedRootTrace) ->
  Transitions DGamma.CP3StatementChecks.registrationTestInitial (namedAfter (removedRemove1 trace))
removedRootTrace trace =
  MoreTransitions (namedTransition (removedInsert0 trace))
  (MoreTransitions (namedTransition (removedRetire0 trace))
  (MoreTransitions (namedTransition (removedRemove0 trace))
  (MoreTransitions (namedTransition (removedInsert1 trace))
  (MoreTransitions (namedTransition (removedRetire1 trace))
  (MoreTransitions (namedTransition (removedRemove1 trace))
    NoTransitions)))))

removedRootTail1 : (trace : RemovedRootTrace) ->
  Transitions (namedAfter (removedInsert0 trace))
    (namedAfter (removedRemove1 trace))
removedRootTail1 trace =
  MoreTransitions (namedTransition (removedRetire0 trace))
  (MoreTransitions (namedTransition (removedRemove0 trace))
  (MoreTransitions (namedTransition (removedInsert1 trace))
  (MoreTransitions (namedTransition (removedRetire1 trace))
  (MoreTransitions (namedTransition (removedRemove1 trace)) NoTransitions))))

buildRemovedRootTrace : Maybe RemovedRootTrace
buildRemovedRootTrace = do
  t0 <- checkedNamedFire DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq
    (OInsert 0 Root DGamma.CP3StatementChecks.registrationTestChild) DGamma.CP3StatementChecks.registrationTestInitial
  t1 <- checkedNamedFire DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq
    (ORetire 0) (namedAfter t0)
  t2 <- checkedNamedFire DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq
    (ORemove 0) (namedAfter t1)
  t3 <- checkedNamedFire DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq
    (OInsert 1 Root DGamma.CP3StatementChecks.registrationTestChild) (namedAfter t2)
  t4 <- checkedNamedFire DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq
    (ORetire 1) (namedAfter t3)
  t5 <- checkedNamedFire DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq
    (ORemove 1) (namedAfter t4)
  Just (MkRemovedRootTrace t0 t1 t2 t3 t4 t5)

public export
removedRootRuntimeCheck : Bool
removedRootRuntimeCheck = case buildRemovedRootTrace of
  Nothing => False
  Just trace => null (bindings (registry (namedAfter (removedRemove1 trace))))

0 historicalFirstRootMoved :
  generationForward DGamma.CP3StatementChecks.historicalRootPermutationBijection
    (MkRegistrationGeneration 0 0) = MkRegistrationGeneration 0 0 -> Void
historicalFirstRootMoved Refl impossible

||| An alleged complete public same-input package for the concrete history,
||| together with the forbidden permutation `(0,0) <-> (1,3)`.  This record is
||| deliberately uninhabited; unlike the old guard it contains every conjunct
||| of `SameOrchestrationModuloGenerated`, not only root coupling.
public export
record CompleteRemovedRootPermutationCandidate where
  constructor MkCompleteRemovedRootPermutationCandidate
  removedRootHistory : RemovedRootTrace
  0 removedRootFullRelation : SameOrchestrationModuloGenerated
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq
    (removedRootTrace removedRootHistory) (removedRootTrace removedRootHistory)
  0 removedRootUsesPermutation : generatedGenerationBijection
    removedRootFullRelation =
    DGamma.CP3StatementChecks.historicalRootPermutationBijection

||| Full-relation rejection: the exact first external input must map `(0,0)` to
||| itself, while the candidate's complete generation renaming maps it to
||| `(1,3)`.  Empty endpoints play no role in the contradiction.
public export
0 historicalExternalRootPermutationRejected :
  CompleteRemovedRootPermutationCandidate -> Void
historicalExternalRootPermutationRejected candidate =
  let generation : RegistrationGeneration Nat
      generation = MkRegistrationGeneration 0 0
      mapped : generationForward
        (generatedGenerationBijection (removedRootFullRelation candidate))
        generation = generation
      mapped = firstExternalRootBirthMapped
        (externalRootGenerationsCoupled (removedRootFullRelation candidate))
        (namedAction (removedInsert0 (removedRootHistory candidate)))
        (namedAction (removedInsert0 (removedRootHistory candidate)))
      renamed = cong (\renaming => generationForward renaming generation)
        (removedRootUsesPermutation candidate) in
    historicalFirstRootMoved (trans (sym renamed) mapped)

0 namedInsertLookup :
  (step : CheckedNamedTransition nameEq keyEq
    (OInsert child parent component) before) ->
  lookupFiber @{nameEq} child (registry (namedAfter step)) =
    Just (freshFiber component parent)
namedInsertLookup {nameEq} {keyEq} {child} {parent} {component} {before} step =
  oInsertResultLookup nameEq keyEq child parent component before
    (namedAfter step) (namedRule step)
    (checkedActionProjects nameEq keyEq (OInsert child parent component) before
      (namedAfter step) (namedRule step) (namedChecked step))

0 namedRetireLookup :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before : SystemState name key value world error} ->
  {child : name} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (fiber : Fiber name key value world error) ->
  (found : lookupFiber @{nameEq} child (registry before) = Just fiber) ->
  (step : CheckedNamedTransition nameEq keyEq (ORetire child) before) ->
  (afterFiber : Fiber name key value world error **
   (lookupFiber @{nameEq} child (registry (namedAfter step)) = Just afterFiber,
    fiberParent afterFiber = fiberParent fiber))
namedRetireLookup {child} {before} nameEq keyEq fiber found step =
  oRetireResultLookup nameEq keyEq child fiber before (namedAfter step)
    (namedRule step) found
    (checkedActionProjects nameEq keyEq (ORetire child) before
      (namedAfter step) (namedRule step) (namedChecked step))

public export
0 lifecycleCannotBeRoot :
  (transition : Transition before afterState) ->
  isLifecycleAction (transitionAction transition) = True ->
  RootOrchestrationStep nameEq transition -> Void
lifecycleCannotBeRoot transition lifecycle (RootInsertStep action) =
  case trans (sym (cong isLifecycleAction action)) lifecycle of Refl impossible
lifecycleCannotBeRoot transition lifecycle
  (RootRetireStep fiber found parent action) =
    case trans (sym (cong isLifecycleAction action)) lifecycle of Refl impossible
lifecycleCannotBeRoot transition lifecycle
  (RootRemoveStep fiber found parent action) =
    case trans (sym (cong isLifecycleAction action)) lifecycle of Refl impossible

public export
0 childInsertCannotBeRoot :
  (transition : Transition before afterState) ->
  transitionAction transition = OInsert child (ChildOf parent) component ->
  RootOrchestrationStep nameEq transition -> Void
childInsertCannotBeRoot transition childAction (RootInsertStep rootAction) =
  case trans (sym childAction) rootAction of Refl impossible
childInsertCannotBeRoot transition childAction
  (RootRetireStep fiber found parent rootAction) =
    case trans (sym childAction) rootAction of Refl impossible
childInsertCannotBeRoot transition childAction
  (RootRemoveStep fiber found parent rootAction) =
    case trans (sym childAction) rootAction of Refl impossible

public export
0 childRetireCannotBeRoot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  {child, parent : name} ->
  (nameEq : DecEq name) ->
  (transition : Transition before afterState) ->
  transitionAction transition = ORetire child ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} child (registry before) = Just fiber ->
  fiberParent fiber = ChildOf parent ->
  RootOrchestrationStep nameEq transition -> Void
childRetireCannotBeRoot nameEq transition childAction fiber childFound childParent
  (RootInsertStep rootAction) =
    case trans (sym childAction) rootAction of Refl impossible
childRetireCannotBeRoot nameEq transition childAction fiber childFound childParent
  (RootRetireStep rootFiber rootFound rootParent rootAction) =
    case trans (sym childAction) rootAction of
      Refl =>
        let sameFiber = justInjective (trans (sym childFound) rootFound)
            roleConflict : (ChildOf parent = Root)
            roleConflict = trans (sym childParent)
              (trans (cong fiberParent sameFiber) rootParent) in
          case roleConflict of Refl impossible
childRetireCannotBeRoot nameEq transition childAction fiber childFound childParent
  (RootRemoveStep rootFiber rootFound rootParent rootAction) =
    case trans (sym childAction) rootAction of Refl impossible

0 childRemoveCannotBeRoot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  {child, parent : name} ->
  (nameEq : DecEq name) ->
  (transition : Transition before afterState) ->
  transitionAction transition = ORemove child ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} child (registry before) = Just fiber ->
  fiberParent fiber = ChildOf parent ->
  RootOrchestrationStep nameEq transition -> Void
childRemoveCannotBeRoot nameEq transition childAction fiber childFound childParent
  (RootInsertStep rootAction) =
    case trans (sym childAction) rootAction of Refl impossible
childRemoveCannotBeRoot nameEq transition childAction fiber childFound childParent
  (RootRetireStep rootFiber rootFound rootParent rootAction) =
    case trans (sym childAction) rootAction of Refl impossible
childRemoveCannotBeRoot nameEq transition childAction fiber childFound childParent
  (RootRemoveStep rootFiber rootFound rootParent rootAction) =
    case trans (sym childAction) rootAction of
      Refl =>
        let sameFiber = justInjective (trans (sym childFound) rootFound)
            roleConflict : (ChildOf parent = Root)
            roleConflict = trans (sym childParent)
              (trans (cong fiberParent sameFiber) rootParent) in
          case roleConflict of Refl impossible

record RoleChangingNamedTrace (generatedChild : Nat) where
  constructor MkRoleChangingNamedTrace
  rootInsert0 : CheckedNamedTransition DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (OInsert 0 Root DGamma.CP3StatementChecks.registrationTestParent)
    DGamma.CP3StatementChecks.registrationTestInitial
  parentBegin : CheckedNamedTransition DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (LBegin 0) (namedAfter rootInsert0)
  childInsert : CheckedNamedTransition DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq
    (OInsert generatedChild (ChildOf 0) DGamma.CP3StatementChecks.registrationTestChild)
    (namedAfter parentBegin)
  childRetire : CheckedNamedTransition DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (ORetire generatedChild) (namedAfter childInsert)
  childRemove : CheckedNamedTransition DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (ORemove generatedChild) (namedAfter childRetire)
  rootInsert1 : CheckedNamedTransition DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (OInsert 1 Root DGamma.CP3StatementChecks.registrationTestChild)
    (namedAfter childRemove)
  parentAdvance : CheckedNamedTransition DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (LAdvance 0) (namedAfter rootInsert1)
  rootBegin1 : CheckedNamedTransition DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (LBegin 1) (namedAfter parentAdvance)
  rootAdvance1 : CheckedNamedTransition DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (LAdvance 1) (namedAfter rootBegin1)

namedRoleChangingTrace : (evidence : RoleChangingNamedTrace generatedChild) ->
  Transitions DGamma.CP3StatementChecks.registrationTestInitial (namedAfter (rootAdvance1 evidence))
namedRoleChangingTrace evidence =
  MoreTransitions (namedTransition (rootInsert0 evidence))
    (MoreTransitions (namedTransition (parentBegin evidence))
      (MoreTransitions (namedTransition (childInsert evidence))
        (MoreTransitions (namedTransition (childRetire evidence))
          (MoreTransitions (namedTransition (childRemove evidence))
            (MoreTransitions (namedTransition (rootInsert1 evidence))
              (MoreTransitions (namedTransition (parentAdvance evidence))
                (MoreTransitions (namedTransition (rootBegin1 evidence))
                  (MoreTransitions (namedTransition (rootAdvance1 evidence))
                    NoTransitions))))))))

namedRoleTail9 : (evidence : RoleChangingNamedTrace generatedChild) ->
  Transitions (namedAfter (rootBegin1 evidence))
    (namedAfter (rootAdvance1 evidence))
namedRoleTail9 evidence = MoreTransitions
  (namedTransition (rootAdvance1 evidence)) NoTransitions

namedRoleTail8 : (evidence : RoleChangingNamedTrace generatedChild) ->
  Transitions (namedAfter (parentAdvance evidence))
    (namedAfter (rootAdvance1 evidence))
namedRoleTail8 evidence = MoreTransitions (namedTransition (rootBegin1 evidence))
  (namedRoleTail9 evidence)

namedRoleTail7 : (evidence : RoleChangingNamedTrace generatedChild) ->
  Transitions (namedAfter (rootInsert1 evidence))
    (namedAfter (rootAdvance1 evidence))
namedRoleTail7 evidence = MoreTransitions
  (namedTransition (parentAdvance evidence)) (namedRoleTail8 evidence)

namedRoleTail6 : (evidence : RoleChangingNamedTrace generatedChild) ->
  Transitions (namedAfter (childRemove evidence))
    (namedAfter (rootAdvance1 evidence))
namedRoleTail6 evidence = MoreTransitions (namedTransition (rootInsert1 evidence))
  (namedRoleTail7 evidence)

namedRoleTail5 : (evidence : RoleChangingNamedTrace generatedChild) ->
  Transitions (namedAfter (childRetire evidence))
    (namedAfter (rootAdvance1 evidence))
namedRoleTail5 evidence = MoreTransitions (namedTransition (childRemove evidence))
  (namedRoleTail6 evidence)

namedRoleTail4 : (evidence : RoleChangingNamedTrace generatedChild) ->
  Transitions (namedAfter (childInsert evidence))
    (namedAfter (rootAdvance1 evidence))
namedRoleTail4 evidence = MoreTransitions (namedTransition (childRetire evidence))
  (namedRoleTail5 evidence)

namedRoleTail3 : (evidence : RoleChangingNamedTrace generatedChild) ->
  Transitions (namedAfter (parentBegin evidence))
    (namedAfter (rootAdvance1 evidence))
namedRoleTail3 evidence = MoreTransitions (namedTransition (childInsert evidence))
  (namedRoleTail4 evidence)

namedRoleTail2 : (evidence : RoleChangingNamedTrace generatedChild) ->
  Transitions (namedAfter (rootInsert0 evidence))
    (namedAfter (rootAdvance1 evidence))
namedRoleTail2 evidence = MoreTransitions (namedTransition (parentBegin evidence))
  (namedRoleTail3 evidence)

registrationTestAdvance : Nat ->
  Action Nat RegistrationTestKey RegistrationTestValue Unit String ->
  RegistrationIndexState Nat -> RegistrationIndexState Nat
registrationTestAdvance = DGamma.CP3.advanceRegistrationIndex
  @{DGamma.CP3StatementChecks.registrationTestNameEq}

registrationTestAdvanceSurviving : Nat -> (child, parent : Nat) ->
  Component RegistrationTestKey RegistrationTestValue Unit String ->
  RegistrationIndexState Nat -> RegistrationIndexState Nat
registrationTestAdvanceSurviving = DGamma.CP3.advanceSurvivingRegistrationIndex
  @{DGamma.CP3StatementChecks.registrationTestNameEq}

freshChoiceFinalGenerations : GenerationEnvironment Nat
freshChoiceFinalGenerations =
  [(0, MkRegistrationGeneration 0 0),
   (1, MkRegistrationGeneration 1 5)]

freshChoiceParentIndex : RegistrationIndexState Nat
freshChoiceParentIndex = registrationTestAdvance 1 (LBegin 0)
  (registrationTestAdvance 0
    (OInsert 0 Root registrationTestParent) DGamma.CP3.emptyRegistrationIndex)

freshChoiceLeftFinalIndex : RegistrationIndexState Nat
freshChoiceLeftFinalIndex =
  let afterChild = registrationTestAdvanceSurviving 2
        1 0 registrationTestChild freshChoiceParentIndex
      afterRetire = registrationTestAdvance 3 (ORetire 1) afterChild
      afterRemove = registrationTestAdvance 4 (ORemove 1) afterRetire
      afterRoot = registrationTestAdvance 5
        (OInsert 1 Root registrationTestChild) afterRemove
      afterParent = registrationTestAdvance 6 (LAdvance 0) afterRoot
      afterBegin = registrationTestAdvance 7 (LBegin 1) afterParent in
    registrationTestAdvance 8 (LAdvance 1) afterBegin

freshChoiceRightFinalIndex : RegistrationIndexState Nat
freshChoiceRightFinalIndex =
  let afterChild = registrationTestAdvanceSurviving 2
        2 0 registrationTestChild freshChoiceParentIndex
      afterRetire = registrationTestAdvance 3 (ORetire 2) afterChild
      afterRemove = registrationTestAdvance 4 (ORemove 2) afterRetire
      afterRoot = registrationTestAdvance 5
        (OInsert 1 Root registrationTestChild) afterRemove
      afterParent = registrationTestAdvance 6 (LAdvance 0) afterRoot
      afterBegin = registrationTestAdvance 7 (LBegin 1) afterParent in
    registrationTestAdvance 8 (LAdvance 1) afterBegin

0 freshChoiceParentSurvives :
  (evidence : RoleChangingNamedTrace generatedChild) ->
  NoParentUnload 0 (namedRoleTail4 evidence)
freshChoiceParentSurvives evidence =
  NoParentUnloadStep (namedTransition (childRetire evidence))
    (namedRoleTail5 evidence)
    (namedTransitionNotUnload (childRetire evidence) (\Refl impossible))
  (NoParentUnloadStep (namedTransition (childRemove evidence))
    (namedRoleTail6 evidence)
    (namedTransitionNotUnload (childRemove evidence) (\Refl impossible))
  (NoParentUnloadStep (namedTransition (rootInsert1 evidence))
    (namedRoleTail7 evidence)
    (namedTransitionNotUnload (rootInsert1 evidence) (\Refl impossible))
  (NoParentUnloadStep (namedTransition (parentAdvance evidence))
    (namedRoleTail8 evidence)
    (namedTransitionNotUnload (parentAdvance evidence) (\Refl impossible))
  (NoParentUnloadStep (namedTransition (rootBegin1 evidence))
    (namedRoleTail9 evidence)
    (namedTransitionNotUnload (rootBegin1 evidence) (\Refl impossible))
  (NoParentUnloadStep (namedTransition (rootAdvance1 evidence))
    NoTransitions
    (namedTransitionNotUnload (rootAdvance1 evidence) (\Refl impossible))
    NoParentUnloadEnd)))))

0 freshChoiceSurvivingRegistration :
  (evidence : RoleChangingNamedTrace generatedChild) ->
  SurvivingRegistration
    (registrationEventAt @{DGamma.CP3StatementChecks.registrationTestNameEq}
      2 DGamma.CP3StatementChecks.freshChoiceParentIndex generatedChild 0
      DGamma.CP3StatementChecks.registrationTestChild)
    (namedRoleTail4 evidence)
freshChoiceSurvivingRegistration evidence = MkSurvivingRegistration
  (MkRegistrationActivation (MkRegistrationGeneration 0 0) 1) Refl
  (freshChoiceParentSurvives evidence)

0 freshChoiceGenerationTraceCorrespondence :
  (left : RoleChangingNamedTrace 1) ->
  (right : RoleChangingNamedTrace 2) ->
  RegistrationTraceCorrespondence
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.freshChoiceGenerationBijection
    0 DGamma.CP3.emptyRegistrationIndex (namedRoleChangingTrace left)
    DGamma.CP3StatementChecks.freshChoiceLeftFinalIndex
    0 DGamma.CP3.emptyRegistrationIndex (namedRoleChangingTrace right)
    DGamma.CP3StatementChecks.freshChoiceRightFinalIndex [] []
freshChoiceGenerationTraceCorrespondence left right =
  SkipLeftNonRegistration (OInsert 0 Root registrationTestParent)
    (namedTransition (rootInsert0 left)) (namedRoleTail2 left)
    (namedAction (rootInsert0 left)) Refl
  (SkipLeftNonRegistration (LBegin 0)
    (namedTransition (parentBegin left)) (namedRoleTail3 left)
    (namedAction (parentBegin left)) Refl
  (QueueLeftGeneratedRegistration
    (namedTransition (childInsert left)) (namedRoleTail4 left)
    (namedAction (childInsert left)) (freshChoiceSurvivingRegistration left)
  (SkipLeftNonRegistration (ORetire 1)
    (namedTransition (childRetire left)) (namedRoleTail5 left)
    (namedAction (childRetire left)) Refl
  (SkipLeftNonRegistration (ORemove 1)
    (namedTransition (childRemove left)) (namedRoleTail6 left)
    (namedAction (childRemove left)) Refl
  (SkipLeftNonRegistration (OInsert 1 Root registrationTestChild)
    (namedTransition (rootInsert1 left)) (namedRoleTail7 left)
    (namedAction (rootInsert1 left)) Refl
  (SkipLeftNonRegistration (LAdvance 0)
    (namedTransition (parentAdvance left)) (namedRoleTail8 left)
    (namedAction (parentAdvance left)) Refl
  (SkipLeftNonRegistration (LBegin 1)
    (namedTransition (rootBegin1 left)) (namedRoleTail9 left)
    (namedAction (rootBegin1 left)) Refl
  (SkipLeftNonRegistration (LAdvance 1)
    (namedTransition (rootAdvance1 left)) NoTransitions
    (namedAction (rootAdvance1 left)) Refl
  (SkipRightNonRegistration (OInsert 0 Root registrationTestParent)
    (namedTransition (rootInsert0 right)) (namedRoleTail2 right)
    (namedAction (rootInsert0 right)) Refl
  (SkipRightNonRegistration (LBegin 0)
    (namedTransition (parentBegin right)) (namedRoleTail3 right)
    (namedAction (parentBegin right)) Refl
  (MatchRightWithPendingLeft
    (namedTransition (childInsert right)) (namedRoleTail4 right)
    (namedAction (childInsert right)) (freshChoiceSurvivingRegistration right) []
    (registrationEventAt @{DGamma.CP3StatementChecks.registrationTestNameEq}
      2 DGamma.CP3StatementChecks.freshChoiceParentIndex 1 0 registrationTestChild)
    []
    (MkRegistrationEventMatch Refl
      (MkRegistrationActivation (MkRegistrationGeneration 0 0) 1)
      (MkRegistrationActivation (MkRegistrationGeneration 0 0) 1)
      Refl Refl Refl Refl Refl)
  (SkipRightNonRegistration (ORetire 2)
    (namedTransition (childRetire right)) (namedRoleTail5 right)
    (namedAction (childRetire right)) Refl
  (SkipRightNonRegistration (ORemove 2)
    (namedTransition (childRemove right)) (namedRoleTail6 right)
    (namedAction (childRemove right)) Refl
  (SkipRightNonRegistration (OInsert 1 Root registrationTestChild)
    (namedTransition (rootInsert1 right)) (namedRoleTail7 right)
    (namedAction (rootInsert1 right)) Refl
  (SkipRightNonRegistration (LAdvance 0)
    (namedTransition (parentAdvance right)) (namedRoleTail8 right)
    (namedAction (parentAdvance right)) Refl
  (SkipRightNonRegistration (LBegin 1)
    (namedTransition (rootBegin1 right)) (namedRoleTail9 right)
    (namedAction (rootBegin1 right)) Refl
  (SkipRightNonRegistration (LAdvance 1)
    (namedTransition (rootAdvance1 right)) NoTransitions
    (namedAction (rootAdvance1 right)) Refl
    RegistrationCorrespondenceEnd)))))))))))))))))

0 freshChoiceRegistrationCorrespondence :
  (left : RoleChangingNamedTrace 1) ->
  (right : RoleChangingNamedTrace 2) ->
  RegistrationCorrespondenceByGeneration DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.freshChoiceGenerationBijection (namedRoleChangingTrace left)
    (namedRoleChangingTrace right)
freshChoiceRegistrationCorrespondence left right =
  MkRegistrationCorrespondenceByGeneration
    freshChoiceLeftFinalIndex freshChoiceRightFinalIndex
    (freshChoiceGenerationTraceCorrespondence left right)

0 freshChoiceCurrentGenerationForward : (n : Nat) ->
  (generation : RegistrationGeneration Nat) ->
  lookupCurrentGeneration @{DGamma.CP3StatementChecks.registrationTestNameEq} n DGamma.CP3StatementChecks.freshChoiceFinalGenerations = Just generation ->
  (rightGeneration : RegistrationGeneration Nat **
   (generationForward DGamma.CP3StatementChecks.freshChoiceGenerationBijection generation = rightGeneration,
    lookupCurrentGeneration @{DGamma.CP3StatementChecks.registrationTestNameEq} n DGamma.CP3StatementChecks.freshChoiceFinalGenerations = Just rightGeneration))
freshChoiceCurrentGenerationForward Z generation found =
  case justInjective found of
    Refl => ((MkRegistrationGeneration 0 0) ** (Refl, Refl))
freshChoiceCurrentGenerationForward (S Z) generation found =
  case justInjective found of
    Refl => ((MkRegistrationGeneration 1 5) ** (Refl, Refl))
freshChoiceCurrentGenerationForward (S (S later)) generation found =
  void (nothingIsNotJust found)

0 freshChoiceCurrentEndpointRenaming :
  (left : RoleChangingNamedTrace 1) ->
  (right : RoleChangingNamedTrace 2) ->
  CurrentEndpointRenaming DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq
    DGamma.CP3StatementChecks.freshChoiceGenerationBijection
    (namedRoleChangingTrace left) (namedRoleChangingTrace right)
    (freshChoiceRegistrationCorrespondence left right)
freshChoiceCurrentEndpointRenaming left right =
  MkCurrentEndpointRenaming identityNameBijection
    (\n, fiber, found, root => Refl)
    (\n, fiber, found, root => Refl)
    (\n, generation, found =>
      Right (freshChoiceCurrentGenerationForward n generation found))
    (\n, generation, found =>
      Right (freshChoiceCurrentGenerationForward n generation found))

record RoleChildRetiredEvidence
  (generatedChild : Nat) (evidence : RoleChangingNamedTrace generatedChild) where
  constructor MkRoleChildRetiredEvidence
  retiredChildFiber : Fiber Nat RegistrationTestKey RegistrationTestValue Unit String
  0 retiredChildFound : lookupFiber
    @{DGamma.CP3StatementChecks.registrationTestNameEq} generatedChild
    (registry (namedAfter (childRetire evidence))) = Just retiredChildFiber
  0 retiredChildParent : fiberParent retiredChildFiber = ChildOf 0

0 roleChildRetiredEvidence :
  (evidence : RoleChangingNamedTrace generatedChild) ->
  RoleChildRetiredEvidence generatedChild evidence
roleChildRetiredEvidence {generatedChild} evidence =
  case namedRetireLookup registrationTestNameEq registrationTestKeyEq
       (freshFiber registrationTestChild (ChildOf 0))
       (namedInsertLookup (childInsert evidence)) (childRetire evidence) of
    (afterFiber ** (afterFound, afterParent)) =>
      MkRoleChildRetiredEvidence afterFiber afterFound (trans afterParent Refl)

0 freshChoiceSameExternal :
  (left : RoleChangingNamedTrace 1) ->
  (right : RoleChangingNamedTrace 2) ->
  SameExternalOrchestration
    DGamma.CP3StatementChecks.registrationTestNameEq
    (namedRoleChangingTrace left) (namedRoleChangingTrace right)
freshChoiceSameExternal left right =
  let leftRetired = roleChildRetiredEvidence left
      rightRetired = roleChildRetiredEvidence right in
  MatchExternalInput (OInsert 0 Root registrationTestParent)
            (namedTransition (rootInsert0 left)) (namedRoleTail2 left)
            (RootInsertStep (namedAction (rootInsert0 left)))
            (namedTransition (rootInsert0 right)) (namedRoleTail2 right)
            (RootInsertStep (namedAction (rootInsert0 right)))
            (namedAction (rootInsert0 left)) (namedAction (rootInsert0 right))
          (SkipLeftInternal (namedTransition (parentBegin left))
            (namedRoleTail3 left)
            (lifecycleCannotBeRoot (namedTransition (parentBegin left))
              (trans (cong isLifecycleAction (namedAction (parentBegin left)))
                Refl))
          (SkipRightInternal (namedTransition (parentBegin right))
            (namedRoleTail3 right)
            (lifecycleCannotBeRoot (namedTransition (parentBegin right))
              (trans (cong isLifecycleAction (namedAction (parentBegin right)))
                Refl))
          (SkipLeftInternal (namedTransition (childInsert left))
            (namedRoleTail4 left)
            (childInsertCannotBeRoot (namedTransition (childInsert left))
              (namedAction (childInsert left)))
          (SkipRightInternal (namedTransition (childInsert right))
            (namedRoleTail4 right)
            (childInsertCannotBeRoot (namedTransition (childInsert right))
              (namedAction (childInsert right)))
          (SkipLeftInternal (namedTransition (childRetire left))
            (namedRoleTail5 left)
            (childRetireCannotBeRoot registrationTestNameEq
              (namedTransition (childRetire left))
              (namedAction (childRetire left))
              (freshFiber registrationTestChild (ChildOf 0))
              (namedInsertLookup (childInsert left)) Refl)
          (SkipRightInternal (namedTransition (childRetire right))
            (namedRoleTail5 right)
            (childRetireCannotBeRoot registrationTestNameEq
              (namedTransition (childRetire right))
              (namedAction (childRetire right))
              (freshFiber registrationTestChild (ChildOf 0))
              (namedInsertLookup (childInsert right)) Refl)
          (SkipLeftInternal (namedTransition (childRemove left))
            (namedRoleTail6 left)
            (childRemoveCannotBeRoot registrationTestNameEq
              (namedTransition (childRemove left))
              (namedAction (childRemove left))
              (retiredChildFiber leftRetired) (retiredChildFound leftRetired)
              (retiredChildParent leftRetired))
          (SkipRightInternal (namedTransition (childRemove right))
            (namedRoleTail6 right)
            (childRemoveCannotBeRoot registrationTestNameEq
              (namedTransition (childRemove right))
              (namedAction (childRemove right))
              (retiredChildFiber rightRetired) (retiredChildFound rightRetired)
              (retiredChildParent rightRetired))
          (MatchExternalInput (OInsert 1 Root registrationTestChild)
            (namedTransition (rootInsert1 left)) (namedRoleTail7 left)
            (RootInsertStep (namedAction (rootInsert1 left)))
            (namedTransition (rootInsert1 right)) (namedRoleTail7 right)
            (RootInsertStep (namedAction (rootInsert1 right)))
            (namedAction (rootInsert1 left)) (namedAction (rootInsert1 right))
          (SkipLeftInternal (namedTransition (parentAdvance left))
            (namedRoleTail8 left)
            (lifecycleCannotBeRoot (namedTransition (parentAdvance left))
              (trans (cong isLifecycleAction (namedAction (parentAdvance left)))
                Refl))
          (SkipRightInternal (namedTransition (parentAdvance right))
            (namedRoleTail8 right)
            (lifecycleCannotBeRoot (namedTransition (parentAdvance right))
              (trans (cong isLifecycleAction (namedAction (parentAdvance right)))
                Refl))
          (SkipLeftInternal (namedTransition (rootBegin1 left))
            (namedRoleTail9 left)
            (lifecycleCannotBeRoot (namedTransition (rootBegin1 left))
              (trans (cong isLifecycleAction (namedAction (rootBegin1 left)))
                Refl))
          (SkipRightInternal (namedTransition (rootBegin1 right))
            (namedRoleTail9 right)
            (lifecycleCannotBeRoot (namedTransition (rootBegin1 right))
              (trans (cong isLifecycleAction (namedAction (rootBegin1 right)))
                Refl))
          (SkipLeftInternal (namedTransition (rootAdvance1 left)) NoTransitions
            (lifecycleCannotBeRoot (namedTransition (rootAdvance1 left))
              (trans (cong isLifecycleAction (namedAction (rootAdvance1 left)))
                Refl))
          (SkipRightInternal (namedTransition (rootAdvance1 right)) NoTransitions
            (lifecycleCannotBeRoot (namedTransition (rootAdvance1 right))
              (trans (cong isLifecycleAction (namedAction (rootAdvance1 right)))
                Refl))
            SameExternalOrchestrationEnd)))))))))))))))

buildRoleChangingNamedTrace : (generatedChild : Nat) ->
  Maybe (RoleChangingNamedTrace generatedChild)
buildRoleChangingNamedTrace generatedChild = do
  t1 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (OInsert 0 Root registrationTestParent) registrationTestInitial
  t2 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq (LBegin 0)
    (namedAfter t1)
  t3 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (OInsert generatedChild (ChildOf 0) registrationTestChild) (namedAfter t2)
  t4 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (ORetire generatedChild) (namedAfter t3)
  t5 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (ORemove generatedChild) (namedAfter t4)
  t6 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (OInsert 1 Root registrationTestChild) (namedAfter t5)
  t7 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (LAdvance 0) (namedAfter t6)
  t8 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (LBegin 1) (namedAfter t7)
  t9 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (LAdvance 1) (namedAfter t8)
  Just (MkRoleChangingNamedTrace t1 t2 t3 t4 t5 t6 t7 t8 t9)

0 freshChoiceExternalRootBirthCorrespondence :
  (left : RoleChangingNamedTrace 1) ->
  (right : RoleChangingNamedTrace 2) ->
  ExternalRootBirthCorrespondence
    DGamma.CP3StatementChecks.freshChoiceGenerationBijection 0
    (namedRoleChangingTrace left) 0 (namedRoleChangingTrace right)
freshChoiceExternalRootBirthCorrespondence left right =
  MatchExternalRootBirth
    (namedTransition (rootInsert0 left)) (namedRoleTail2 left)
    (namedTransition (rootInsert0 right)) (namedRoleTail2 right)
    (namedAction (rootInsert0 left)) (namedAction (rootInsert0 right)) Refl
  (SkipLeftNonExternalRootBirth (LBegin 0)
    (namedTransition (parentBegin left)) (namedRoleTail3 left)
    (namedAction (parentBegin left)) Refl
  (SkipRightNonExternalRootBirth (LBegin 0)
    (namedTransition (parentBegin right)) (namedRoleTail3 right)
    (namedAction (parentBegin right)) Refl
  (SkipLeftNonExternalRootBirth
    (OInsert 1 (ChildOf 0) registrationTestChild)
    (namedTransition (childInsert left)) (namedRoleTail4 left)
    (namedAction (childInsert left)) Refl
  (SkipRightNonExternalRootBirth
    (OInsert 2 (ChildOf 0) registrationTestChild)
    (namedTransition (childInsert right)) (namedRoleTail4 right)
    (namedAction (childInsert right)) Refl
  (SkipLeftNonExternalRootBirth (ORetire 1)
    (namedTransition (childRetire left)) (namedRoleTail5 left)
    (namedAction (childRetire left)) Refl
  (SkipRightNonExternalRootBirth (ORetire 2)
    (namedTransition (childRetire right)) (namedRoleTail5 right)
    (namedAction (childRetire right)) Refl
  (SkipLeftNonExternalRootBirth (ORemove 1)
    (namedTransition (childRemove left)) (namedRoleTail6 left)
    (namedAction (childRemove left)) Refl
  (SkipRightNonExternalRootBirth (ORemove 2)
    (namedTransition (childRemove right)) (namedRoleTail6 right)
    (namedAction (childRemove right)) Refl
  (MatchExternalRootBirth
    (namedTransition (rootInsert1 left)) (namedRoleTail7 left)
    (namedTransition (rootInsert1 right)) (namedRoleTail7 right)
    (namedAction (rootInsert1 left)) (namedAction (rootInsert1 right)) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 0)
    (namedTransition (parentAdvance left)) (namedRoleTail8 left)
    (namedAction (parentAdvance left)) Refl
  (SkipRightNonExternalRootBirth (LAdvance 0)
    (namedTransition (parentAdvance right)) (namedRoleTail8 right)
    (namedAction (parentAdvance right)) Refl
  (SkipLeftNonExternalRootBirth (LBegin 1)
    (namedTransition (rootBegin1 left)) (namedRoleTail9 left)
    (namedAction (rootBegin1 left)) Refl
  (SkipRightNonExternalRootBirth (LBegin 1)
    (namedTransition (rootBegin1 right)) (namedRoleTail9 right)
    (namedAction (rootBegin1 right)) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 1)
    (namedTransition (rootAdvance1 left)) NoTransitions
    (namedAction (rootAdvance1 left)) Refl
  (SkipRightNonExternalRootBirth (LAdvance 1)
    (namedTransition (rootAdvance1 right)) NoTransitions
    (namedAction (rootAdvance1 right)) Refl
    ExternalRootBirthCorrespondenceEnd)))))))))))))))

0 freshChoiceSameInputs :
  (left : RoleChangingNamedTrace 1) ->
  (right : RoleChangingNamedTrace 2) ->
  SameOrchestrationModuloGenerated
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq
    (namedRoleChangingTrace left) (namedRoleChangingTrace right)
freshChoiceSameInputs left right =
  MkSameOrchestrationModuloGenerated freshChoiceGenerationBijection
    (freshChoiceSameExternal left right)
    (freshChoiceExternalRootBirthCorrespondence left right)
    (freshChoiceRegistrationCorrespondence left right)
    (freshChoiceCurrentEndpointRenaming left right)

||| Concrete checked witness for the reviewer's blocker pair.  The left trace
||| uses raw child 1 and later live root 1; the right trace uses raw child 2 and
||| the same later live root 1.  The historical generations swap while the
||| current endpoint bijection is identity.
public export
record FreshChoiceCorrespondenceWitness where
  constructor MkFreshChoiceCorrespondenceWitness
  leftFreshChoice : RoleChangingNamedTrace 1
  rightFreshChoice : RoleChangingNamedTrace 2
  0 blockerPairSameInputs : SameOrchestrationModuloGenerated
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq
    (namedRoleChangingTrace leftFreshChoice)
    (namedRoleChangingTrace rightFreshChoice)

public export
freshChoiceCorrespondenceWitness : Maybe FreshChoiceCorrespondenceWitness
freshChoiceCorrespondenceWitness = do
  left <- buildRoleChangingNamedTrace 1
  right <- buildRoleChangingNamedTrace 2
  Just (MkFreshChoiceCorrespondenceWitness left right
    (freshChoiceSameInputs left right))

public export
freshChoiceCorrespondenceCheck : Bool
freshChoiceCorrespondenceCheck = case freshChoiceCorrespondenceWitness of
  Nothing => False
  Just witness => True

swapFourFive : Nat -> Nat
swapFourFive 4 = 5
swapFourFive 5 = 4
swapFourFive n = n

0 swapFourFiveInvolutive : (n : Nat) -> swapFourFive (swapFourFive n) = n
swapFourFiveInvolutive Z = Refl
swapFourFiveInvolutive (S Z) = Refl
swapFourFiveInvolutive (S (S Z)) = Refl
swapFourFiveInvolutive (S (S (S Z))) = Refl
swapFourFiveInvolutive (S (S (S (S Z)))) = Refl
swapFourFiveInvolutive (S (S (S (S (S Z))))) = Refl
swapFourFiveInvolutive (S (S (S (S (S (S later)))))) = Refl

swapCrossParentGeneration : RegistrationGeneration Nat -> RegistrationGeneration Nat
swapCrossParentGeneration (MkRegistrationGeneration 2 ordinal) =
  MkRegistrationGeneration 2 (swapFourFive ordinal)
swapCrossParentGeneration (MkRegistrationGeneration 3 ordinal) =
  MkRegistrationGeneration 3 (swapFourFive ordinal)
swapCrossParentGeneration generation = generation

0 swapCrossParentGenerationInvolutive :
  (generation : RegistrationGeneration Nat) ->
  swapCrossParentGeneration (swapCrossParentGeneration generation) = generation
swapCrossParentGenerationInvolutive (MkRegistrationGeneration Z ordinal) = Refl
swapCrossParentGenerationInvolutive
  (MkRegistrationGeneration (S Z) ordinal) = Refl
swapCrossParentGenerationInvolutive
  (MkRegistrationGeneration (S (S Z)) ordinal) =
    cong (MkRegistrationGeneration 2) (swapFourFiveInvolutive ordinal)
swapCrossParentGenerationInvolutive
  (MkRegistrationGeneration (S (S (S Z))) ordinal) =
    cong (MkRegistrationGeneration 3) (swapFourFiveInvolutive ordinal)
swapCrossParentGenerationInvolutive
  (MkRegistrationGeneration (S (S (S (S later)))) ordinal) = Refl

public export
crossParentGenerationBijection : RegistrationGenerationBijection Nat
crossParentGenerationBijection = MkRegistrationGenerationBijection
  swapCrossParentGeneration swapCrossParentGeneration
  swapCrossParentGenerationInvolutive swapCrossParentGenerationInvolutive

record CrossParentNamedTrace
  (firstChild, firstParent, secondChild, secondParent : Nat) where
  constructor MkCrossParentNamedTrace
  crossRoot0 : CheckedNamedTransition
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq
    (OInsert 0 Root DGamma.CP3StatementChecks.registrationTestParent)
    DGamma.CP3StatementChecks.registrationTestInitial
  crossRoot1 : CheckedNamedTransition
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq
    (OInsert 1 Root DGamma.CP3StatementChecks.registrationTestParent)
    (namedAfter crossRoot0)
  crossBegin0 : CheckedNamedTransition
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (LBegin 0)
    (namedAfter crossRoot1)
  crossBegin1 : CheckedNamedTransition
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (LBegin 1)
    (namedAfter crossBegin0)
  crossFirstChild : CheckedNamedTransition
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq
    (OInsert firstChild (ChildOf firstParent)
      DGamma.CP3StatementChecks.registrationTestChild)
    (namedAfter crossBegin1)
  crossSecondChild : CheckedNamedTransition
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq
    (OInsert secondChild (ChildOf secondParent)
      DGamma.CP3StatementChecks.registrationTestChild)
    (namedAfter crossFirstChild)
  crossAdvance0 : CheckedNamedTransition
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (LAdvance 0)
    (namedAfter crossSecondChild)
  crossAdvance1 : CheckedNamedTransition
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (LAdvance 1)
    (namedAfter crossAdvance0)
  crossBegin2 : CheckedNamedTransition
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (LBegin 2)
    (namedAfter crossAdvance1)
  crossAdvance2 : CheckedNamedTransition
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (LAdvance 2)
    (namedAfter crossBegin2)
  crossBegin3 : CheckedNamedTransition
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (LBegin 3)
    (namedAfter crossAdvance2)
  crossAdvance3 : CheckedNamedTransition
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq (LAdvance 3)
    (namedAfter crossBegin3)

crossParentTrace :
  (trace : CrossParentNamedTrace firstChild firstParent secondChild secondParent) ->
  Transitions DGamma.CP3StatementChecks.registrationTestInitial
    (namedAfter (crossAdvance3 trace))
crossParentTrace trace =
  MoreTransitions (namedTransition (crossRoot0 trace))
  (MoreTransitions (namedTransition (crossRoot1 trace))
  (MoreTransitions (namedTransition (crossBegin0 trace))
  (MoreTransitions (namedTransition (crossBegin1 trace))
  (MoreTransitions (namedTransition (crossFirstChild trace))
  (MoreTransitions (namedTransition (crossSecondChild trace))
  (MoreTransitions (namedTransition (crossAdvance0 trace))
  (MoreTransitions (namedTransition (crossAdvance1 trace))
  (MoreTransitions (namedTransition (crossBegin2 trace))
  (MoreTransitions (namedTransition (crossAdvance2 trace))
  (MoreTransitions (namedTransition (crossBegin3 trace))
  (MoreTransitions (namedTransition (crossAdvance3 trace))
    NoTransitions)))))))))))

crossTail12 : (trace : CrossParentNamedTrace a b c d) ->
  Transitions (namedAfter (crossBegin3 trace)) (namedAfter (crossAdvance3 trace))
crossTail12 trace = MoreTransitions (namedTransition (crossAdvance3 trace)) NoTransitions
crossTail11 : (trace : CrossParentNamedTrace a b c d) ->
  Transitions (namedAfter (crossAdvance2 trace)) (namedAfter (crossAdvance3 trace))
crossTail11 trace = MoreTransitions (namedTransition (crossBegin3 trace)) (crossTail12 trace)
crossTail10 : (trace : CrossParentNamedTrace a b c d) ->
  Transitions (namedAfter (crossBegin2 trace)) (namedAfter (crossAdvance3 trace))
crossTail10 trace = MoreTransitions (namedTransition (crossAdvance2 trace)) (crossTail11 trace)
crossTail9 : (trace : CrossParentNamedTrace a b c d) ->
  Transitions (namedAfter (crossAdvance1 trace)) (namedAfter (crossAdvance3 trace))
crossTail9 trace = MoreTransitions (namedTransition (crossBegin2 trace)) (crossTail10 trace)
crossTail8 : (trace : CrossParentNamedTrace a b c d) ->
  Transitions (namedAfter (crossAdvance0 trace)) (namedAfter (crossAdvance3 trace))
crossTail8 trace = MoreTransitions (namedTransition (crossAdvance1 trace)) (crossTail9 trace)
crossTail7 : (trace : CrossParentNamedTrace a b c d) ->
  Transitions (namedAfter (crossSecondChild trace)) (namedAfter (crossAdvance3 trace))
crossTail7 trace = MoreTransitions (namedTransition (crossAdvance0 trace)) (crossTail8 trace)
crossTail6 : (trace : CrossParentNamedTrace a b c d) ->
  Transitions (namedAfter (crossFirstChild trace)) (namedAfter (crossAdvance3 trace))
crossTail6 trace = MoreTransitions (namedTransition (crossSecondChild trace)) (crossTail7 trace)
crossTail5 : (trace : CrossParentNamedTrace a b c d) ->
  Transitions (namedAfter (crossBegin1 trace)) (namedAfter (crossAdvance3 trace))
crossTail5 trace = MoreTransitions (namedTransition (crossFirstChild trace)) (crossTail6 trace)
crossTail4 : (trace : CrossParentNamedTrace a b c d) ->
  Transitions (namedAfter (crossBegin0 trace)) (namedAfter (crossAdvance3 trace))
crossTail4 trace = MoreTransitions (namedTransition (crossBegin1 trace)) (crossTail5 trace)
crossTail3 : (trace : CrossParentNamedTrace a b c d) ->
  Transitions (namedAfter (crossRoot1 trace)) (namedAfter (crossAdvance3 trace))
crossTail3 trace = MoreTransitions (namedTransition (crossBegin0 trace)) (crossTail4 trace)
crossTail2 : (trace : CrossParentNamedTrace a b c d) ->
  Transitions (namedAfter (crossRoot0 trace)) (namedAfter (crossAdvance3 trace))
crossTail2 trace = MoreTransitions (namedTransition (crossRoot1 trace)) (crossTail3 trace)

buildCrossParentNamedTrace :
  (firstChild, firstParent, secondChild, secondParent : Nat) ->
  Maybe (CrossParentNamedTrace firstChild firstParent secondChild secondParent)
buildCrossParentNamedTrace firstChild firstParent secondChild secondParent = do
  t1 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (OInsert 0 Root registrationTestParent) registrationTestInitial
  t2 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (OInsert 1 Root registrationTestParent) (namedAfter t1)
  t3 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (LBegin 0) (namedAfter t2)
  t4 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (LBegin 1) (namedAfter t3)
  t5 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (OInsert firstChild (ChildOf firstParent) registrationTestChild)
    (namedAfter t4)
  t6 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (OInsert secondChild (ChildOf secondParent) registrationTestChild)
    (namedAfter t5)
  t7 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (LAdvance 0) (namedAfter t6)
  t8 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (LAdvance 1) (namedAfter t7)
  t9 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (LBegin 2) (namedAfter t8)
  t10 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (LAdvance 2) (namedAfter t9)
  t11 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (LBegin 3) (namedAfter t10)
  t12 <- checkedNamedFire registrationTestNameEq registrationTestKeyEq
    (LAdvance 3) (namedAfter t11)
  Just (MkCrossParentNamedTrace t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12)

crossRootsIndex : RegistrationIndexState Nat
crossRootsIndex =
  let root0 = registrationTestAdvance 0
        (OInsert 0 Root registrationTestParent) DGamma.CP3.emptyRegistrationIndex
      root1 = registrationTestAdvance 1
        (OInsert 1 Root registrationTestParent) root0
      begin0 = registrationTestAdvance 2 (LBegin 0) root1 in
    registrationTestAdvance 3 (LBegin 1) begin0

crossLeftBeforeSecondIndex : RegistrationIndexState Nat
crossLeftBeforeSecondIndex = registrationTestAdvanceSurviving 4
  2 0 registrationTestChild crossRootsIndex

crossRightBeforeSecondIndex : RegistrationIndexState Nat
crossRightBeforeSecondIndex = registrationTestAdvanceSurviving 4
  3 1 registrationTestChild crossRootsIndex

crossLeftFinalIndex : RegistrationIndexState Nat
crossLeftFinalIndex =
  let child3 = registrationTestAdvanceSurviving 5
        3 1 registrationTestChild crossLeftBeforeSecondIndex
      advance0 = registrationTestAdvance 6 (LAdvance 0) child3
      advance1 = registrationTestAdvance 7 (LAdvance 1) advance0
      begin2 = registrationTestAdvance 8 (LBegin 2) advance1
      advance2 = registrationTestAdvance 9 (LAdvance 2) begin2
      begin3 = registrationTestAdvance 10 (LBegin 3) advance2 in
    registrationTestAdvance 11 (LAdvance 3) begin3

crossRightFinalIndex : RegistrationIndexState Nat
crossRightFinalIndex =
  let child2 = registrationTestAdvanceSurviving 5
        2 0 registrationTestChild crossRightBeforeSecondIndex
      advance0 = registrationTestAdvance 6 (LAdvance 0) child2
      advance1 = registrationTestAdvance 7 (LAdvance 1) advance0
      begin2 = registrationTestAdvance 8 (LBegin 2) advance1
      advance2 = registrationTestAdvance 9 (LAdvance 2) begin2
      begin3 = registrationTestAdvance 10 (LBegin 3) advance2 in
    registrationTestAdvance 11 (LAdvance 3) begin3

0 crossNoParentUnloadTail7 : (parent : Nat) ->
  (trace : CrossParentNamedTrace a b c d) ->
  NoParentUnload parent (crossTail7 trace)
crossNoParentUnloadTail7 parent trace =
  NoParentUnloadStep (namedTransition (crossAdvance0 trace))
    (crossTail8 trace)
    (namedTransitionNotUnload (crossAdvance0 trace) (\Refl impossible))
  (NoParentUnloadStep (namedTransition (crossAdvance1 trace))
    (crossTail9 trace)
    (namedTransitionNotUnload (crossAdvance1 trace) (\Refl impossible))
  (NoParentUnloadStep (namedTransition (crossBegin2 trace))
    (crossTail10 trace)
    (namedTransitionNotUnload (crossBegin2 trace) (\Refl impossible))
  (NoParentUnloadStep (namedTransition (crossAdvance2 trace))
    (crossTail11 trace)
    (namedTransitionNotUnload (crossAdvance2 trace) (\Refl impossible))
  (NoParentUnloadStep (namedTransition (crossBegin3 trace))
    (crossTail12 trace)
    (namedTransitionNotUnload (crossBegin3 trace) (\Refl impossible))
  (NoParentUnloadStep (namedTransition (crossAdvance3 trace))
    NoTransitions
    (namedTransitionNotUnload (crossAdvance3 trace) (\Refl impossible))
    NoParentUnloadEnd)))))

0 crossNoParentUnloadTail6 : (parent : Nat) ->
  (trace : CrossParentNamedTrace a b c d) ->
  NoParentUnload parent (crossTail6 trace)
crossNoParentUnloadTail6 parent trace =
  NoParentUnloadStep (namedTransition (crossSecondChild trace))
    (crossTail7 trace)
    (namedTransitionNotUnload (crossSecondChild trace) (\Refl impossible))
    (crossNoParentUnloadTail7 parent trace)

0 crossLeftFirstSurvives : (trace : CrossParentNamedTrace 2 0 3 1) ->
  SurvivingRegistration
    (registrationEventAt @{DGamma.CP3StatementChecks.registrationTestNameEq}
      4 DGamma.CP3StatementChecks.crossRootsIndex 2 0
      DGamma.CP3StatementChecks.registrationTestChild)
    (crossTail6 trace)
crossLeftFirstSurvives trace = MkSurvivingRegistration
  (MkRegistrationActivation (MkRegistrationGeneration 0 0) 2) Refl
  (crossNoParentUnloadTail6 0 trace)

0 crossLeftSecondSurvives : (trace : CrossParentNamedTrace 2 0 3 1) ->
  SurvivingRegistration
    (registrationEventAt @{DGamma.CP3StatementChecks.registrationTestNameEq}
      5 DGamma.CP3StatementChecks.crossLeftBeforeSecondIndex
      3 1 DGamma.CP3StatementChecks.registrationTestChild) (crossTail7 trace)
crossLeftSecondSurvives trace = MkSurvivingRegistration
  (MkRegistrationActivation (MkRegistrationGeneration 1 1) 3) Refl
  (crossNoParentUnloadTail7 1 trace)

0 crossRightFirstSurvives : (trace : CrossParentNamedTrace 3 1 2 0) ->
  SurvivingRegistration
    (registrationEventAt @{DGamma.CP3StatementChecks.registrationTestNameEq}
      4 DGamma.CP3StatementChecks.crossRootsIndex 3 1
      DGamma.CP3StatementChecks.registrationTestChild)
    (crossTail6 trace)
crossRightFirstSurvives trace = MkSurvivingRegistration
  (MkRegistrationActivation (MkRegistrationGeneration 1 1) 3) Refl
  (crossNoParentUnloadTail6 1 trace)

0 crossRightSecondSurvives : (trace : CrossParentNamedTrace 3 1 2 0) ->
  SurvivingRegistration
    (registrationEventAt @{DGamma.CP3StatementChecks.registrationTestNameEq}
      5 DGamma.CP3StatementChecks.crossRightBeforeSecondIndex
      2 0 DGamma.CP3StatementChecks.registrationTestChild) (crossTail7 trace)
crossRightSecondSurvives trace = MkSurvivingRegistration
  (MkRegistrationActivation (MkRegistrationGeneration 0 0) 2) Refl
  (crossNoParentUnloadTail7 0 trace)

0 crossParentGenerationTraceCorrespondence :
  (left : CrossParentNamedTrace 2 0 3 1) ->
  (right : CrossParentNamedTrace 3 1 2 0) ->
  RegistrationTraceCorrespondence
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.crossParentGenerationBijection
    0 DGamma.CP3.emptyRegistrationIndex (crossParentTrace left)
      DGamma.CP3StatementChecks.crossLeftFinalIndex
    0 DGamma.CP3.emptyRegistrationIndex (crossParentTrace right)
      DGamma.CP3StatementChecks.crossRightFinalIndex [] []
crossParentGenerationTraceCorrespondence left right =
  SkipLeftNonRegistration (OInsert 0 Root registrationTestParent)
    (namedTransition (crossRoot0 left)) (crossTail2 left)
    (namedAction (crossRoot0 left)) Refl
  (SkipLeftNonRegistration (OInsert 1 Root registrationTestParent)
    (namedTransition (crossRoot1 left)) (crossTail3 left)
    (namedAction (crossRoot1 left)) Refl
  (SkipLeftNonRegistration (LBegin 0)
    (namedTransition (crossBegin0 left)) (crossTail4 left)
    (namedAction (crossBegin0 left)) Refl
  (SkipLeftNonRegistration (LBegin 1)
    (namedTransition (crossBegin1 left)) (crossTail5 left)
    (namedAction (crossBegin1 left)) Refl
  (QueueLeftGeneratedRegistration
    (namedTransition (crossFirstChild left)) (crossTail6 left)
    (namedAction (crossFirstChild left)) (crossLeftFirstSurvives left)
  (QueueLeftGeneratedRegistration
    (namedTransition (crossSecondChild left)) (crossTail7 left)
    (namedAction (crossSecondChild left)) (crossLeftSecondSurvives left)
  (SkipLeftNonRegistration (LAdvance 0)
    (namedTransition (crossAdvance0 left)) (crossTail8 left)
    (namedAction (crossAdvance0 left)) Refl
  (SkipLeftNonRegistration (LAdvance 1)
    (namedTransition (crossAdvance1 left)) (crossTail9 left)
    (namedAction (crossAdvance1 left)) Refl
  (SkipLeftNonRegistration (LBegin 2)
    (namedTransition (crossBegin2 left)) (crossTail10 left)
    (namedAction (crossBegin2 left)) Refl
  (SkipLeftNonRegistration (LAdvance 2)
    (namedTransition (crossAdvance2 left)) (crossTail11 left)
    (namedAction (crossAdvance2 left)) Refl
  (SkipLeftNonRegistration (LBegin 3)
    (namedTransition (crossBegin3 left)) (crossTail12 left)
    (namedAction (crossBegin3 left)) Refl
  (SkipLeftNonRegistration (LAdvance 3)
    (namedTransition (crossAdvance3 left)) NoTransitions
    (namedAction (crossAdvance3 left)) Refl
  (SkipRightNonRegistration (OInsert 0 Root registrationTestParent)
    (namedTransition (crossRoot0 right)) (crossTail2 right)
    (namedAction (crossRoot0 right)) Refl
  (SkipRightNonRegistration (OInsert 1 Root registrationTestParent)
    (namedTransition (crossRoot1 right)) (crossTail3 right)
    (namedAction (crossRoot1 right)) Refl
  (SkipRightNonRegistration (LBegin 0)
    (namedTransition (crossBegin0 right)) (crossTail4 right)
    (namedAction (crossBegin0 right)) Refl
  (SkipRightNonRegistration (LBegin 1)
    (namedTransition (crossBegin1 right)) (crossTail5 right)
    (namedAction (crossBegin1 right)) Refl
  (MatchRightWithPendingLeft
    (namedTransition (crossFirstChild right)) (crossTail6 right)
    (namedAction (crossFirstChild right)) (crossRightFirstSurvives right) []
    (registrationEventAt @{DGamma.CP3StatementChecks.registrationTestNameEq}
      5 DGamma.CP3StatementChecks.crossLeftBeforeSecondIndex
      3 1 registrationTestChild)
    [(registrationEventAt @{DGamma.CP3StatementChecks.registrationTestNameEq}
      4 DGamma.CP3StatementChecks.crossRootsIndex
      2 0 registrationTestChild)]
    (MkRegistrationEventMatch Refl
      (MkRegistrationActivation (MkRegistrationGeneration 1 1) 3)
      (MkRegistrationActivation (MkRegistrationGeneration 1 1) 3)
      Refl Refl Refl Refl Refl)
  (MatchRightWithPendingLeft
    (namedTransition (crossSecondChild right)) (crossTail7 right)
    (namedAction (crossSecondChild right)) (crossRightSecondSurvives right) []
    (registrationEventAt @{DGamma.CP3StatementChecks.registrationTestNameEq}
      4 DGamma.CP3StatementChecks.crossRootsIndex
      2 0 registrationTestChild) []
    (MkRegistrationEventMatch Refl
      (MkRegistrationActivation (MkRegistrationGeneration 0 0) 2)
      (MkRegistrationActivation (MkRegistrationGeneration 0 0) 2)
      Refl Refl Refl Refl Refl)
  (SkipRightNonRegistration (LAdvance 0)
    (namedTransition (crossAdvance0 right)) (crossTail8 right)
    (namedAction (crossAdvance0 right)) Refl
  (SkipRightNonRegistration (LAdvance 1)
    (namedTransition (crossAdvance1 right)) (crossTail9 right)
    (namedAction (crossAdvance1 right)) Refl
  (SkipRightNonRegistration (LBegin 2)
    (namedTransition (crossBegin2 right)) (crossTail10 right)
    (namedAction (crossBegin2 right)) Refl
  (SkipRightNonRegistration (LAdvance 2)
    (namedTransition (crossAdvance2 right)) (crossTail11 right)
    (namedAction (crossAdvance2 right)) Refl
  (SkipRightNonRegistration (LBegin 3)
    (namedTransition (crossBegin3 right)) (crossTail12 right)
    (namedAction (crossBegin3 right)) Refl
  (SkipRightNonRegistration (LAdvance 3)
    (namedTransition (crossAdvance3 right)) NoTransitions
    (namedAction (crossAdvance3 right)) Refl
    RegistrationCorrespondenceEnd)))))))))))))))))))))))

public export
0 namedLifecycleNotRoot :
  (step : CheckedNamedTransition nameEq keyEq action before) ->
  isLifecycleAction action = True ->
  RootOrchestrationStep nameEq (namedTransition step) -> Void
namedLifecycleNotRoot step lifecycle =
  lifecycleCannotBeRoot (namedTransition step)
    (trans (cong isLifecycleAction (namedAction step)) lifecycle)

0 crossParentExternalRootBirthCorrespondence :
  (left : CrossParentNamedTrace 2 0 3 1) ->
  (right : CrossParentNamedTrace 3 1 2 0) ->
  ExternalRootBirthCorrespondence
    DGamma.CP3StatementChecks.crossParentGenerationBijection 0
    (crossParentTrace left) 0 (crossParentTrace right)
crossParentExternalRootBirthCorrespondence left right =
  MatchExternalRootBirth
    (namedTransition (crossRoot0 left)) (crossTail2 left)
    (namedTransition (crossRoot0 right)) (crossTail2 right)
    (namedAction (crossRoot0 left)) (namedAction (crossRoot0 right)) Refl
  (MatchExternalRootBirth
    (namedTransition (crossRoot1 left)) (crossTail3 left)
    (namedTransition (crossRoot1 right)) (crossTail3 right)
    (namedAction (crossRoot1 left)) (namedAction (crossRoot1 right)) Refl
  (SkipLeftNonExternalRootBirth (LBegin 0)
    (namedTransition (crossBegin0 left)) (crossTail4 left)
    (namedAction (crossBegin0 left)) Refl
  (SkipLeftNonExternalRootBirth (LBegin 1)
    (namedTransition (crossBegin1 left)) (crossTail5 left)
    (namedAction (crossBegin1 left)) Refl
  (SkipLeftNonExternalRootBirth
    (OInsert 2 (ChildOf 0) registrationTestChild)
    (namedTransition (crossFirstChild left)) (crossTail6 left)
    (namedAction (crossFirstChild left)) Refl
  (SkipLeftNonExternalRootBirth
    (OInsert 3 (ChildOf 1) registrationTestChild)
    (namedTransition (crossSecondChild left)) (crossTail7 left)
    (namedAction (crossSecondChild left)) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 0)
    (namedTransition (crossAdvance0 left)) (crossTail8 left)
    (namedAction (crossAdvance0 left)) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 1)
    (namedTransition (crossAdvance1 left)) (crossTail9 left)
    (namedAction (crossAdvance1 left)) Refl
  (SkipLeftNonExternalRootBirth (LBegin 2)
    (namedTransition (crossBegin2 left)) (crossTail10 left)
    (namedAction (crossBegin2 left)) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 2)
    (namedTransition (crossAdvance2 left)) (crossTail11 left)
    (namedAction (crossAdvance2 left)) Refl
  (SkipLeftNonExternalRootBirth (LBegin 3)
    (namedTransition (crossBegin3 left)) (crossTail12 left)
    (namedAction (crossBegin3 left)) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 3)
    (namedTransition (crossAdvance3 left)) NoTransitions
    (namedAction (crossAdvance3 left)) Refl
  (SkipRightNonExternalRootBirth (LBegin 0)
    (namedTransition (crossBegin0 right)) (crossTail4 right)
    (namedAction (crossBegin0 right)) Refl
  (SkipRightNonExternalRootBirth (LBegin 1)
    (namedTransition (crossBegin1 right)) (crossTail5 right)
    (namedAction (crossBegin1 right)) Refl
  (SkipRightNonExternalRootBirth
    (OInsert 3 (ChildOf 1) registrationTestChild)
    (namedTransition (crossFirstChild right)) (crossTail6 right)
    (namedAction (crossFirstChild right)) Refl
  (SkipRightNonExternalRootBirth
    (OInsert 2 (ChildOf 0) registrationTestChild)
    (namedTransition (crossSecondChild right)) (crossTail7 right)
    (namedAction (crossSecondChild right)) Refl
  (SkipRightNonExternalRootBirth (LAdvance 0)
    (namedTransition (crossAdvance0 right)) (crossTail8 right)
    (namedAction (crossAdvance0 right)) Refl
  (SkipRightNonExternalRootBirth (LAdvance 1)
    (namedTransition (crossAdvance1 right)) (crossTail9 right)
    (namedAction (crossAdvance1 right)) Refl
  (SkipRightNonExternalRootBirth (LBegin 2)
    (namedTransition (crossBegin2 right)) (crossTail10 right)
    (namedAction (crossBegin2 right)) Refl
  (SkipRightNonExternalRootBirth (LAdvance 2)
    (namedTransition (crossAdvance2 right)) (crossTail11 right)
    (namedAction (crossAdvance2 right)) Refl
  (SkipRightNonExternalRootBirth (LBegin 3)
    (namedTransition (crossBegin3 right)) (crossTail12 right)
    (namedAction (crossBegin3 right)) Refl
  (SkipRightNonExternalRootBirth (LAdvance 3)
    (namedTransition (crossAdvance3 right)) NoTransitions
    (namedAction (crossAdvance3 right)) Refl
    ExternalRootBirthCorrespondenceEnd)))))))))))))))))))))

0 crossParentSameExternal :
  (left : CrossParentNamedTrace 2 0 3 1) ->
  (right : CrossParentNamedTrace 3 1 2 0) ->
  SameExternalOrchestration DGamma.CP3StatementChecks.registrationTestNameEq
    (crossParentTrace left) (crossParentTrace right)
crossParentSameExternal left right =
  MatchExternalInput (OInsert 0 Root registrationTestParent)
    (namedTransition (crossRoot0 left)) (crossTail2 left)
    (RootInsertStep (namedAction (crossRoot0 left)))
    (namedTransition (crossRoot0 right)) (crossTail2 right)
    (RootInsertStep (namedAction (crossRoot0 right)))
    (namedAction (crossRoot0 left)) (namedAction (crossRoot0 right))
  (MatchExternalInput (OInsert 1 Root registrationTestParent)
    (namedTransition (crossRoot1 left)) (crossTail3 left)
    (RootInsertStep (namedAction (crossRoot1 left)))
    (namedTransition (crossRoot1 right)) (crossTail3 right)
    (RootInsertStep (namedAction (crossRoot1 right)))
    (namedAction (crossRoot1 left)) (namedAction (crossRoot1 right))
  (SkipLeftInternal (namedTransition (crossBegin0 left)) (crossTail4 left)
    (namedLifecycleNotRoot (crossBegin0 left) Refl)
  (SkipLeftInternal (namedTransition (crossBegin1 left)) (crossTail5 left)
    (namedLifecycleNotRoot (crossBegin1 left) Refl)
  (SkipLeftInternal (namedTransition (crossFirstChild left)) (crossTail6 left)
    (childInsertCannotBeRoot (namedTransition (crossFirstChild left))
      (namedAction (crossFirstChild left)))
  (SkipLeftInternal (namedTransition (crossSecondChild left)) (crossTail7 left)
    (childInsertCannotBeRoot (namedTransition (crossSecondChild left))
      (namedAction (crossSecondChild left)))
  (SkipLeftInternal (namedTransition (crossAdvance0 left)) (crossTail8 left)
    (namedLifecycleNotRoot (crossAdvance0 left) Refl)
  (SkipLeftInternal (namedTransition (crossAdvance1 left)) (crossTail9 left)
    (namedLifecycleNotRoot (crossAdvance1 left) Refl)
  (SkipLeftInternal (namedTransition (crossBegin2 left)) (crossTail10 left)
    (namedLifecycleNotRoot (crossBegin2 left) Refl)
  (SkipLeftInternal (namedTransition (crossAdvance2 left)) (crossTail11 left)
    (namedLifecycleNotRoot (crossAdvance2 left) Refl)
  (SkipLeftInternal (namedTransition (crossBegin3 left)) (crossTail12 left)
    (namedLifecycleNotRoot (crossBegin3 left) Refl)
  (SkipLeftInternal (namedTransition (crossAdvance3 left)) NoTransitions
    (namedLifecycleNotRoot (crossAdvance3 left) Refl)
  (SkipRightInternal (namedTransition (crossBegin0 right)) (crossTail4 right)
    (namedLifecycleNotRoot (crossBegin0 right) Refl)
  (SkipRightInternal (namedTransition (crossBegin1 right)) (crossTail5 right)
    (namedLifecycleNotRoot (crossBegin1 right) Refl)
  (SkipRightInternal (namedTransition (crossFirstChild right)) (crossTail6 right)
    (childInsertCannotBeRoot (namedTransition (crossFirstChild right))
      (namedAction (crossFirstChild right)))
  (SkipRightInternal (namedTransition (crossSecondChild right)) (crossTail7 right)
    (childInsertCannotBeRoot (namedTransition (crossSecondChild right))
      (namedAction (crossSecondChild right)))
  (SkipRightInternal (namedTransition (crossAdvance0 right)) (crossTail8 right)
    (namedLifecycleNotRoot (crossAdvance0 right) Refl)
  (SkipRightInternal (namedTransition (crossAdvance1 right)) (crossTail9 right)
    (namedLifecycleNotRoot (crossAdvance1 right) Refl)
  (SkipRightInternal (namedTransition (crossBegin2 right)) (crossTail10 right)
    (namedLifecycleNotRoot (crossBegin2 right) Refl)
  (SkipRightInternal (namedTransition (crossAdvance2 right)) (crossTail11 right)
    (namedLifecycleNotRoot (crossAdvance2 right) Refl)
  (SkipRightInternal (namedTransition (crossBegin3 right)) (crossTail12 right)
    (namedLifecycleNotRoot (crossBegin3 right) Refl)
  (SkipRightInternal (namedTransition (crossAdvance3 right)) NoTransitions
    (namedLifecycleNotRoot (crossAdvance3 right) Refl)
    SameExternalOrchestrationEnd)))))))))))))))))))))

0 crossParentRegistrationCorrespondence :
  (left : CrossParentNamedTrace 2 0 3 1) ->
  (right : CrossParentNamedTrace 3 1 2 0) ->
  RegistrationCorrespondenceByGeneration
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.crossParentGenerationBijection
    (crossParentTrace left) (crossParentTrace right)
crossParentRegistrationCorrespondence left right =
  MkRegistrationCorrespondenceByGeneration crossLeftFinalIndex
    crossRightFinalIndex (crossParentGenerationTraceCorrespondence left right)

0 crossParentCurrentForward :
  (left : CrossParentNamedTrace 2 0 3 1) ->
  (right : CrossParentNamedTrace 3 1 2 0) ->
  (n : Nat) -> (generation : RegistrationGeneration Nat) ->
  lookupCurrentGeneration @{DGamma.CP3StatementChecks.registrationTestNameEq} n
    (leftFinalGenerations (crossParentRegistrationCorrespondence left right)) =
      Just generation ->
  (rightGeneration : RegistrationGeneration Nat **
   (generationForward DGamma.CP3StatementChecks.crossParentGenerationBijection
      generation = rightGeneration,
    lookupCurrentGeneration @{DGamma.CP3StatementChecks.registrationTestNameEq} n
      (rightFinalGenerations (crossParentRegistrationCorrespondence left right)) =
        Just rightGeneration))
crossParentCurrentForward left right Z generation found =
  case justInjective found of
    Refl => (MkRegistrationGeneration 0 0 ** (Refl, Refl))
crossParentCurrentForward left right (S Z) generation found =
  case justInjective found of
    Refl => (MkRegistrationGeneration 1 1 ** (Refl, Refl))
crossParentCurrentForward left right (S (S Z)) generation found =
  case justInjective found of
    Refl => (MkRegistrationGeneration 2 5 ** (Refl, Refl))
crossParentCurrentForward left right (S (S (S Z))) generation found =
  case justInjective found of
    Refl => (MkRegistrationGeneration 3 4 ** (Refl, Refl))
crossParentCurrentForward left right (S (S (S (S later)))) generation found =
  void (nothingIsNotJust found)

0 crossParentCurrentBackward :
  (left : CrossParentNamedTrace 2 0 3 1) ->
  (right : CrossParentNamedTrace 3 1 2 0) ->
  (n : Nat) -> (generation : RegistrationGeneration Nat) ->
  lookupCurrentGeneration @{DGamma.CP3StatementChecks.registrationTestNameEq} n
    (rightFinalGenerations (crossParentRegistrationCorrespondence left right)) =
      Just generation ->
  (leftGeneration : RegistrationGeneration Nat **
   (generationBackward DGamma.CP3StatementChecks.crossParentGenerationBijection
      generation = leftGeneration,
    lookupCurrentGeneration @{DGamma.CP3StatementChecks.registrationTestNameEq} n
      (leftFinalGenerations (crossParentRegistrationCorrespondence left right)) =
        Just leftGeneration))
crossParentCurrentBackward left right Z generation found =
  case justInjective found of
    Refl => (MkRegistrationGeneration 0 0 ** (Refl, Refl))
crossParentCurrentBackward left right (S Z) generation found =
  case justInjective found of
    Refl => (MkRegistrationGeneration 1 1 ** (Refl, Refl))
crossParentCurrentBackward left right (S (S Z)) generation found =
  case justInjective found of
    Refl => (MkRegistrationGeneration 2 4 ** (Refl, Refl))
crossParentCurrentBackward left right (S (S (S Z))) generation found =
  case justInjective found of
    Refl => (MkRegistrationGeneration 3 5 ** (Refl, Refl))
crossParentCurrentBackward left right (S (S (S (S later)))) generation found =
  void (nothingIsNotJust found)

0 crossParentCurrentEndpointRenaming :
  (left : CrossParentNamedTrace 2 0 3 1) ->
  (right : CrossParentNamedTrace 3 1 2 0) ->
  CurrentEndpointRenaming DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq
    DGamma.CP3StatementChecks.crossParentGenerationBijection
    (crossParentTrace left) (crossParentTrace right)
    (crossParentRegistrationCorrespondence left right)
crossParentCurrentEndpointRenaming left right =
  MkCurrentEndpointRenaming identityNameBijection
    (\n, fiber, found, root => Refl)
    (\n, fiber, found, root => Refl)
    (\n, generation, found =>
      Right (crossParentCurrentForward left right n generation found))
    (\n, generation, found =>
      Right (crossParentCurrentBackward left right n generation found))

0 crossParentSameInputs :
  (left : CrossParentNamedTrace 2 0 3 1) ->
  (right : CrossParentNamedTrace 3 1 2 0) ->
  SameOrchestrationModuloGenerated
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq
    (crossParentTrace left) (crossParentTrace right)
crossParentSameInputs left right =
  MkSameOrchestrationModuloGenerated crossParentGenerationBijection
    (crossParentSameExternal left right)
    (crossParentExternalRootBirthCorrespondence left right)
    (crossParentRegistrationCorrespondence left right)
    (crossParentCurrentEndpointRenaming left right)

public export
record CrossParentPermutationCorrespondenceWitness where
  constructor MkCrossParentPermutationCorrespondenceWitness
  crossParentLeft : CrossParentNamedTrace 2 0 3 1
  crossParentRight : CrossParentNamedTrace 3 1 2 0
  0 crossParentBlockerSameInputs : SameOrchestrationModuloGenerated
    DGamma.CP3StatementChecks.registrationTestNameEq
    DGamma.CP3StatementChecks.registrationTestKeyEq
    (crossParentTrace crossParentLeft) (crossParentTrace crossParentRight)

public export
crossParentPermutationCorrespondenceWitness :
  Maybe CrossParentPermutationCorrespondenceWitness
crossParentPermutationCorrespondenceWitness = do
  left <- buildCrossParentNamedTrace 2 0 3 1
  right <- buildCrossParentNamedTrace 3 1 2 0
  Just (MkCrossParentPermutationCorrespondenceWitness left right
    (crossParentSameInputs left right))

public export
crossParentPermutationCorrespondenceCheck : Bool
crossParentPermutationCorrespondenceCheck =
  case crossParentPermutationCorrespondenceWitness of
    Nothing => False
    Just witness => True

public export
crossParentPermutationRuntimeCheck : Bool
crossParentPermutationRuntimeCheck =
  case (buildCrossParentNamedTrace 2 0 3 1,
        buildCrossParentNamedTrace 3 1 2 0) of
    (Just left, Just right) =>
      quiet @{registrationTestNameEq} @{registrationTestKeyEq}
        (namedAfter (crossAdvance3 left)) &&
      quiet @{registrationTestNameEq} @{registrationTestKeyEq}
        (namedAfter (crossAdvance3 right)) &&
      noFailedFibers (namedAfter (crossAdvance3 left)) &&
      noFailedFibers (namedAfter (crossAdvance3 right)) &&
      isSupported @{registrationTestNameEq} @{registrationTestKeyEq} 0
        (namedAfter (crossAdvance3 left)) &&
      isSupported @{registrationTestNameEq} @{registrationTestKeyEq} 1
        (namedAfter (crossAdvance3 left)) &&
      isSupported @{registrationTestNameEq} @{registrationTestKeyEq} 2
        (namedAfter (crossAdvance3 left)) &&
      isSupported @{registrationTestNameEq} @{registrationTestKeyEq} 3
        (namedAfter (crossAdvance3 left))
    _ => False

||| Round-8 delay/divert/reopen regression.  The parent depends on ServiceA,
||| so retiring provider 0 diverts its first activation.  A replacement provider
||| later reopens the parent from the start of its iterator.
public export
episodeNameEq : DecEq Nat
episodeNameEq = %search

public export
episodeKeyEq : DecEq ToyKey
episodeKeyEq = %search

public export
episodeRegistrationStep : StepEffect ToyKey ToyValue ToyRuntime String
  [ServiceA] DGamma.CalculusChecks.toyEmptySpec
episodeRegistrationStep = MkStepEffect (Just 0)
  (\(OneDepValue service NoDepValues), before => Right (before, id))
  (\(OneDepValue service NoDepValues), before, after, undo, returned =>
    replace
      {p = \outcome => case outcome of
        Left _ => Unit
        Right (next, inverse) => inverse next = before}
      returned Refl)

public export
episodeChild : Component ToyKey ToyValue ToyRuntime String
episodeChild = MkComponent DGamma.CalculusChecks.toyEmptySpec
  DGamma.CalculusChecks.toyEmptySpec []

public export
episodeParent : Component ToyKey ToyValue ToyRuntime String
episodeParent = MkComponent DGamma.Section3Example.toySpecA
  DGamma.CalculusChecks.toyEmptySpec [episodeRegistrationStep]

public export
record EpisodeRootSource
  (root : Nat)
  (before : SystemState Nat ToyKey ToyValue ToyRuntime String) where
  constructor MkEpisodeRootSource
  episodeRootFiber : Fiber Nat ToyKey ToyValue ToyRuntime String
  0 episodeRootFound : lookupFiber
    @{DGamma.CP3StatementChecks.episodeNameEq} root (registry before) =
    Just episodeRootFiber
  0 episodeRootParent : fiberParent episodeRootFiber = Root

public export
findEpisodeRootSource : (root : Nat) ->
  (before : SystemState Nat ToyKey ToyValue ToyRuntime String) ->
  Maybe (EpisodeRootSource root before)
findEpisodeRootSource root before
  with (lookupFiber @{DGamma.CP3StatementChecks.episodeNameEq}
    root (registry before)) proof found
    findEpisodeRootSource root before | Nothing = Nothing
    findEpisodeRootSource root before | Just fiber
      with (fiberParent fiber) proof parentRole
        findEpisodeRootSource root before | Just fiber | Root =
          Just (MkEpisodeRootSource fiber found parentRole)
        findEpisodeRootSource root before | Just fiber | ChildOf parent = Nothing

public export
record EpisodeChildSource
  (child : Nat)
  (before : SystemState Nat ToyKey ToyValue ToyRuntime String) where
  constructor MkEpisodeChildSource
  episodeChildFiber : Fiber Nat ToyKey ToyValue ToyRuntime String
  episodeChildParent : Nat
  0 episodeChildFound : lookupFiber
    @{DGamma.CP3StatementChecks.episodeNameEq} child (registry before) =
    Just episodeChildFiber
  0 episodeChildParentRole : fiberParent episodeChildFiber =
    ChildOf episodeChildParent

public export
findEpisodeChildSource : (child : Nat) ->
  (before : SystemState Nat ToyKey ToyValue ToyRuntime String) ->
  Maybe (EpisodeChildSource child before)
findEpisodeChildSource child before
  with (lookupFiber @{DGamma.CP3StatementChecks.episodeNameEq}
    child (registry before)) proof found
    findEpisodeChildSource child before | Nothing = Nothing
    findEpisodeChildSource child before | Just fiber
      with (fiberParent fiber) proof parentRole
        findEpisodeChildSource child before | Just fiber | Root = Nothing
        findEpisodeChildSource child before | Just fiber | ChildOf parent =
          Just (MkEpisodeChildSource fiber parent found parentRole)

public export
record EpisodeCommonPrefix where
  constructor MkEpisodeCommonPrefix
  episodeInsert0 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq
    (OInsert 0 Root DGamma.CalculusChecks.providerComponent)
    DGamma.CalculusChecks.initialSystem
  episodeInsert1 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq
    (OInsert 1 Root DGamma.CP3StatementChecks.episodeParent)
    (namedAfter episodeInsert0)
  episodeBegin0 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LBegin 0)
    (namedAfter episodeInsert1)
  episodeAdvance0a : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LAdvance 0)
    (namedAfter episodeBegin0)
  episodeAdvance0b : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LAdvance 0)
    (namedAfter episodeAdvance0a)

public export
buildEpisodeCommonPrefix : Maybe EpisodeCommonPrefix
buildEpisodeCommonPrefix = do
  t0 <- checkedNamedFire episodeNameEq episodeKeyEq
    (OInsert 0 Root DGamma.CalculusChecks.providerComponent)
    DGamma.CalculusChecks.initialSystem
  t1 <- checkedNamedFire episodeNameEq episodeKeyEq
    (OInsert 1 Root episodeParent) (namedAfter t0)
  t2 <- checkedNamedFire episodeNameEq episodeKeyEq (LBegin 0) (namedAfter t1)
  t3 <- checkedNamedFire episodeNameEq episodeKeyEq (LAdvance 0) (namedAfter t2)
  t4 <- checkedNamedFire episodeNameEq episodeKeyEq (LAdvance 0) (namedAfter t3)
  Just (MkEpisodeCommonPrefix t0 t1 t2 t3 t4)

record EpisodeLeftTrace where
  constructor MkEpisodeLeftTrace
  leftEpisodePrefix : EpisodeCommonPrefix
  leftBegin1 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LBegin 1)
    (namedAfter (episodeAdvance0b leftEpisodePrefix))
  leftDeletedChild : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq
    (OInsert 2 (ChildOf 1) DGamma.CP3StatementChecks.episodeChild)
    (namedAfter leftBegin1)
  leftRetireChild2 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (ORetire 2)
    (namedAfter leftDeletedChild)
  leftRemoveChild2 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (ORemove 2)
    (namedAfter leftRetireChild2)
  leftRetire0 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (ORetire 0)
    (namedAfter leftRemoveChild2)
  leftLeave0 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LLeave 0)
    (namedAfter leftRetire0)
  leftDivert1 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LDivert 1)
    (namedAfter leftLeave0)
  leftUnload1 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LUnload 1)
    (namedAfter leftDivert1)
  leftUnload0 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LUnload 0)
    (namedAfter leftUnload1)
  leftRemove0 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (ORemove 0)
    (namedAfter leftUnload0)
  leftInsert3 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq
    (OInsert 3 Root DGamma.CalculusChecks.providerComponent)
    (namedAfter leftRemove0)
  leftBegin3 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LBegin 3)
    (namedAfter leftInsert3)
  leftAdvance3a : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LAdvance 3)
    (namedAfter leftBegin3)
  leftAdvance3b : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LAdvance 3)
    (namedAfter leftAdvance3a)
  leftReopen1 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LBegin 1)
    (namedAfter leftAdvance3b)
  leftSurvivingChild : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq
    (OInsert 4 (ChildOf 1) DGamma.CP3StatementChecks.episodeChild)
    (namedAfter leftReopen1)
  leftFinish1 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LAdvance 1)
    (namedAfter leftSurvivingChild)
  leftBegin4 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LBegin 4)
    (namedAfter leftFinish1)
  leftFinish4 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LAdvance 4)
    (namedAfter leftBegin4)
  leftRetireChildSource : EpisodeChildSource 2
    (namedAfter leftDeletedChild)
  leftRemoveChildSource : EpisodeChildSource 2
    (namedAfter leftRetireChild2)
  leftRetire0Source : EpisodeRootSource 0 (namedAfter leftRemoveChild2)
  leftRemove0Source : EpisodeRootSource 0 (namedAfter leftUnload0)

buildEpisodeLeftTrace : EpisodeCommonPrefix -> Maybe EpisodeLeftTrace
buildEpisodeLeftTrace common = do
  t5 <- checkedNamedFire episodeNameEq episodeKeyEq (LBegin 1)
    (namedAfter (episodeAdvance0b common))
  t6 <- checkedNamedFire episodeNameEq episodeKeyEq
    (OInsert 2 (ChildOf 1) episodeChild) (namedAfter t5)
  t7 <- checkedNamedFire episodeNameEq episodeKeyEq (ORetire 2) (namedAfter t6)
  t8 <- checkedNamedFire episodeNameEq episodeKeyEq (ORemove 2) (namedAfter t7)
  t9 <- checkedNamedFire episodeNameEq episodeKeyEq (ORetire 0) (namedAfter t8)
  t10 <- checkedNamedFire episodeNameEq episodeKeyEq (LLeave 0) (namedAfter t9)
  t11 <- checkedNamedFire episodeNameEq episodeKeyEq (LDivert 1) (namedAfter t10)
  t12 <- checkedNamedFire episodeNameEq episodeKeyEq (LUnload 1) (namedAfter t11)
  t13 <- checkedNamedFire episodeNameEq episodeKeyEq (LUnload 0) (namedAfter t12)
  t14 <- checkedNamedFire episodeNameEq episodeKeyEq (ORemove 0) (namedAfter t13)
  t15 <- checkedNamedFire episodeNameEq episodeKeyEq
    (OInsert 3 Root DGamma.CalculusChecks.providerComponent) (namedAfter t14)
  t16 <- checkedNamedFire episodeNameEq episodeKeyEq (LBegin 3) (namedAfter t15)
  t17 <- checkedNamedFire episodeNameEq episodeKeyEq (LAdvance 3) (namedAfter t16)
  t18 <- checkedNamedFire episodeNameEq episodeKeyEq (LAdvance 3) (namedAfter t17)
  t19 <- checkedNamedFire episodeNameEq episodeKeyEq (LBegin 1) (namedAfter t18)
  t20 <- checkedNamedFire episodeNameEq episodeKeyEq
    (OInsert 4 (ChildOf 1) episodeChild) (namedAfter t19)
  t21 <- checkedNamedFire episodeNameEq episodeKeyEq (LAdvance 1) (namedAfter t20)
  t22 <- checkedNamedFire episodeNameEq episodeKeyEq (LBegin 4) (namedAfter t21)
  t23 <- checkedNamedFire episodeNameEq episodeKeyEq (LAdvance 4) (namedAfter t22)
  childRetireSource <- findEpisodeChildSource 2 (namedAfter t6)
  childRemoveSource <- findEpisodeChildSource 2 (namedAfter t7)
  retire0Source <- findEpisodeRootSource 0 (namedAfter t8)
  remove0Source <- findEpisodeRootSource 0 (namedAfter t13)
  Just (MkEpisodeLeftTrace common t5 t6 t7 t8 t9 t10 t11 t12 t13 t14
    t15 t16 t17 t18 t19 t20 t21 t22 t23 childRetireSource
    childRemoveSource retire0Source remove0Source)

public export
record EpisodeRightTrace where
  constructor MkEpisodeRightTrace
  rightEpisodePrefix : EpisodeCommonPrefix
  rightRetire0 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (ORetire 0)
    (namedAfter (episodeAdvance0b rightEpisodePrefix))
  rightLeave0 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LLeave 0)
    (namedAfter rightRetire0)
  rightUnload0 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LUnload 0)
    (namedAfter rightLeave0)
  rightRemove0 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (ORemove 0)
    (namedAfter rightUnload0)
  rightInsert3 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq
    (OInsert 3 Root DGamma.CalculusChecks.providerComponent)
    (namedAfter rightRemove0)
  rightBegin3 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LBegin 3)
    (namedAfter rightInsert3)
  rightAdvance3a : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LAdvance 3)
    (namedAfter rightBegin3)
  rightAdvance3b : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LAdvance 3)
    (namedAfter rightAdvance3a)
  rightBegin1 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LBegin 1)
    (namedAfter rightAdvance3b)
  rightSurvivingChild : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq
    (OInsert 4 (ChildOf 1) DGamma.CP3StatementChecks.episodeChild)
    (namedAfter rightBegin1)
  rightFinish1 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LAdvance 1)
    (namedAfter rightSurvivingChild)
  rightBegin4 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LBegin 4)
    (namedAfter rightFinish1)
  rightFinish4 : CheckedNamedTransition DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq (LAdvance 4)
    (namedAfter rightBegin4)
  rightRetire0Source : EpisodeRootSource 0
    (namedAfter (episodeAdvance0b rightEpisodePrefix))
  rightRemove0Source : EpisodeRootSource 0 (namedAfter rightUnload0)

public export
buildEpisodeRightTrace : EpisodeCommonPrefix -> Maybe EpisodeRightTrace
buildEpisodeRightTrace common = do
  t5 <- checkedNamedFire episodeNameEq episodeKeyEq (ORetire 0)
    (namedAfter (episodeAdvance0b common))
  t6 <- checkedNamedFire episodeNameEq episodeKeyEq (LLeave 0) (namedAfter t5)
  t7 <- checkedNamedFire episodeNameEq episodeKeyEq (LUnload 0) (namedAfter t6)
  t8 <- checkedNamedFire episodeNameEq episodeKeyEq (ORemove 0) (namedAfter t7)
  t9 <- checkedNamedFire episodeNameEq episodeKeyEq
    (OInsert 3 Root DGamma.CalculusChecks.providerComponent) (namedAfter t8)
  t10 <- checkedNamedFire episodeNameEq episodeKeyEq (LBegin 3) (namedAfter t9)
  t11 <- checkedNamedFire episodeNameEq episodeKeyEq (LAdvance 3) (namedAfter t10)
  t12 <- checkedNamedFire episodeNameEq episodeKeyEq (LAdvance 3) (namedAfter t11)
  t13 <- checkedNamedFire episodeNameEq episodeKeyEq (LBegin 1) (namedAfter t12)
  t14 <- checkedNamedFire episodeNameEq episodeKeyEq
    (OInsert 4 (ChildOf 1) episodeChild) (namedAfter t13)
  t15 <- checkedNamedFire episodeNameEq episodeKeyEq (LAdvance 1) (namedAfter t14)
  t16 <- checkedNamedFire episodeNameEq episodeKeyEq (LBegin 4) (namedAfter t15)
  t17 <- checkedNamedFire episodeNameEq episodeKeyEq (LAdvance 4) (namedAfter t16)
  retire0Source <- findEpisodeRootSource 0
    (namedAfter (episodeAdvance0b common))
  remove0Source <- findEpisodeRootSource 0 (namedAfter t7)
  Just (MkEpisodeRightTrace common t5 t6 t7 t8 t9 t10 t11 t12 t13 t14
    t15 t16 t17 retire0Source remove0Source)

episodeLeftTail24 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (leftFinish4 trace)) (namedAfter (leftFinish4 trace))
episodeLeftTail24 trace = NoTransitions

episodeLeftTail23 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (leftBegin4 trace)) (namedAfter (leftFinish4 trace))
episodeLeftTail23 trace = MoreTransitions (namedTransition (leftFinish4 trace))
  (episodeLeftTail24 trace)

episodeLeftTail22 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (leftFinish1 trace)) (namedAfter (leftFinish4 trace))
episodeLeftTail22 trace = MoreTransitions (namedTransition (leftBegin4 trace))
  (episodeLeftTail23 trace)

episodeLeftTail21 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (leftSurvivingChild trace)) (namedAfter (leftFinish4 trace))
episodeLeftTail21 trace = MoreTransitions (namedTransition (leftFinish1 trace))
  (episodeLeftTail22 trace)

episodeLeftTail20 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (leftReopen1 trace)) (namedAfter (leftFinish4 trace))
episodeLeftTail20 trace = MoreTransitions (namedTransition (leftSurvivingChild trace))
  (episodeLeftTail21 trace)

episodeLeftTail19 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (leftAdvance3b trace)) (namedAfter (leftFinish4 trace))
episodeLeftTail19 trace = MoreTransitions (namedTransition (leftReopen1 trace))
  (episodeLeftTail20 trace)

episodeLeftTail18 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (leftAdvance3a trace)) (namedAfter (leftFinish4 trace))
episodeLeftTail18 trace = MoreTransitions (namedTransition (leftAdvance3b trace))
  (episodeLeftTail19 trace)

episodeLeftTail17 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (leftBegin3 trace)) (namedAfter (leftFinish4 trace))
episodeLeftTail17 trace = MoreTransitions (namedTransition (leftAdvance3a trace))
  (episodeLeftTail18 trace)

episodeLeftTail16 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (leftInsert3 trace)) (namedAfter (leftFinish4 trace))
episodeLeftTail16 trace = MoreTransitions (namedTransition (leftBegin3 trace))
  (episodeLeftTail17 trace)

episodeLeftTail15 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (leftRemove0 trace)) (namedAfter (leftFinish4 trace))
episodeLeftTail15 trace = MoreTransitions (namedTransition (leftInsert3 trace))
  (episodeLeftTail16 trace)

episodeLeftTail14 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (leftUnload0 trace)) (namedAfter (leftFinish4 trace))
episodeLeftTail14 trace = MoreTransitions (namedTransition (leftRemove0 trace))
  (episodeLeftTail15 trace)

episodeLeftTail13 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (leftUnload1 trace)) (namedAfter (leftFinish4 trace))
episodeLeftTail13 trace = MoreTransitions (namedTransition (leftUnload0 trace))
  (episodeLeftTail14 trace)

episodeLeftTail12 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (leftDivert1 trace)) (namedAfter (leftFinish4 trace))
episodeLeftTail12 trace = MoreTransitions (namedTransition (leftUnload1 trace))
  (episodeLeftTail13 trace)

episodeLeftTail11 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (leftLeave0 trace)) (namedAfter (leftFinish4 trace))
episodeLeftTail11 trace = MoreTransitions (namedTransition (leftDivert1 trace))
  (episodeLeftTail12 trace)

episodeLeftTail10 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (leftRetire0 trace)) (namedAfter (leftFinish4 trace))
episodeLeftTail10 trace = MoreTransitions (namedTransition (leftLeave0 trace))
  (episodeLeftTail11 trace)

episodeLeftTail9 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (leftRemoveChild2 trace)) (namedAfter (leftFinish4 trace))
episodeLeftTail9 trace = MoreTransitions (namedTransition (leftRetire0 trace))
  (episodeLeftTail10 trace)

episodeLeftTail8 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (leftRetireChild2 trace)) (namedAfter (leftFinish4 trace))
episodeLeftTail8 trace = MoreTransitions (namedTransition (leftRemoveChild2 trace))
  (episodeLeftTail9 trace)

episodeLeftTail7 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (leftDeletedChild trace)) (namedAfter (leftFinish4 trace))
episodeLeftTail7 trace = MoreTransitions (namedTransition (leftRetireChild2 trace))
  (episodeLeftTail8 trace)

episodeLeftTail6 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (leftBegin1 trace)) (namedAfter (leftFinish4 trace))
episodeLeftTail6 trace = MoreTransitions (namedTransition (leftDeletedChild trace))
  (episodeLeftTail7 trace)

episodeLeftTail5 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (episodeAdvance0b (leftEpisodePrefix trace))) (namedAfter (leftFinish4 trace))
episodeLeftTail5 trace = MoreTransitions (namedTransition (leftBegin1 trace))
  (episodeLeftTail6 trace)

episodeLeftTail4 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (episodeAdvance0a (leftEpisodePrefix trace))) (namedAfter (leftFinish4 trace))
episodeLeftTail4 trace = MoreTransitions (namedTransition (episodeAdvance0b (leftEpisodePrefix trace)))
  (episodeLeftTail5 trace)

episodeLeftTail3 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (episodeBegin0 (leftEpisodePrefix trace))) (namedAfter (leftFinish4 trace))
episodeLeftTail3 trace = MoreTransitions (namedTransition (episodeAdvance0a (leftEpisodePrefix trace)))
  (episodeLeftTail4 trace)

episodeLeftTail2 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (episodeInsert1 (leftEpisodePrefix trace))) (namedAfter (leftFinish4 trace))
episodeLeftTail2 trace = MoreTransitions (namedTransition (episodeBegin0 (leftEpisodePrefix trace)))
  (episodeLeftTail3 trace)

episodeLeftTail1 : (trace : EpisodeLeftTrace) ->
  Transitions (namedAfter (episodeInsert0 (leftEpisodePrefix trace))) (namedAfter (leftFinish4 trace))
episodeLeftTail1 trace = MoreTransitions (namedTransition (episodeInsert1 (leftEpisodePrefix trace)))
  (episodeLeftTail2 trace)

public export
episodeLeftTrace : (trace : EpisodeLeftTrace) ->
  Transitions DGamma.CalculusChecks.initialSystem (namedAfter (leftFinish4 trace))
episodeLeftTrace trace = MoreTransitions (namedTransition (episodeInsert0 (leftEpisodePrefix trace)))
  (episodeLeftTail1 trace)

public export
episodeRightTail18 : (trace : EpisodeRightTrace) ->
  Transitions (namedAfter (rightFinish4 trace)) (namedAfter (rightFinish4 trace))
episodeRightTail18 trace = NoTransitions

public export
episodeRightTail17 : (trace : EpisodeRightTrace) ->
  Transitions (namedAfter (rightBegin4 trace)) (namedAfter (rightFinish4 trace))
episodeRightTail17 trace = MoreTransitions (namedTransition (rightFinish4 trace))
  (episodeRightTail18 trace)

public export
episodeRightTail16 : (trace : EpisodeRightTrace) ->
  Transitions (namedAfter (rightFinish1 trace)) (namedAfter (rightFinish4 trace))
episodeRightTail16 trace = MoreTransitions (namedTransition (rightBegin4 trace))
  (episodeRightTail17 trace)

public export
episodeRightTail15 : (trace : EpisodeRightTrace) ->
  Transitions (namedAfter (rightSurvivingChild trace)) (namedAfter (rightFinish4 trace))
episodeRightTail15 trace = MoreTransitions (namedTransition (rightFinish1 trace))
  (episodeRightTail16 trace)

public export
episodeRightTail14 : (trace : EpisodeRightTrace) ->
  Transitions (namedAfter (rightBegin1 trace)) (namedAfter (rightFinish4 trace))
episodeRightTail14 trace = MoreTransitions (namedTransition (rightSurvivingChild trace))
  (episodeRightTail15 trace)

public export
episodeRightTail13 : (trace : EpisodeRightTrace) ->
  Transitions (namedAfter (rightAdvance3b trace)) (namedAfter (rightFinish4 trace))
episodeRightTail13 trace = MoreTransitions (namedTransition (rightBegin1 trace))
  (episodeRightTail14 trace)

public export
episodeRightTail12 : (trace : EpisodeRightTrace) ->
  Transitions (namedAfter (rightAdvance3a trace)) (namedAfter (rightFinish4 trace))
episodeRightTail12 trace = MoreTransitions (namedTransition (rightAdvance3b trace))
  (episodeRightTail13 trace)

public export
episodeRightTail11 : (trace : EpisodeRightTrace) ->
  Transitions (namedAfter (rightBegin3 trace)) (namedAfter (rightFinish4 trace))
episodeRightTail11 trace = MoreTransitions (namedTransition (rightAdvance3a trace))
  (episodeRightTail12 trace)

public export
episodeRightTail10 : (trace : EpisodeRightTrace) ->
  Transitions (namedAfter (rightInsert3 trace)) (namedAfter (rightFinish4 trace))
episodeRightTail10 trace = MoreTransitions (namedTransition (rightBegin3 trace))
  (episodeRightTail11 trace)

public export
episodeRightTail9 : (trace : EpisodeRightTrace) ->
  Transitions (namedAfter (rightRemove0 trace)) (namedAfter (rightFinish4 trace))
episodeRightTail9 trace = MoreTransitions (namedTransition (rightInsert3 trace))
  (episodeRightTail10 trace)

public export
episodeRightTail8 : (trace : EpisodeRightTrace) ->
  Transitions (namedAfter (rightUnload0 trace)) (namedAfter (rightFinish4 trace))
episodeRightTail8 trace = MoreTransitions (namedTransition (rightRemove0 trace))
  (episodeRightTail9 trace)

public export
episodeRightTail7 : (trace : EpisodeRightTrace) ->
  Transitions (namedAfter (rightLeave0 trace)) (namedAfter (rightFinish4 trace))
episodeRightTail7 trace = MoreTransitions (namedTransition (rightUnload0 trace))
  (episodeRightTail8 trace)

public export
episodeRightTail6 : (trace : EpisodeRightTrace) ->
  Transitions (namedAfter (rightRetire0 trace)) (namedAfter (rightFinish4 trace))
episodeRightTail6 trace = MoreTransitions (namedTransition (rightLeave0 trace))
  (episodeRightTail7 trace)

public export
episodeRightTail5 : (trace : EpisodeRightTrace) ->
  Transitions (namedAfter (episodeAdvance0b (rightEpisodePrefix trace))) (namedAfter (rightFinish4 trace))
episodeRightTail5 trace = MoreTransitions (namedTransition (rightRetire0 trace))
  (episodeRightTail6 trace)

public export
episodeRightTail4 : (trace : EpisodeRightTrace) ->
  Transitions (namedAfter (episodeAdvance0a (rightEpisodePrefix trace))) (namedAfter (rightFinish4 trace))
episodeRightTail4 trace = MoreTransitions (namedTransition (episodeAdvance0b (rightEpisodePrefix trace)))
  (episodeRightTail5 trace)

public export
episodeRightTail3 : (trace : EpisodeRightTrace) ->
  Transitions (namedAfter (episodeBegin0 (rightEpisodePrefix trace))) (namedAfter (rightFinish4 trace))
episodeRightTail3 trace = MoreTransitions (namedTransition (episodeAdvance0a (rightEpisodePrefix trace)))
  (episodeRightTail4 trace)

public export
episodeRightTail2 : (trace : EpisodeRightTrace) ->
  Transitions (namedAfter (episodeInsert1 (rightEpisodePrefix trace))) (namedAfter (rightFinish4 trace))
episodeRightTail2 trace = MoreTransitions (namedTransition (episodeBegin0 (rightEpisodePrefix trace)))
  (episodeRightTail3 trace)

public export
episodeRightTail1 : (trace : EpisodeRightTrace) ->
  Transitions (namedAfter (episodeInsert0 (rightEpisodePrefix trace))) (namedAfter (rightFinish4 trace))
episodeRightTail1 trace = MoreTransitions (namedTransition (episodeInsert1 (rightEpisodePrefix trace)))
  (episodeRightTail2 trace)

public export
episodeRightTrace : (trace : EpisodeRightTrace) ->
  Transitions DGamma.CalculusChecks.initialSystem (namedAfter (rightFinish4 trace))
episodeRightTrace trace = MoreTransitions (namedTransition (episodeInsert0 (rightEpisodePrefix trace)))
  (episodeRightTail1 trace)

swapNineFifteen : Nat -> Nat
swapNineFifteen 9 = 15
swapNineFifteen 15 = 9
swapNineFifteen n = n

0 swapNineFifteenInvolutive : (n : Nat) -> swapNineFifteen (swapNineFifteen n) = n
swapNineFifteenInvolutive 0 = Refl
swapNineFifteenInvolutive 1 = Refl
swapNineFifteenInvolutive 2 = Refl
swapNineFifteenInvolutive 3 = Refl
swapNineFifteenInvolutive 4 = Refl
swapNineFifteenInvolutive 5 = Refl
swapNineFifteenInvolutive 6 = Refl
swapNineFifteenInvolutive 7 = Refl
swapNineFifteenInvolutive 8 = Refl
swapNineFifteenInvolutive 9 = Refl
swapNineFifteenInvolutive 10 = Refl
swapNineFifteenInvolutive 11 = Refl
swapNineFifteenInvolutive 12 = Refl
swapNineFifteenInvolutive 13 = Refl
swapNineFifteenInvolutive 14 = Refl
swapNineFifteenInvolutive 15 = Refl
swapNineFifteenInvolutive (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S later)))))))))))))))) = Refl

swapFourteenTwenty : Nat -> Nat
swapFourteenTwenty 14 = 20
swapFourteenTwenty 20 = 14
swapFourteenTwenty n = n

0 swapFourteenTwentyInvolutive : (n : Nat) -> swapFourteenTwenty (swapFourteenTwenty n) = n
swapFourteenTwentyInvolutive 0 = Refl
swapFourteenTwentyInvolutive 1 = Refl
swapFourteenTwentyInvolutive 2 = Refl
swapFourteenTwentyInvolutive 3 = Refl
swapFourteenTwentyInvolutive 4 = Refl
swapFourteenTwentyInvolutive 5 = Refl
swapFourteenTwentyInvolutive 6 = Refl
swapFourteenTwentyInvolutive 7 = Refl
swapFourteenTwentyInvolutive 8 = Refl
swapFourteenTwentyInvolutive 9 = Refl
swapFourteenTwentyInvolutive 10 = Refl
swapFourteenTwentyInvolutive 11 = Refl
swapFourteenTwentyInvolutive 12 = Refl
swapFourteenTwentyInvolutive 13 = Refl
swapFourteenTwentyInvolutive 14 = Refl
swapFourteenTwentyInvolutive 15 = Refl
swapFourteenTwentyInvolutive 16 = Refl
swapFourteenTwentyInvolutive 17 = Refl
swapFourteenTwentyInvolutive 18 = Refl
swapFourteenTwentyInvolutive 19 = Refl
swapFourteenTwentyInvolutive 20 = Refl
swapFourteenTwentyInvolutive (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S later))))))))))))))))))))) = Refl

episodeGenerationMap : RegistrationGeneration Nat -> RegistrationGeneration Nat
episodeGenerationMap (MkRegistrationGeneration 3 ordinal) =
  MkRegistrationGeneration 3 (swapNineFifteen ordinal)
episodeGenerationMap (MkRegistrationGeneration 4 ordinal) =
  MkRegistrationGeneration 4 (swapFourteenTwenty ordinal)
episodeGenerationMap generation = generation

0 episodeGenerationMapInvolutive : (generation : RegistrationGeneration Nat) ->
  episodeGenerationMap (episodeGenerationMap generation) = generation
episodeGenerationMapInvolutive (MkRegistrationGeneration Z ordinal) = Refl
episodeGenerationMapInvolutive (MkRegistrationGeneration (S Z) ordinal) = Refl
episodeGenerationMapInvolutive
  (MkRegistrationGeneration (S (S Z)) ordinal) = Refl
episodeGenerationMapInvolutive
  (MkRegistrationGeneration (S (S (S Z))) ordinal) =
    cong (MkRegistrationGeneration 3) (swapNineFifteenInvolutive ordinal)
episodeGenerationMapInvolutive
  (MkRegistrationGeneration (S (S (S (S Z)))) ordinal) =
    cong (MkRegistrationGeneration 4) (swapFourteenTwentyInvolutive ordinal)
episodeGenerationMapInvolutive
  (MkRegistrationGeneration (S (S (S (S (S later))))) ordinal) = Refl

public export
episodeBoundaryGenerationBijection : RegistrationGenerationBijection Nat
episodeBoundaryGenerationBijection = MkRegistrationGenerationBijection
  episodeGenerationMap episodeGenerationMap episodeGenerationMapInvolutive
  episodeGenerationMapInvolutive

episodeIndexAdvance : Nat ->
  Action Nat ToyKey ToyValue ToyRuntime String -> RegistrationIndexState Nat ->
  RegistrationIndexState Nat
episodeIndexAdvance = DGamma.CP3.advanceRegistrationIndex
  @{DGamma.CP3StatementChecks.episodeNameEq}

episodeIndexSurvive : Nat -> (child, parent : Nat) ->
  Component ToyKey ToyValue ToyRuntime String -> RegistrationIndexState Nat ->
  RegistrationIndexState Nat
episodeIndexSurvive = DGamma.CP3.advanceSurvivingRegistrationIndex
  @{DGamma.CP3StatementChecks.episodeNameEq}

episodeIndexDelete : Nat -> (child, parent : Nat) ->
  Component ToyKey ToyValue ToyRuntime String -> RegistrationIndexState Nat ->
  RegistrationIndexState Nat
episodeIndexDelete = DGamma.CP3.advanceDeletedRegistrationIndex
  @{DGamma.CP3StatementChecks.episodeNameEq}

episodeCommonIndex : RegistrationIndexState Nat
episodeCommonIndex =
  let i0 = episodeIndexAdvance 0
        (OInsert 0 Root DGamma.CalculusChecks.providerComponent)
        DGamma.CP3.emptyRegistrationIndex
      i1 = episodeIndexAdvance 1 (OInsert 1 Root episodeParent) i0
      i2 = episodeIndexAdvance 2 (LBegin 0) i1
      i3 = episodeIndexAdvance 3 (LAdvance 0) i2 in
    episodeIndexAdvance 4 (LAdvance 0) i3

episodeLeftDeletedIndex : RegistrationIndexState Nat
episodeLeftDeletedIndex = episodeIndexAdvance 5 (LBegin 1) episodeCommonIndex

episodeLeftSurvivingIndex : RegistrationIndexState Nat
episodeLeftSurvivingIndex =
  let i7 = episodeIndexAdvance 7 (ORetire 2)
        (episodeIndexDelete 6 2 1 episodeChild episodeLeftDeletedIndex)
      i8 = episodeIndexAdvance 8 (ORemove 2) i7
      i9 = episodeIndexAdvance 9 (ORetire 0) i8
      i10 = episodeIndexAdvance 10 (LLeave 0) i9
      i11 = episodeIndexAdvance 11 (LDivert 1) i10
      i12 = episodeIndexAdvance 12 (LUnload 1) i11
      i13 = episodeIndexAdvance 13 (LUnload 0) i12
      i14 = episodeIndexAdvance 14 (ORemove 0) i13
      i15 = episodeIndexAdvance 15
        (OInsert 3 Root DGamma.CalculusChecks.providerComponent) i14
      i16 = episodeIndexAdvance 16 (LBegin 3) i15
      i17 = episodeIndexAdvance 17 (LAdvance 3) i16
      i18 = episodeIndexAdvance 18 (LAdvance 3) i17 in
    episodeIndexAdvance 19 (LBegin 1) i18

episodeLeftFinalIndex : RegistrationIndexState Nat
episodeLeftFinalIndex =
  let i20 = episodeIndexSurvive 20 4 1 episodeChild
        episodeLeftSurvivingIndex
      i21 = episodeIndexAdvance 21 (LAdvance 1) i20
      i22 = episodeIndexAdvance 22 (LBegin 4) i21 in
    episodeIndexAdvance 23 (LAdvance 4) i22

episodeRightSurvivingIndex : RegistrationIndexState Nat
episodeRightSurvivingIndex =
  let i5 = episodeIndexAdvance 5 (ORetire 0) episodeCommonIndex
      i6 = episodeIndexAdvance 6 (LLeave 0) i5
      i7 = episodeIndexAdvance 7 (LUnload 0) i6
      i8 = episodeIndexAdvance 8 (ORemove 0) i7
      i9 = episodeIndexAdvance 9
        (OInsert 3 Root DGamma.CalculusChecks.providerComponent) i8
      i10 = episodeIndexAdvance 10 (LBegin 3) i9
      i11 = episodeIndexAdvance 11 (LAdvance 3) i10
      i12 = episodeIndexAdvance 12 (LAdvance 3) i11 in
    episodeIndexAdvance 13 (LBegin 1) i12

episodeRightFinalIndex : RegistrationIndexState Nat
episodeRightFinalIndex =
  let i14 = episodeIndexSurvive 14 4 1 episodeChild
        episodeRightSurvivingIndex
      i15 = episodeIndexAdvance 15 (LAdvance 1) i14
      i16 = episodeIndexAdvance 16 (LBegin 4) i15 in
    episodeIndexAdvance 17 (LAdvance 4) i16

0 episodeDeletedBirthCloses : (left : EpisodeLeftTrace) ->
  ActionOccurs (LUnload 1) (episodeLeftTail7 left)
episodeDeletedBirthCloses left =
  ActionOccursLater (namedTransition (leftRetireChild2 left))
    (episodeLeftTail8 left)
  (ActionOccursLater (namedTransition (leftRemoveChild2 left))
    (episodeLeftTail9 left)
  (ActionOccursLater (namedTransition (leftRetire0 left))
    (episodeLeftTail10 left)
  (ActionOccursLater (namedTransition (leftLeave0 left))
    (episodeLeftTail11 left)
  (ActionOccursLater (namedTransition (leftDivert1 left))
    (episodeLeftTail12 left)
  (ActionOccursHere (namedTransition (leftUnload1 left))
    (episodeLeftTail13 left) (namedAction (leftUnload1 left)))))))

0 episodeLeftDeletedClassification : (left : EpisodeLeftTrace) ->
  DeletedClosingRegistration
    (registrationEventAt @{DGamma.CP3StatementChecks.episodeNameEq} 6
      DGamma.CP3StatementChecks.episodeLeftDeletedIndex 2 1
      DGamma.CP3StatementChecks.episodeChild)
    (episodeLeftTail7 left)
episodeLeftDeletedClassification left = MkDeletedClosingRegistration
  (MkRegistrationActivation (MkRegistrationGeneration 1 1) 5) Refl
  (episodeDeletedBirthCloses left)

0 episodeLeftParentRemainsOpen : (left : EpisodeLeftTrace) ->
  NoParentUnload 1 (episodeLeftTail21 left)
episodeLeftParentRemainsOpen left =
  NoParentUnloadStep (namedTransition (leftFinish1 left))
    (episodeLeftTail22 left)
    (namedTransitionNotUnload (leftFinish1 left) (\Refl impossible))
  (NoParentUnloadStep (namedTransition (leftBegin4 left))
    (episodeLeftTail23 left)
    (namedTransitionNotUnload (leftBegin4 left) (\Refl impossible))
  (NoParentUnloadStep (namedTransition (leftFinish4 left))
    (episodeLeftTail24 left)
    (namedTransitionNotUnload (leftFinish4 left) (\Refl impossible))
    NoParentUnloadEnd))

0 episodeRightParentRemainsOpen : (right : EpisodeRightTrace) ->
  NoParentUnload 1 (episodeRightTail15 right)
episodeRightParentRemainsOpen right =
  NoParentUnloadStep (namedTransition (rightFinish1 right))
    (episodeRightTail16 right)
    (namedTransitionNotUnload (rightFinish1 right) (\Refl impossible))
  (NoParentUnloadStep (namedTransition (rightBegin4 right))
    (episodeRightTail17 right)
    (namedTransitionNotUnload (rightBegin4 right) (\Refl impossible))
  (NoParentUnloadStep (namedTransition (rightFinish4 right))
    (episodeRightTail18 right)
    (namedTransitionNotUnload (rightFinish4 right) (\Refl impossible))
    NoParentUnloadEnd))

0 episodeLeftSurvivingClassification : (left : EpisodeLeftTrace) ->
  SurvivingRegistration
    (registrationEventAt @{DGamma.CP3StatementChecks.episodeNameEq} 20
      DGamma.CP3StatementChecks.episodeLeftSurvivingIndex 4 1
      DGamma.CP3StatementChecks.episodeChild)
    (episodeLeftTail21 left)
episodeLeftSurvivingClassification left = MkSurvivingRegistration
  (MkRegistrationActivation (MkRegistrationGeneration 1 1) 19) Refl
  (episodeLeftParentRemainsOpen left)

0 episodeRightSurvivingClassification : (right : EpisodeRightTrace) ->
  SurvivingRegistration
    (registrationEventAt @{DGamma.CP3StatementChecks.episodeNameEq} 14
      DGamma.CP3StatementChecks.episodeRightSurvivingIndex 4 1
      DGamma.CP3StatementChecks.episodeChild)
    (episodeRightTail15 right)
episodeRightSurvivingClassification right = MkSurvivingRegistration
  (MkRegistrationActivation (MkRegistrationGeneration 1 1) 13) Refl
  (episodeRightParentRemainsOpen right)

||| The old lifetime counter assigned the reopened left birth position one.
||| Closed-episode exclusion plus the L-Begin activation stamp makes both first
||| surviving yields position zero.
public export
0 episodeBoundaryPositionsReset :
  (eventChildPosition
    (registrationEventAt @{DGamma.CP3StatementChecks.episodeNameEq} 20
      DGamma.CP3StatementChecks.episodeLeftSurvivingIndex 4 1
      DGamma.CP3StatementChecks.episodeChild) = 0,
   eventChildPosition
    (registrationEventAt @{DGamma.CP3StatementChecks.episodeNameEq} 14
      DGamma.CP3StatementChecks.episodeRightSurvivingIndex 4 1
      DGamma.CP3StatementChecks.episodeChild) = 0)
episodeBoundaryPositionsReset = (Refl, Refl)

0 episodeBoundaryTraceCorrespondence :
  (left : EpisodeLeftTrace) -> (right : EpisodeRightTrace) ->
  RegistrationTraceCorrespondence DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeBoundaryGenerationBijection
    0 DGamma.CP3.emptyRegistrationIndex (episodeLeftTrace left)
      DGamma.CP3StatementChecks.episodeLeftFinalIndex
    0 DGamma.CP3.emptyRegistrationIndex (episodeRightTrace right)
      DGamma.CP3StatementChecks.episodeRightFinalIndex [] []
episodeBoundaryTraceCorrespondence left right =
  SkipLeftNonRegistration (OInsert 0 Root DGamma.CalculusChecks.providerComponent)
    (namedTransition (episodeInsert0 (leftEpisodePrefix left))) (episodeLeftTail1 left)
    (namedAction (episodeInsert0 (leftEpisodePrefix left))) Refl
  (SkipLeftNonRegistration (OInsert 1 Root episodeParent)
    (namedTransition (episodeInsert1 (leftEpisodePrefix left))) (episodeLeftTail2 left)
    (namedAction (episodeInsert1 (leftEpisodePrefix left))) Refl
  (SkipLeftNonRegistration (LBegin 0)
    (namedTransition (episodeBegin0 (leftEpisodePrefix left))) (episodeLeftTail3 left)
    (namedAction (episodeBegin0 (leftEpisodePrefix left))) Refl
  (SkipLeftNonRegistration (LAdvance 0)
    (namedTransition (episodeAdvance0a (leftEpisodePrefix left))) (episodeLeftTail4 left)
    (namedAction (episodeAdvance0a (leftEpisodePrefix left))) Refl
  (SkipLeftNonRegistration (LAdvance 0)
    (namedTransition (episodeAdvance0b (leftEpisodePrefix left))) (episodeLeftTail5 left)
    (namedAction (episodeAdvance0b (leftEpisodePrefix left))) Refl
  (SkipLeftNonRegistration (LBegin 1)
    (namedTransition (leftBegin1 left)) (episodeLeftTail6 left)
    (namedAction (leftBegin1 left)) Refl
  (DiscardLeftDeletedRegistration
    (namedTransition (leftDeletedChild left)) (episodeLeftTail7 left)
    (namedAction (leftDeletedChild left)) (episodeLeftDeletedClassification left)
  (SkipLeftNonRegistration (ORetire 2)
    (namedTransition (leftRetireChild2 left)) (episodeLeftTail8 left)
    (namedAction (leftRetireChild2 left)) Refl
  (SkipLeftNonRegistration (ORemove 2)
    (namedTransition (leftRemoveChild2 left)) (episodeLeftTail9 left)
    (namedAction (leftRemoveChild2 left)) Refl
  (SkipLeftNonRegistration (ORetire 0)
    (namedTransition (leftRetire0 left)) (episodeLeftTail10 left)
    (namedAction (leftRetire0 left)) Refl
  (SkipLeftNonRegistration (LLeave 0)
    (namedTransition (leftLeave0 left)) (episodeLeftTail11 left)
    (namedAction (leftLeave0 left)) Refl
  (SkipLeftNonRegistration (LDivert 1)
    (namedTransition (leftDivert1 left)) (episodeLeftTail12 left)
    (namedAction (leftDivert1 left)) Refl
  (SkipLeftNonRegistration (LUnload 1)
    (namedTransition (leftUnload1 left)) (episodeLeftTail13 left)
    (namedAction (leftUnload1 left)) Refl
  (SkipLeftNonRegistration (LUnload 0)
    (namedTransition (leftUnload0 left)) (episodeLeftTail14 left)
    (namedAction (leftUnload0 left)) Refl
  (SkipLeftNonRegistration (ORemove 0)
    (namedTransition (leftRemove0 left)) (episodeLeftTail15 left)
    (namedAction (leftRemove0 left)) Refl
  (SkipLeftNonRegistration (OInsert 3 Root DGamma.CalculusChecks.providerComponent)
    (namedTransition (leftInsert3 left)) (episodeLeftTail16 left)
    (namedAction (leftInsert3 left)) Refl
  (SkipLeftNonRegistration (LBegin 3)
    (namedTransition (leftBegin3 left)) (episodeLeftTail17 left)
    (namedAction (leftBegin3 left)) Refl
  (SkipLeftNonRegistration (LAdvance 3)
    (namedTransition (leftAdvance3a left)) (episodeLeftTail18 left)
    (namedAction (leftAdvance3a left)) Refl
  (SkipLeftNonRegistration (LAdvance 3)
    (namedTransition (leftAdvance3b left)) (episodeLeftTail19 left)
    (namedAction (leftAdvance3b left)) Refl
  (SkipLeftNonRegistration (LBegin 1)
    (namedTransition (leftReopen1 left)) (episodeLeftTail20 left)
    (namedAction (leftReopen1 left)) Refl
  (QueueLeftGeneratedRegistration
    (namedTransition (leftSurvivingChild left)) (episodeLeftTail21 left)
    (namedAction (leftSurvivingChild left)) (episodeLeftSurvivingClassification left)
  (SkipLeftNonRegistration (LAdvance 1)
    (namedTransition (leftFinish1 left)) (episodeLeftTail22 left)
    (namedAction (leftFinish1 left)) Refl
  (SkipLeftNonRegistration (LBegin 4)
    (namedTransition (leftBegin4 left)) (episodeLeftTail23 left)
    (namedAction (leftBegin4 left)) Refl
  (SkipLeftNonRegistration (LAdvance 4)
    (namedTransition (leftFinish4 left)) (episodeLeftTail24 left)
    (namedAction (leftFinish4 left)) Refl
  (SkipRightNonRegistration (OInsert 0 Root DGamma.CalculusChecks.providerComponent)
    (namedTransition (episodeInsert0 (rightEpisodePrefix right))) (episodeRightTail1 right)
    (namedAction (episodeInsert0 (rightEpisodePrefix right))) Refl
  (SkipRightNonRegistration (OInsert 1 Root episodeParent)
    (namedTransition (episodeInsert1 (rightEpisodePrefix right))) (episodeRightTail2 right)
    (namedAction (episodeInsert1 (rightEpisodePrefix right))) Refl
  (SkipRightNonRegistration (LBegin 0)
    (namedTransition (episodeBegin0 (rightEpisodePrefix right))) (episodeRightTail3 right)
    (namedAction (episodeBegin0 (rightEpisodePrefix right))) Refl
  (SkipRightNonRegistration (LAdvance 0)
    (namedTransition (episodeAdvance0a (rightEpisodePrefix right))) (episodeRightTail4 right)
    (namedAction (episodeAdvance0a (rightEpisodePrefix right))) Refl
  (SkipRightNonRegistration (LAdvance 0)
    (namedTransition (episodeAdvance0b (rightEpisodePrefix right))) (episodeRightTail5 right)
    (namedAction (episodeAdvance0b (rightEpisodePrefix right))) Refl
  (SkipRightNonRegistration (ORetire 0)
    (namedTransition (rightRetire0 right)) (episodeRightTail6 right)
    (namedAction (rightRetire0 right)) Refl
  (SkipRightNonRegistration (LLeave 0)
    (namedTransition (rightLeave0 right)) (episodeRightTail7 right)
    (namedAction (rightLeave0 right)) Refl
  (SkipRightNonRegistration (LUnload 0)
    (namedTransition (rightUnload0 right)) (episodeRightTail8 right)
    (namedAction (rightUnload0 right)) Refl
  (SkipRightNonRegistration (ORemove 0)
    (namedTransition (rightRemove0 right)) (episodeRightTail9 right)
    (namedAction (rightRemove0 right)) Refl
  (SkipRightNonRegistration (OInsert 3 Root DGamma.CalculusChecks.providerComponent)
    (namedTransition (rightInsert3 right)) (episodeRightTail10 right)
    (namedAction (rightInsert3 right)) Refl
  (SkipRightNonRegistration (LBegin 3)
    (namedTransition (rightBegin3 right)) (episodeRightTail11 right)
    (namedAction (rightBegin3 right)) Refl
  (SkipRightNonRegistration (LAdvance 3)
    (namedTransition (rightAdvance3a right)) (episodeRightTail12 right)
    (namedAction (rightAdvance3a right)) Refl
  (SkipRightNonRegistration (LAdvance 3)
    (namedTransition (rightAdvance3b right)) (episodeRightTail13 right)
    (namedAction (rightAdvance3b right)) Refl
  (SkipRightNonRegistration (LBegin 1)
    (namedTransition (rightBegin1 right)) (episodeRightTail14 right)
    (namedAction (rightBegin1 right)) Refl
  (MatchRightWithPendingLeft
    (namedTransition (rightSurvivingChild right)) (episodeRightTail15 right)
    (namedAction (rightSurvivingChild right)) (episodeRightSurvivingClassification right) []
    (registrationEventAt @{DGamma.CP3StatementChecks.episodeNameEq} 20
      DGamma.CP3StatementChecks.episodeLeftSurvivingIndex 4 1 episodeChild) []
    (MkRegistrationEventMatch Refl
      (MkRegistrationActivation (MkRegistrationGeneration 1 1) 19)
      (MkRegistrationActivation (MkRegistrationGeneration 1 1) 13)
      Refl Refl Refl Refl Refl)
  (SkipRightNonRegistration (LAdvance 1)
    (namedTransition (rightFinish1 right)) (episodeRightTail16 right)
    (namedAction (rightFinish1 right)) Refl
  (SkipRightNonRegistration (LBegin 4)
    (namedTransition (rightBegin4 right)) (episodeRightTail17 right)
    (namedAction (rightBegin4 right)) Refl
  (SkipRightNonRegistration (LAdvance 4)
    (namedTransition (rightFinish4 right)) (episodeRightTail18 right)
    (namedAction (rightFinish4 right)) Refl
  (RegistrationCorrespondenceEnd))))))))))))))))))))))))))))))))))))))))))

0 episodeBoundaryRegistrationCorrespondence :
  (left : EpisodeLeftTrace) -> (right : EpisodeRightTrace) ->
  RegistrationCorrespondenceByGeneration
    DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeBoundaryGenerationBijection
    (episodeLeftTrace left) (episodeRightTrace right)
episodeBoundaryRegistrationCorrespondence left right =
  MkRegistrationCorrespondenceByGeneration episodeLeftFinalIndex
    episodeRightFinalIndex (episodeBoundaryTraceCorrespondence left right)

0 episodeCurrentForward :
  (left : EpisodeLeftTrace) -> (right : EpisodeRightTrace) ->
  (n : Nat) -> (generation : RegistrationGeneration Nat) ->
  lookupCurrentGeneration @{DGamma.CP3StatementChecks.episodeNameEq} n
    (leftFinalGenerations
      (episodeBoundaryRegistrationCorrespondence left right)) = Just generation ->
  (rightGeneration : RegistrationGeneration Nat **
   (generationForward DGamma.CP3StatementChecks.episodeBoundaryGenerationBijection generation =
      rightGeneration,
    lookupCurrentGeneration @{DGamma.CP3StatementChecks.episodeNameEq} n
      (rightFinalGenerations
        (episodeBoundaryRegistrationCorrespondence left right)) =
      Just rightGeneration))
episodeCurrentForward left right Z generation found =
  void (nothingIsNotJust found)
episodeCurrentForward left right (S Z) generation found =
  case justInjective found of
    Refl => (MkRegistrationGeneration 1 1 ** (Refl, Refl))
episodeCurrentForward left right (S (S Z)) generation found =
  void (nothingIsNotJust found)
episodeCurrentForward left right (S (S (S Z))) generation found =
  case justInjective found of
    Refl => (MkRegistrationGeneration 3 9 ** (Refl, Refl))
episodeCurrentForward left right (S (S (S (S Z)))) generation found =
  case justInjective found of
    Refl => (MkRegistrationGeneration 4 14 ** (Refl, Refl))
episodeCurrentForward left right (S (S (S (S (S later))))) generation found =
  void (nothingIsNotJust found)

0 episodeCurrentBackward :
  (left : EpisodeLeftTrace) -> (right : EpisodeRightTrace) ->
  (n : Nat) -> (generation : RegistrationGeneration Nat) ->
  lookupCurrentGeneration @{DGamma.CP3StatementChecks.episodeNameEq} n
    (rightFinalGenerations
      (episodeBoundaryRegistrationCorrespondence left right)) = Just generation ->
  (leftGeneration : RegistrationGeneration Nat **
   (generationBackward DGamma.CP3StatementChecks.episodeBoundaryGenerationBijection generation =
      leftGeneration,
    lookupCurrentGeneration @{DGamma.CP3StatementChecks.episodeNameEq} n
      (leftFinalGenerations
        (episodeBoundaryRegistrationCorrespondence left right)) =
      Just leftGeneration))
episodeCurrentBackward left right Z generation found =
  void (nothingIsNotJust found)
episodeCurrentBackward left right (S Z) generation found =
  case justInjective found of
    Refl => (MkRegistrationGeneration 1 1 ** (Refl, Refl))
episodeCurrentBackward left right (S (S Z)) generation found =
  void (nothingIsNotJust found)
episodeCurrentBackward left right (S (S (S Z))) generation found =
  case justInjective found of
    Refl => (MkRegistrationGeneration 3 15 ** (Refl, Refl))
episodeCurrentBackward left right (S (S (S (S Z)))) generation found =
  case justInjective found of
    Refl => (MkRegistrationGeneration 4 20 ** (Refl, Refl))
episodeCurrentBackward left right (S (S (S (S (S later))))) generation found =
  void (nothingIsNotJust found)

0 episodeBoundaryEndpointRenaming :
  (left : EpisodeLeftTrace) -> (right : EpisodeRightTrace) ->
  CurrentEndpointRenaming DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq
    DGamma.CP3StatementChecks.episodeBoundaryGenerationBijection
    (episodeLeftTrace left) (episodeRightTrace right)
    (episodeBoundaryRegistrationCorrespondence left right)
episodeBoundaryEndpointRenaming left right =
  MkCurrentEndpointRenaming identityNameBijection
    (\n, fiber, found, root => Refl)
    (\n, fiber, found, root => Refl)
    (\n, generation, found =>
      Right (episodeCurrentForward left right n generation found))
    (\n, generation, found =>
      Right (episodeCurrentBackward left right n generation found))

0 episodeLeftRetireRoot : (left : EpisodeLeftTrace) ->
  RootOrchestrationStep DGamma.CP3StatementChecks.episodeNameEq
    (namedTransition (leftRetire0 left))
episodeLeftRetireRoot left = RootRetireStep
  (episodeRootFiber (leftRetire0Source left))
  (episodeRootFound (leftRetire0Source left))
  (episodeRootParent (leftRetire0Source left))
  (namedAction (leftRetire0 left))

0 episodeRightRetireRoot : (right : EpisodeRightTrace) ->
  RootOrchestrationStep DGamma.CP3StatementChecks.episodeNameEq
    (namedTransition (rightRetire0 right))
episodeRightRetireRoot right = RootRetireStep
  (episodeRootFiber (rightRetire0Source right))
  (episodeRootFound (rightRetire0Source right))
  (episodeRootParent (rightRetire0Source right))
  (namedAction (rightRetire0 right))

0 episodeLeftRemoveRoot : (left : EpisodeLeftTrace) ->
  RootOrchestrationStep DGamma.CP3StatementChecks.episodeNameEq
    (namedTransition (leftRemove0 left))
episodeLeftRemoveRoot left = RootRemoveStep
  (episodeRootFiber (leftRemove0Source left))
  (episodeRootFound (leftRemove0Source left))
  (episodeRootParent (leftRemove0Source left))
  (namedAction (leftRemove0 left))

0 episodeRightRemoveRoot : (right : EpisodeRightTrace) ->
  RootOrchestrationStep DGamma.CP3StatementChecks.episodeNameEq
    (namedTransition (rightRemove0 right))
episodeRightRemoveRoot right = RootRemoveStep
  (episodeRootFiber (rightRemove0Source right))
  (episodeRootFound (rightRemove0Source right))
  (episodeRootParent (rightRemove0Source right))
  (namedAction (rightRemove0 right))

0 episodeLeftChildRetireInternal : (left : EpisodeLeftTrace) ->
  RootOrchestrationStep DGamma.CP3StatementChecks.episodeNameEq
    (namedTransition (leftRetireChild2 left)) -> Void
episodeLeftChildRetireInternal left = childRetireCannotBeRoot
  DGamma.CP3StatementChecks.episodeNameEq
  (namedTransition (leftRetireChild2 left))
  (namedAction (leftRetireChild2 left))
  (episodeChildFiber (leftRetireChildSource left))
  (episodeChildFound (leftRetireChildSource left))
  (episodeChildParentRole (leftRetireChildSource left))

0 episodeLeftChildRemoveInternal : (left : EpisodeLeftTrace) ->
  RootOrchestrationStep DGamma.CP3StatementChecks.episodeNameEq
    (namedTransition (leftRemoveChild2 left)) -> Void
episodeLeftChildRemoveInternal left = childRemoveCannotBeRoot
  DGamma.CP3StatementChecks.episodeNameEq
  (namedTransition (leftRemoveChild2 left))
  (namedAction (leftRemoveChild2 left))
  (episodeChildFiber (leftRemoveChildSource left))
  (episodeChildFound (leftRemoveChildSource left))
  (episodeChildParentRole (leftRemoveChildSource left))

0 episodeBoundaryExternalRoots :
  (left : EpisodeLeftTrace) -> (right : EpisodeRightTrace) ->
  ExternalRootBirthCorrespondence
    DGamma.CP3StatementChecks.episodeBoundaryGenerationBijection 0
    (episodeLeftTrace left) 0 (episodeRightTrace right)
episodeBoundaryExternalRoots left right =
  MatchExternalRootBirth
    (namedTransition (episodeInsert0 (leftEpisodePrefix left))) (episodeLeftTail1 left)
    (namedTransition (episodeInsert0 (rightEpisodePrefix right))) (episodeRightTail1 right)
    (namedAction (episodeInsert0 (leftEpisodePrefix left))) (namedAction (episodeInsert0 (rightEpisodePrefix right))) Refl
  (MatchExternalRootBirth
    (namedTransition (episodeInsert1 (leftEpisodePrefix left))) (episodeLeftTail2 left)
    (namedTransition (episodeInsert1 (rightEpisodePrefix right))) (episodeRightTail2 right)
    (namedAction (episodeInsert1 (leftEpisodePrefix left))) (namedAction (episodeInsert1 (rightEpisodePrefix right))) Refl
  (SkipLeftNonExternalRootBirth (LBegin 0)
    (namedTransition (episodeBegin0 (leftEpisodePrefix left))) (episodeLeftTail3 left)
    (namedAction (episodeBegin0 (leftEpisodePrefix left))) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 0)
    (namedTransition (episodeAdvance0a (leftEpisodePrefix left))) (episodeLeftTail4 left)
    (namedAction (episodeAdvance0a (leftEpisodePrefix left))) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 0)
    (namedTransition (episodeAdvance0b (leftEpisodePrefix left))) (episodeLeftTail5 left)
    (namedAction (episodeAdvance0b (leftEpisodePrefix left))) Refl
  (SkipLeftNonExternalRootBirth (LBegin 1)
    (namedTransition (leftBegin1 left)) (episodeLeftTail6 left)
    (namedAction (leftBegin1 left)) Refl
  (SkipLeftNonExternalRootBirth (OInsert 2 (ChildOf 1) episodeChild)
    (namedTransition (leftDeletedChild left)) (episodeLeftTail7 left)
    (namedAction (leftDeletedChild left)) Refl
  (SkipLeftNonExternalRootBirth (ORetire 2)
    (namedTransition (leftRetireChild2 left)) (episodeLeftTail8 left)
    (namedAction (leftRetireChild2 left)) Refl
  (SkipLeftNonExternalRootBirth (ORemove 2)
    (namedTransition (leftRemoveChild2 left)) (episodeLeftTail9 left)
    (namedAction (leftRemoveChild2 left)) Refl
  (SkipLeftNonExternalRootBirth (ORetire 0)
    (namedTransition (leftRetire0 left)) (episodeLeftTail10 left)
    (namedAction (leftRetire0 left)) Refl
  (SkipLeftNonExternalRootBirth (LLeave 0)
    (namedTransition (leftLeave0 left)) (episodeLeftTail11 left)
    (namedAction (leftLeave0 left)) Refl
  (SkipLeftNonExternalRootBirth (LDivert 1)
    (namedTransition (leftDivert1 left)) (episodeLeftTail12 left)
    (namedAction (leftDivert1 left)) Refl
  (SkipLeftNonExternalRootBirth (LUnload 1)
    (namedTransition (leftUnload1 left)) (episodeLeftTail13 left)
    (namedAction (leftUnload1 left)) Refl
  (SkipLeftNonExternalRootBirth (LUnload 0)
    (namedTransition (leftUnload0 left)) (episodeLeftTail14 left)
    (namedAction (leftUnload0 left)) Refl
  (SkipLeftNonExternalRootBirth (ORemove 0)
    (namedTransition (leftRemove0 left)) (episodeLeftTail15 left)
    (namedAction (leftRemove0 left)) Refl
  (SkipRightNonExternalRootBirth (LBegin 0)
    (namedTransition (episodeBegin0 (rightEpisodePrefix right))) (episodeRightTail3 right)
    (namedAction (episodeBegin0 (rightEpisodePrefix right))) Refl
  (SkipRightNonExternalRootBirth (LAdvance 0)
    (namedTransition (episodeAdvance0a (rightEpisodePrefix right))) (episodeRightTail4 right)
    (namedAction (episodeAdvance0a (rightEpisodePrefix right))) Refl
  (SkipRightNonExternalRootBirth (LAdvance 0)
    (namedTransition (episodeAdvance0b (rightEpisodePrefix right))) (episodeRightTail5 right)
    (namedAction (episodeAdvance0b (rightEpisodePrefix right))) Refl
  (SkipRightNonExternalRootBirth (ORetire 0)
    (namedTransition (rightRetire0 right)) (episodeRightTail6 right)
    (namedAction (rightRetire0 right)) Refl
  (SkipRightNonExternalRootBirth (LLeave 0)
    (namedTransition (rightLeave0 right)) (episodeRightTail7 right)
    (namedAction (rightLeave0 right)) Refl
  (SkipRightNonExternalRootBirth (LUnload 0)
    (namedTransition (rightUnload0 right)) (episodeRightTail8 right)
    (namedAction (rightUnload0 right)) Refl
  (SkipRightNonExternalRootBirth (ORemove 0)
    (namedTransition (rightRemove0 right)) (episodeRightTail9 right)
    (namedAction (rightRemove0 right)) Refl
  (MatchExternalRootBirth
    (namedTransition (leftInsert3 left)) (episodeLeftTail16 left)
    (namedTransition (rightInsert3 right)) (episodeRightTail10 right)
    (namedAction (leftInsert3 left)) (namedAction (rightInsert3 right)) Refl
  (SkipLeftNonExternalRootBirth (LBegin 3)
    (namedTransition (leftBegin3 left)) (episodeLeftTail17 left)
    (namedAction (leftBegin3 left)) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 3)
    (namedTransition (leftAdvance3a left)) (episodeLeftTail18 left)
    (namedAction (leftAdvance3a left)) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 3)
    (namedTransition (leftAdvance3b left)) (episodeLeftTail19 left)
    (namedAction (leftAdvance3b left)) Refl
  (SkipLeftNonExternalRootBirth (LBegin 1)
    (namedTransition (leftReopen1 left)) (episodeLeftTail20 left)
    (namedAction (leftReopen1 left)) Refl
  (SkipLeftNonExternalRootBirth (OInsert 4 (ChildOf 1) episodeChild)
    (namedTransition (leftSurvivingChild left)) (episodeLeftTail21 left)
    (namedAction (leftSurvivingChild left)) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 1)
    (namedTransition (leftFinish1 left)) (episodeLeftTail22 left)
    (namedAction (leftFinish1 left)) Refl
  (SkipLeftNonExternalRootBirth (LBegin 4)
    (namedTransition (leftBegin4 left)) (episodeLeftTail23 left)
    (namedAction (leftBegin4 left)) Refl
  (SkipLeftNonExternalRootBirth (LAdvance 4)
    (namedTransition (leftFinish4 left)) (episodeLeftTail24 left)
    (namedAction (leftFinish4 left)) Refl
  (SkipRightNonExternalRootBirth (LBegin 3)
    (namedTransition (rightBegin3 right)) (episodeRightTail11 right)
    (namedAction (rightBegin3 right)) Refl
  (SkipRightNonExternalRootBirth (LAdvance 3)
    (namedTransition (rightAdvance3a right)) (episodeRightTail12 right)
    (namedAction (rightAdvance3a right)) Refl
  (SkipRightNonExternalRootBirth (LAdvance 3)
    (namedTransition (rightAdvance3b right)) (episodeRightTail13 right)
    (namedAction (rightAdvance3b right)) Refl
  (SkipRightNonExternalRootBirth (LBegin 1)
    (namedTransition (rightBegin1 right)) (episodeRightTail14 right)
    (namedAction (rightBegin1 right)) Refl
  (SkipRightNonExternalRootBirth (OInsert 4 (ChildOf 1) episodeChild)
    (namedTransition (rightSurvivingChild right)) (episodeRightTail15 right)
    (namedAction (rightSurvivingChild right)) Refl
  (SkipRightNonExternalRootBirth (LAdvance 1)
    (namedTransition (rightFinish1 right)) (episodeRightTail16 right)
    (namedAction (rightFinish1 right)) Refl
  (SkipRightNonExternalRootBirth (LBegin 4)
    (namedTransition (rightBegin4 right)) (episodeRightTail17 right)
    (namedAction (rightBegin4 right)) Refl
  (SkipRightNonExternalRootBirth (LAdvance 4)
    (namedTransition (rightFinish4 right)) (episodeRightTail18 right)
    (namedAction (rightFinish4 right)) Refl
  (ExternalRootBirthCorrespondenceEnd)))))))))))))))))))))))))))))))))))))))

0 episodeBoundarySameExternal :
  (left : EpisodeLeftTrace) -> (right : EpisodeRightTrace) ->
  SameExternalOrchestration DGamma.CP3StatementChecks.episodeNameEq
    (episodeLeftTrace left) (episodeRightTrace right)
episodeBoundarySameExternal left right =
  MatchExternalInput (OInsert 0 Root DGamma.CalculusChecks.providerComponent)
    (namedTransition (episodeInsert0 (leftEpisodePrefix left))) (episodeLeftTail1 left) (RootInsertStep (namedAction (episodeInsert0 (leftEpisodePrefix left))))
    (namedTransition (episodeInsert0 (rightEpisodePrefix right))) (episodeRightTail1 right) (RootInsertStep (namedAction (episodeInsert0 (rightEpisodePrefix right))))
    (namedAction (episodeInsert0 (leftEpisodePrefix left))) (namedAction (episodeInsert0 (rightEpisodePrefix right)))
  (MatchExternalInput (OInsert 1 Root episodeParent)
    (namedTransition (episodeInsert1 (leftEpisodePrefix left))) (episodeLeftTail2 left) (RootInsertStep (namedAction (episodeInsert1 (leftEpisodePrefix left))))
    (namedTransition (episodeInsert1 (rightEpisodePrefix right))) (episodeRightTail2 right) (RootInsertStep (namedAction (episodeInsert1 (rightEpisodePrefix right))))
    (namedAction (episodeInsert1 (leftEpisodePrefix left))) (namedAction (episodeInsert1 (rightEpisodePrefix right)))
  (SkipLeftInternal (namedTransition (episodeBegin0 (leftEpisodePrefix left)))
    (episodeLeftTail3 left) (namedLifecycleNotRoot (episodeBegin0 (leftEpisodePrefix left)) Refl)
  (SkipLeftInternal (namedTransition (episodeAdvance0a (leftEpisodePrefix left)))
    (episodeLeftTail4 left) (namedLifecycleNotRoot (episodeAdvance0a (leftEpisodePrefix left)) Refl)
  (SkipLeftInternal (namedTransition (episodeAdvance0b (leftEpisodePrefix left)))
    (episodeLeftTail5 left) (namedLifecycleNotRoot (episodeAdvance0b (leftEpisodePrefix left)) Refl)
  (SkipLeftInternal (namedTransition (leftBegin1 left))
    (episodeLeftTail6 left) (namedLifecycleNotRoot (leftBegin1 left) Refl)
  (SkipLeftInternal (namedTransition (leftDeletedChild left))
    (episodeLeftTail7 left) (childInsertCannotBeRoot (namedTransition (leftDeletedChild left)) (namedAction (leftDeletedChild left)))
  (SkipLeftInternal (namedTransition (leftRetireChild2 left))
    (episodeLeftTail8 left) (episodeLeftChildRetireInternal left)
  (SkipLeftInternal (namedTransition (leftRemoveChild2 left))
    (episodeLeftTail9 left) (episodeLeftChildRemoveInternal left)
  (SkipRightInternal (namedTransition (episodeBegin0 (rightEpisodePrefix right)))
    (episodeRightTail3 right) (namedLifecycleNotRoot (episodeBegin0 (rightEpisodePrefix right)) Refl)
  (SkipRightInternal (namedTransition (episodeAdvance0a (rightEpisodePrefix right)))
    (episodeRightTail4 right) (namedLifecycleNotRoot (episodeAdvance0a (rightEpisodePrefix right)) Refl)
  (SkipRightInternal (namedTransition (episodeAdvance0b (rightEpisodePrefix right)))
    (episodeRightTail5 right) (namedLifecycleNotRoot (episodeAdvance0b (rightEpisodePrefix right)) Refl)
  (MatchExternalInput (ORetire 0)
    (namedTransition (leftRetire0 left)) (episodeLeftTail10 left) (episodeLeftRetireRoot left)
    (namedTransition (rightRetire0 right)) (episodeRightTail6 right) (episodeRightRetireRoot right)
    (namedAction (leftRetire0 left)) (namedAction (rightRetire0 right))
  (SkipLeftInternal (namedTransition (leftLeave0 left))
    (episodeLeftTail11 left) (namedLifecycleNotRoot (leftLeave0 left) Refl)
  (SkipLeftInternal (namedTransition (leftDivert1 left))
    (episodeLeftTail12 left) (namedLifecycleNotRoot (leftDivert1 left) Refl)
  (SkipLeftInternal (namedTransition (leftUnload1 left))
    (episodeLeftTail13 left) (namedLifecycleNotRoot (leftUnload1 left) Refl)
  (SkipLeftInternal (namedTransition (leftUnload0 left))
    (episodeLeftTail14 left) (namedLifecycleNotRoot (leftUnload0 left) Refl)
  (SkipRightInternal (namedTransition (rightLeave0 right))
    (episodeRightTail7 right) (namedLifecycleNotRoot (rightLeave0 right) Refl)
  (SkipRightInternal (namedTransition (rightUnload0 right))
    (episodeRightTail8 right) (namedLifecycleNotRoot (rightUnload0 right) Refl)
  (MatchExternalInput (ORemove 0)
    (namedTransition (leftRemove0 left)) (episodeLeftTail15 left) (episodeLeftRemoveRoot left)
    (namedTransition (rightRemove0 right)) (episodeRightTail9 right) (episodeRightRemoveRoot right)
    (namedAction (leftRemove0 left)) (namedAction (rightRemove0 right))
  (MatchExternalInput (OInsert 3 Root DGamma.CalculusChecks.providerComponent)
    (namedTransition (leftInsert3 left)) (episodeLeftTail16 left) (RootInsertStep (namedAction (leftInsert3 left)))
    (namedTransition (rightInsert3 right)) (episodeRightTail10 right) (RootInsertStep (namedAction (rightInsert3 right)))
    (namedAction (leftInsert3 left)) (namedAction (rightInsert3 right))
  (SkipLeftInternal (namedTransition (leftBegin3 left))
    (episodeLeftTail17 left) (namedLifecycleNotRoot (leftBegin3 left) Refl)
  (SkipLeftInternal (namedTransition (leftAdvance3a left))
    (episodeLeftTail18 left) (namedLifecycleNotRoot (leftAdvance3a left) Refl)
  (SkipLeftInternal (namedTransition (leftAdvance3b left))
    (episodeLeftTail19 left) (namedLifecycleNotRoot (leftAdvance3b left) Refl)
  (SkipLeftInternal (namedTransition (leftReopen1 left))
    (episodeLeftTail20 left) (namedLifecycleNotRoot (leftReopen1 left) Refl)
  (SkipLeftInternal (namedTransition (leftSurvivingChild left))
    (episodeLeftTail21 left) (childInsertCannotBeRoot (namedTransition (leftSurvivingChild left)) (namedAction (leftSurvivingChild left)))
  (SkipLeftInternal (namedTransition (leftFinish1 left))
    (episodeLeftTail22 left) (namedLifecycleNotRoot (leftFinish1 left) Refl)
  (SkipLeftInternal (namedTransition (leftBegin4 left))
    (episodeLeftTail23 left) (namedLifecycleNotRoot (leftBegin4 left) Refl)
  (SkipLeftInternal (namedTransition (leftFinish4 left))
    (episodeLeftTail24 left) (namedLifecycleNotRoot (leftFinish4 left) Refl)
  (SkipRightInternal (namedTransition (rightBegin3 right))
    (episodeRightTail11 right) (namedLifecycleNotRoot (rightBegin3 right) Refl)
  (SkipRightInternal (namedTransition (rightAdvance3a right))
    (episodeRightTail12 right) (namedLifecycleNotRoot (rightAdvance3a right) Refl)
  (SkipRightInternal (namedTransition (rightAdvance3b right))
    (episodeRightTail13 right) (namedLifecycleNotRoot (rightAdvance3b right) Refl)
  (SkipRightInternal (namedTransition (rightBegin1 right))
    (episodeRightTail14 right) (namedLifecycleNotRoot (rightBegin1 right) Refl)
  (SkipRightInternal (namedTransition (rightSurvivingChild right))
    (episodeRightTail15 right) (childInsertCannotBeRoot (namedTransition (rightSurvivingChild right)) (namedAction (rightSurvivingChild right)))
  (SkipRightInternal (namedTransition (rightFinish1 right))
    (episodeRightTail16 right) (namedLifecycleNotRoot (rightFinish1 right) Refl)
  (SkipRightInternal (namedTransition (rightBegin4 right))
    (episodeRightTail17 right) (namedLifecycleNotRoot (rightBegin4 right) Refl)
  (SkipRightInternal (namedTransition (rightFinish4 right))
    (episodeRightTail18 right) (namedLifecycleNotRoot (rightFinish4 right) Refl)
  (SameExternalOrchestrationEnd)))))))))))))))))))))))))))))))))))))

0 episodeBoundarySameInputs :
  (left : EpisodeLeftTrace) -> (right : EpisodeRightTrace) ->
  SameOrchestrationModuloGenerated DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq
    (episodeLeftTrace left) (episodeRightTrace right)
episodeBoundarySameInputs left right = MkSameOrchestrationModuloGenerated
  episodeBoundaryGenerationBijection (episodeBoundarySameExternal left right)
  (episodeBoundaryExternalRoots left right)
  (episodeBoundaryRegistrationCorrespondence left right)
  (episodeBoundaryEndpointRenaming left right)

public export
record EpisodeBoundaryCorrespondenceWitness where
  constructor MkEpisodeBoundaryCorrespondenceWitness
  episodeBoundaryLeft : EpisodeLeftTrace
  episodeBoundaryRight : EpisodeRightTrace
  0 episodeBoundarySameInputWitness : SameOrchestrationModuloGenerated
    DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq
    (episodeLeftTrace episodeBoundaryLeft)
    (episodeRightTrace episodeBoundaryRight)

public export
episodeBoundaryCorrespondenceWitness :
  Maybe EpisodeBoundaryCorrespondenceWitness
episodeBoundaryCorrespondenceWitness = do
  leftCommon <- buildEpisodeCommonPrefix
  rightCommon <- buildEpisodeCommonPrefix
  left <- buildEpisodeLeftTrace leftCommon
  right <- buildEpisodeRightTrace rightCommon
  Just (MkEpisodeBoundaryCorrespondenceWitness left right
    (episodeBoundarySameInputs left right))

public export
episodeBoundaryCorrespondenceCheck : Bool
episodeBoundaryCorrespondenceCheck =
  case episodeBoundaryCorrespondenceWitness of
    Nothing => False
    Just witness => True

||| Full public Theorem-73 boundary for the hardened round-8 pair.  The left
||| deleted child is retired and removed before its parent's L-Unload.  Its
||| classification is discharged by `DeletedClosingRegistration`; the final
||| child is position zero in the reopened left activation and in the delayed
||| right activation.
public export
0 episodeBoundaryTheorem73PremiseChain :
  confluenceTheorem Nat ToyKey ToyValue ToyRuntime String ->
  (protocol : RegistrationProtocol ToyKey ToyValue ToyRuntime String) ->
  (0 witness : EpisodeBoundaryCorrespondenceWitness) ->
  AlignedTransitions Nat ToyKey ToyRuntime String ToyValue
    DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq
    (episodeLeftTrace (episodeBoundaryLeft witness)) ->
  AlignedTransitions Nat ToyKey ToyRuntime String ToyValue
    DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq
    (episodeRightTrace (episodeBoundaryRight witness)) ->
  RegistrationDiscipline protocol DGamma.CP3StatementChecks.episodeNameEq
    (episodeLeftTrace (episodeBoundaryLeft witness)) ->
  RegistrationDiscipline protocol DGamma.CP3StatementChecks.episodeNameEq
    (episodeRightTrace (episodeBoundaryRight witness)) ->
  registryWellFormed @{DGamma.CP3StatementChecks.episodeNameEq}
    @{DGamma.CP3StatementChecks.episodeKeyEq}
    DGamma.CalculusChecks.initialSystem = True ->
  bindings (registry DGamma.CalculusChecks.initialSystem) = [] ->
  quiet @{DGamma.CP3StatementChecks.episodeNameEq}
    @{DGamma.CP3StatementChecks.episodeKeyEq}
    (namedAfter (leftFinish4 (episodeBoundaryLeft witness))) = True ->
  quiet @{DGamma.CP3StatementChecks.episodeNameEq}
    @{DGamma.CP3StatementChecks.episodeKeyEq}
    (namedAfter (rightFinish4 (episodeBoundaryRight witness))) = True ->
  noFailedFibers
    (namedAfter (leftFinish4 (episodeBoundaryLeft witness))) = True ->
  noFailedFibers
    (namedAfter (rightFinish4 (episodeBoundaryRight witness))) = True ->
  TraceComponentsTotal DGamma.CP3StatementChecks.episodeKeyEq
    (episodeLeftTrace (episodeBoundaryLeft witness)) ->
  TraceComponentsTotal DGamma.CP3StatementChecks.episodeKeyEq
    (episodeRightTrace (episodeBoundaryRight witness)) ->
  TraceIndependent Nat ToyKey ToyRuntime String ToyValue
    DGamma.CP3StatementChecks.episodeKeyEq
    (episodeLeftTrace (episodeBoundaryLeft witness)) ->
  TraceIndependent Nat ToyKey ToyRuntime String ToyValue
    DGamma.CP3StatementChecks.episodeKeyEq
    (episodeRightTrace (episodeBoundaryRight witness)) ->
  ConfluenceResult Nat ToyKey ToyRuntime String ToyValue protocol
    DGamma.CP3StatementChecks.episodeNameEq
    DGamma.CP3StatementChecks.episodeKeyEq
    (episodeLeftTrace (episodeBoundaryLeft witness))
    (episodeRightTrace (episodeBoundaryRight witness))
    (generatedGenerationBijection
      (episodeBoundarySameInputWitness witness))
    (currentNameBijection
      (endpointRenaming (episodeBoundarySameInputWitness witness)))
episodeBoundaryTheorem73PremiseChain claim protocol witness leftAligned
  rightAligned leftDiscipline rightDiscipline initialWellFormed initialEmpty
  leftQuiet rightQuiet leftSuccess rightSuccess leftTotal rightTotal
  leftIndependent rightIndependent =
    claim DGamma.CP3StatementChecks.episodeNameEq
      DGamma.CP3StatementChecks.episodeKeyEq protocol
      DGamma.CalculusChecks.initialSystem
      (namedAfter (leftFinish4 (episodeBoundaryLeft witness)))
      (namedAfter (rightFinish4 (episodeBoundaryRight witness)))
      (episodeLeftTrace (episodeBoundaryLeft witness))
      (episodeRightTrace (episodeBoundaryRight witness))
      leftAligned rightAligned leftDiscipline rightDiscipline initialWellFormed
      initialEmpty leftQuiet rightQuiet leftSuccess rightSuccess leftTotal
      rightTotal leftIndependent rightIndependent
      (episodeBoundarySameInputWitness witness)

public export
episodeBoundaryRuntimeCheck : Bool
episodeBoundaryRuntimeCheck =
  case (buildEpisodeCommonPrefix, buildEpisodeCommonPrefix) of
    (Just leftPrefix, Just rightPrefix) =>
      case (buildEpisodeLeftTrace leftPrefix, buildEpisodeRightTrace rightPrefix) of
        (Just left, Just right) =>
          let leftFinal = namedAfter (leftFinish4 left)
              rightFinal = namedAfter (rightFinish4 right) in
            quiet @{episodeNameEq} @{episodeKeyEq} leftFinal &&
            quiet @{episodeNameEq} @{episodeKeyEq} rightFinal &&
            noFailedFibers leftFinal && noFailedFibers rightFinal &&
            isSupported @{episodeNameEq} @{episodeKeyEq} 1 leftFinal &&
            isSupported @{episodeNameEq} @{episodeKeyEq} 3 leftFinal &&
            isSupported @{episodeNameEq} @{episodeKeyEq} 4 leftFinal &&
            isSupported @{episodeNameEq} @{episodeKeyEq} 1 rightFinal &&
            isSupported @{episodeNameEq} @{episodeKeyEq} 3 rightFinal &&
            isSupported @{episodeNameEq} @{episodeKeyEq} 4 rightFinal
        _ => False
    _ => False

public export
allCP3StatementChecks : Bool
allCP3StatementChecks = roleChangingRuntimeCheck &&
  roleChangingCanonicalRuntimeCheck && roleChangingProofTraceCheck &&
  freshChoiceCorrespondenceCheck && crossParentPermutationRuntimeCheck &&
  crossParentPermutationCorrespondenceCheck && removedRootRuntimeCheck &&
  episodeBoundaryRuntimeCheck &&
  episodeBoundaryCorrespondenceCheck

||| End-to-end Theorem-73 statement check for the blocker pair.  Every premise
||| after the concrete checked traces is the exact public theorem premise; the
||| same-input argument is the constructed generation-wise witness above, not
||| an assumed global raw-name renaming.
public export
0 freshChoiceTheorem73PremiseChain :
  confluenceTheorem Nat RegistrationTestKey RegistrationTestValue Unit String ->
  (0 witness : FreshChoiceCorrespondenceWitness) ->
  AlignedTransitions Nat RegistrationTestKey Unit String RegistrationTestValue
    DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq
    (namedRoleChangingTrace (leftFreshChoice witness)) ->
  AlignedTransitions Nat RegistrationTestKey Unit String RegistrationTestValue
    DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq
    (namedRoleChangingTrace (rightFreshChoice witness)) ->
  RegistrationDiscipline DGamma.CP3StatementChecks.registrationTestProtocol DGamma.CP3StatementChecks.registrationTestNameEq
    (namedRoleChangingTrace (leftFreshChoice witness)) ->
  RegistrationDiscipline DGamma.CP3StatementChecks.registrationTestProtocol DGamma.CP3StatementChecks.registrationTestNameEq
    (namedRoleChangingTrace (rightFreshChoice witness)) ->
  registryWellFormed @{DGamma.CP3StatementChecks.registrationTestNameEq} @{DGamma.CP3StatementChecks.registrationTestKeyEq}
    DGamma.CP3StatementChecks.registrationTestInitial = True ->
  bindings (registry DGamma.CP3StatementChecks.registrationTestInitial) = [] ->
  quiet @{DGamma.CP3StatementChecks.registrationTestNameEq} @{DGamma.CP3StatementChecks.registrationTestKeyEq}
    (namedAfter (rootAdvance1 (leftFreshChoice witness))) = True ->
  quiet @{DGamma.CP3StatementChecks.registrationTestNameEq} @{DGamma.CP3StatementChecks.registrationTestKeyEq}
    (namedAfter (rootAdvance1 (rightFreshChoice witness))) = True ->
  noFailedFibers (namedAfter (rootAdvance1 (leftFreshChoice witness))) = True ->
  noFailedFibers (namedAfter (rootAdvance1 (rightFreshChoice witness))) = True ->
  TraceComponentsTotal DGamma.CP3StatementChecks.registrationTestKeyEq
    (namedRoleChangingTrace (leftFreshChoice witness)) ->
  TraceComponentsTotal DGamma.CP3StatementChecks.registrationTestKeyEq
    (namedRoleChangingTrace (rightFreshChoice witness)) ->
  TraceIndependent Nat RegistrationTestKey Unit String RegistrationTestValue
    DGamma.CP3StatementChecks.registrationTestKeyEq (namedRoleChangingTrace (leftFreshChoice witness)) ->
  TraceIndependent Nat RegistrationTestKey Unit String RegistrationTestValue
    DGamma.CP3StatementChecks.registrationTestKeyEq (namedRoleChangingTrace (rightFreshChoice witness)) ->
  ConfluenceResult Nat RegistrationTestKey Unit String RegistrationTestValue
    DGamma.CP3StatementChecks.registrationTestProtocol DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq
    (namedRoleChangingTrace (leftFreshChoice witness))
    (namedRoleChangingTrace (rightFreshChoice witness))
    (generatedGenerationBijection (blockerPairSameInputs witness))
    (currentNameBijection (endpointRenaming (blockerPairSameInputs witness)))
freshChoiceTheorem73PremiseChain claim witness leftAligned rightAligned
  leftDiscipline rightDiscipline initialWellFormed initialEmpty leftQuiet
  rightQuiet leftSuccess rightSuccess leftTotal rightTotal leftIndependent
  rightIndependent =
    claim DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq DGamma.CP3StatementChecks.registrationTestProtocol
      DGamma.CP3StatementChecks.registrationTestInitial
      (namedAfter (rootAdvance1 (leftFreshChoice witness)))
      (namedAfter (rootAdvance1 (rightFreshChoice witness)))
      (namedRoleChangingTrace (leftFreshChoice witness))
      (namedRoleChangingTrace (rightFreshChoice witness))
      leftAligned rightAligned leftDiscipline rightDiscipline initialWellFormed
      initialEmpty leftQuiet rightQuiet leftSuccess rightSuccess leftTotal
      rightTotal leftIndependent rightIndependent (blockerPairSameInputs witness)

||| End-to-end public Theorem-73 premise check for the round-7 blocker pair.
||| The traces differ only in the cross-parent interleaving of child births:
||| left generations `(2,4),(3,5)` map structurally to right generations
||| `(2,5),(3,4)` while both external roots stay exact.
public export
0 crossParentPermutationTheorem73PremiseChain :
  confluenceTheorem Nat RegistrationTestKey RegistrationTestValue Unit String ->
  (0 witness : CrossParentPermutationCorrespondenceWitness) ->
  AlignedTransitions Nat RegistrationTestKey Unit String RegistrationTestValue
    DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq
    (crossParentTrace (crossParentLeft witness)) ->
  AlignedTransitions Nat RegistrationTestKey Unit String RegistrationTestValue
    DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq
    (crossParentTrace (crossParentRight witness)) ->
  RegistrationDiscipline DGamma.CP3StatementChecks.registrationTestProtocol DGamma.CP3StatementChecks.registrationTestNameEq
    (crossParentTrace (crossParentLeft witness)) ->
  RegistrationDiscipline DGamma.CP3StatementChecks.registrationTestProtocol DGamma.CP3StatementChecks.registrationTestNameEq
    (crossParentTrace (crossParentRight witness)) ->
  registryWellFormed @{DGamma.CP3StatementChecks.registrationTestNameEq} @{DGamma.CP3StatementChecks.registrationTestKeyEq}
    DGamma.CP3StatementChecks.registrationTestInitial = True ->
  bindings (registry DGamma.CP3StatementChecks.registrationTestInitial) = [] ->
  quiet @{DGamma.CP3StatementChecks.registrationTestNameEq} @{DGamma.CP3StatementChecks.registrationTestKeyEq}
    (namedAfter (crossAdvance3 (crossParentLeft witness))) = True ->
  quiet @{DGamma.CP3StatementChecks.registrationTestNameEq} @{DGamma.CP3StatementChecks.registrationTestKeyEq}
    (namedAfter (crossAdvance3 (crossParentRight witness))) = True ->
  noFailedFibers (namedAfter (crossAdvance3 (crossParentLeft witness))) = True ->
  noFailedFibers (namedAfter (crossAdvance3 (crossParentRight witness))) = True ->
  TraceComponentsTotal DGamma.CP3StatementChecks.registrationTestKeyEq
    (crossParentTrace (crossParentLeft witness)) ->
  TraceComponentsTotal DGamma.CP3StatementChecks.registrationTestKeyEq
    (crossParentTrace (crossParentRight witness)) ->
  TraceIndependent Nat RegistrationTestKey Unit String RegistrationTestValue
    DGamma.CP3StatementChecks.registrationTestKeyEq (crossParentTrace (crossParentLeft witness)) ->
  TraceIndependent Nat RegistrationTestKey Unit String RegistrationTestValue
    DGamma.CP3StatementChecks.registrationTestKeyEq (crossParentTrace (crossParentRight witness)) ->
  ConfluenceResult Nat RegistrationTestKey Unit String RegistrationTestValue
    DGamma.CP3StatementChecks.registrationTestProtocol DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq
    (crossParentTrace (crossParentLeft witness))
    (crossParentTrace (crossParentRight witness))
    (generatedGenerationBijection (crossParentBlockerSameInputs witness))
    (currentNameBijection (endpointRenaming (crossParentBlockerSameInputs witness)))
crossParentPermutationTheorem73PremiseChain claim witness leftAligned rightAligned
  leftDiscipline rightDiscipline initialWellFormed initialEmpty leftQuiet
  rightQuiet leftSuccess rightSuccess leftTotal rightTotal leftIndependent
  rightIndependent =
    claim DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq DGamma.CP3StatementChecks.registrationTestProtocol
      DGamma.CP3StatementChecks.registrationTestInitial
      (namedAfter (crossAdvance3 (crossParentLeft witness)))
      (namedAfter (crossAdvance3 (crossParentRight witness)))
      (crossParentTrace (crossParentLeft witness))
      (crossParentTrace (crossParentRight witness))
      leftAligned rightAligned leftDiscipline rightDiscipline initialWellFormed
      initialEmpty leftQuiet rightQuiet leftSuccess rightSuccess leftTotal
      rightTotal leftIndependent rightIndependent (crossParentBlockerSameInputs witness)

||| Complete `CanonicalSchedule` constructor check specialized to the concrete
||| nine-action role-changing trace.  This is intentionally an assembly check,
||| not a claimed construction of the still-open sorting proof: every field is
||| tied to this exact original trace, and the endpoint is additionally forced
||| to have no current raw omission and exactly the historical child generation
||| `(1,2)`.  It replaces the former singleton-membership pseudo-regression.
public export
0 roleChangingFullCanonicalScheduleStatementCheck :
  (original : RoleChangingNamedTrace 1) ->
  (canonicalFinal : SystemState Nat RegistrationTestKey RegistrationTestValue
    Unit String) ->
  (canonicalTrace : Transitions DGamma.CP3StatementChecks.registrationTestInitial canonicalFinal) ->
  SameExternalOrchestration DGamma.CP3StatementChecks.registrationTestNameEq
    (namedRoleChangingTrace original) canonicalTrace ->
  RegistrationDiscipline DGamma.CP3StatementChecks.registrationTestProtocol DGamma.CP3StatementChecks.registrationTestNameEq
    (namedRoleChangingTrace original) ->
  RegistrationDiscipline DGamma.CP3StatementChecks.registrationTestProtocol DGamma.CP3StatementChecks.registrationTestNameEq
    canonicalTrace ->
  (order : List Nat) ->
  (linearization : LinearizesSupport Nat RegistrationTestKey Unit String
    RegistrationTestValue DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq
    (namedAfter (rootAdvance1 original)) order) ->
  (blocks : (n : Nat) -> Elem n order ->
    LocatedOpenEpisodeBlock Nat RegistrationTestKey Unit String
      RegistrationTestValue DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq n
      canonicalTrace) ->
  ((earlier, later : Nat) ->
    (earlierIn : Elem earlier order) -> (laterIn : Elem later order) ->
    BeforeIn earlier later order ->
    BlockBefore Nat RegistrationTestKey Unit String RegistrationTestValue
      DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq canonicalTrace earlier later
      (blocks earlier earlierIn) (blocks later laterIn)) ->
  LifecycleActorsCovered order canonicalTrace ->
  CanonicalInputPlacement Nat RegistrationTestKey Unit String
    RegistrationTestValue DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq
    (namedAfter (rootAdvance1 original)) order canonicalTrace ->
  (endpoint : CanonicalEndpointRelation Nat RegistrationTestKey Unit String
    RegistrationTestValue DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq
    (namedAfter (rootAdvance1 original)) canonicalFinal) ->
  endpointWithdrawnNames endpoint = [] ->
  endpointWithdrawnGenerations endpoint =
    [MkRegistrationGeneration 1 2] ->
  CanonicalRegistrationCorrespondence (namedRoleChangingTrace original)
    canonicalTrace (endpointWithdrawnGenerations endpoint) ->
  CanonicalSchedule Nat RegistrationTestKey Unit String RegistrationTestValue
    DGamma.CP3StatementChecks.registrationTestProtocol DGamma.CP3StatementChecks.registrationTestNameEq DGamma.CP3StatementChecks.registrationTestKeyEq
    (namedRoleChangingTrace original)
roleChangingFullCanonicalScheduleStatementCheck original canonicalFinal
  canonicalTrace sameInputs originalDiscipline canonicalDiscipline order
  linearization blocks ordered coverage placement endpoint noRaw historical
  registrationTree =
    MkCanonicalSchedule canonicalFinal canonicalTrace sameInputs
      originalDiscipline canonicalDiscipline order linearization blocks ordered
      coverage placement endpoint registrationTree

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

||| The constructive CP4 inhabitant has exactly the immutable accepted alias.
public export
0 acceptedSupportLemma68Proof :
  supportWellFoundedTheorem name key value world error
acceptedSupportLemma68Proof =
  supportWellFoundedTheoremProof name key value world error

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
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  (same : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  RegistrationGenerationBijection name
orchestrationGenerationRenamingGuard same = generatedGenerationBijection same

public export
0 orchestrationCurrentRenamingGuard :
  {leftFirst, leftFinal, rightFirst, rightFinal :
    SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} ->
  {right : Transitions rightFirst rightFinal} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  (same : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  NameBijection name
orchestrationCurrentRenamingGuard same =
  currentNameBijection (endpointRenaming same)

public export
0 registrationGenerationGuard :
  {leftFirst, leftFinal, rightFirst, rightFinal :
    SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} ->
  {right : Transitions rightFirst rightFinal} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  (same : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  RegistrationCorrespondenceByGeneration nameEq
    (generatedGenerationBijection same) left right
registrationGenerationGuard same = generatedRegistrationTree same

public export
0 registrationMultiplicityGuard :
  {leftFirst, leftFinal, rightFirst, rightFinal :
    SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} ->
  {right : Transitions rightFirst rightFinal} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  (same : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  RegistrationTraceCorrespondence nameEq (generatedGenerationBijection same)
    0 DGamma.CP3.emptyRegistrationIndex left
      (leftFinalIndex (generatedRegistrationTree same))
    0 DGamma.CP3.emptyRegistrationIndex right
      (rightFinalIndex (generatedRegistrationTree same)) [] []
registrationMultiplicityGuard same =
  generationTraceCorrespondence (generatedRegistrationTree same)

public export
0 confluenceRenamedEndpointGuard :
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {left : Transitions initial leftFinal} ->
  {right : Transitions initial rightFinal} ->
  (result : ConfluenceResult name key world error value protocol nameEq keyEq
    left right generationRenaming currentRenaming) ->
  SystemEquivalentByRenamingModuloVestigial name key world error value nameEq
    keyEq (finalRegistrationCorrespondence result) currentRenaming
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

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
  MkRegistrationGeneration 1 1
swapHistoricalRootGeneration (MkRegistrationGeneration 1 1) =
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
  (MkRegistrationGeneration (S Z) (S (S ordinal))) = Refl
swapHistoricalRootGenerationInvolutive
  (MkRegistrationGeneration (S (S name)) ordinal) = Refl

public export
historicalRootPermutationBijection : RegistrationGenerationBijection Nat
historicalRootPermutationBijection = MkRegistrationGenerationBijection
  swapHistoricalRootGeneration swapHistoricalRootGeneration
  swapHistoricalRootGenerationInvolutive
  swapHistoricalRootGenerationInvolutive

||| The weak dual found in round 7 is rejected at the public coupling: even if
||| root 0 is later removed, its exact external birth at ordinal 0 cannot be
||| reassigned to root 1's historical generation.
public export
0 historicalExternalRootPermutationRejected :
  {leftFirst, leftMiddle, leftFinal, rightFirst, rightMiddle, rightFinal :
    SystemState Nat key value world error} ->
  {leftTransition : Transition leftFirst leftMiddle} ->
  {leftRest : Transitions leftMiddle leftFinal} ->
  {rightTransition : Transition rightFirst rightMiddle} ->
  {rightRest : Transitions rightMiddle rightFinal} ->
  {component : Component key value world error} ->
  ExternalRootBirthCorrespondence
    DGamma.CP3StatementChecks.historicalRootPermutationBijection 0
    (MoreTransitions leftTransition leftRest) 0
    (MoreTransitions rightTransition rightRest) ->
  transitionAction leftTransition = OInsert 0 Root component ->
  transitionAction rightTransition = OInsert 0 Root component -> Void
historicalExternalRootPermutationRejected coupling leftRoot rightRoot =
  case firstExternalRootBirthMapped coupling leftRoot rightRoot of
    Refl impossible

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

freshChoiceFinalGenerations : GenerationEnvironment Nat
freshChoiceFinalGenerations =
  [(0, MkRegistrationGeneration 0 0),
   (1, MkRegistrationGeneration 1 5)]

freshChoiceLeftFinalIndex : RegistrationIndexState Nat
freshChoiceLeftFinalIndex = MkRegistrationIndexState
  (putCurrentGeneration @{DGamma.CP3StatementChecks.registrationTestNameEq}
    1 (MkRegistrationGeneration 1 5)
    (deleteCurrentGeneration @{DGamma.CP3StatementChecks.registrationTestNameEq}
      1 (putCurrentGeneration @{DGamma.CP3StatementChecks.registrationTestNameEq}
        1 (MkRegistrationGeneration 1 2)
        (putCurrentGeneration @{DGamma.CP3StatementChecks.registrationTestNameEq}
          0 (MkRegistrationGeneration 0 0) []))))
  (incrementChildrenBornUnder @{DGamma.CP3StatementChecks.registrationTestNameEq}
    (MkRegistrationGeneration 0 0) [])

freshChoiceRightFinalIndex : RegistrationIndexState Nat
freshChoiceRightFinalIndex = MkRegistrationIndexState
  (putCurrentGeneration @{DGamma.CP3StatementChecks.registrationTestNameEq}
    1 (MkRegistrationGeneration 1 5)
    (deleteCurrentGeneration @{DGamma.CP3StatementChecks.registrationTestNameEq}
      2 (putCurrentGeneration @{DGamma.CP3StatementChecks.registrationTestNameEq}
        2 (MkRegistrationGeneration 2 2)
        (putCurrentGeneration @{DGamma.CP3StatementChecks.registrationTestNameEq}
          0 (MkRegistrationGeneration 0 0) []))))
  (incrementChildrenBornUnder @{DGamma.CP3StatementChecks.registrationTestNameEq}
    (MkRegistrationGeneration 0 0) [])

freshChoiceParentIndex : RegistrationIndexState Nat
freshChoiceParentIndex = MkRegistrationIndexState
  [(0, MkRegistrationGeneration 0 0)] []

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
    (namedAction (childInsert left))
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
    (namedAction (childInsert right)) []
    (registrationEventAt @{DGamma.CP3StatementChecks.registrationTestNameEq}
      2 DGamma.CP3StatementChecks.freshChoiceParentIndex 1 0 registrationTestChild)
    []
    (MkRegistrationEventMatch Refl
      (MkRegistrationGeneration 0 0) (MkRegistrationGeneration 0 0)
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
    DGamma.CP3StatementChecks.freshChoiceGenerationBijection
    (namedRoleChangingTrace left) (namedRoleChangingTrace right)
    (freshChoiceRegistrationCorrespondence left right)
freshChoiceCurrentEndpointRenaming left right =
  MkCurrentEndpointRenaming identityNameBijection
    (\n, fiber, found, root => Refl)
    (\n, fiber, found, root => Refl)
    freshChoiceCurrentGenerationForward freshChoiceCurrentGenerationForward

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

public export
allCP3StatementChecks : Bool
allCP3StatementChecks = roleChangingRuntimeCheck &&
  roleChangingCanonicalRuntimeCheck && roleChangingProofTraceCheck &&
  freshChoiceCorrespondenceCheck

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

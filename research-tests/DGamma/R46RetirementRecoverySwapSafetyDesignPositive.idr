module DGamma.R46RetirementRecoverySwapSafetyDesignPositive

import DGamma.Calculus
import DGamma.Core
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP3StatementChecks
import DGamma.Metatheory
import DGamma.Unified
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality
import Data.List.Elem
import Data.Maybe

%default total
%unbound_implicits off

public export
data R46Key : Type where

public export
implementation DecEq R46Key where
  decEq key impossible

public export
R46Value : R46Key -> Type
R46Value key impossible

public export
r46NameEq : DecEq Nat
r46NameEq = %search

public export
r46KeyEq : DecEq R46Key
r46KeyEq = %search

public export
r46Spec : CoeffectSpec R46Key
r46Spec = MkCoeffectSpec [] UniqueNil

public export
r46Component : Component R46Key R46Value Unit String
r46Component = MkComponent r46Spec r46Spec []

public export
r46ParentActive : Fiber Nat R46Key R46Value Unit String
r46ParentActive = setFiberLifecycle (freshFiber r46Component Root)
  (Active id EmptyView)

public export
r46ParentRetiredActive : Fiber Nat R46Key R46Value Unit String
r46ParentRetiredActive = retireFiber r46ParentActive

public export
r46ChildFresh : Fiber Nat R46Key R46Value Unit String
r46ChildFresh = freshFiber r46Component (ChildOf 0)

public export
r46ChildRetired : Fiber Nat R46Key R46Value Unit String
r46ChildRetired = retireFiber r46ChildFresh

public export
r46ParentLeaving : Fiber Nat R46Key R46Value Unit String
r46ParentLeaving = setFiberLifecycle r46ParentRetiredActive
  (Unloading id EmptyView Nothing)

r46ParentRegistry : Registry Nat R46Key R46Value Unit String
r46ParentRegistry = insertBinding 0 r46ParentRetiredActive emptyContext Refl

r46BeforeRegistry : Registry Nat R46Key R46Value Unit String
r46BeforeRegistry = insertBinding 1 r46ChildFresh r46ParentRegistry Refl

r46AfterRetireRegistry : Registry Nat R46Key R46Value Unit String
r46AfterRetireRegistry = replaceBinding 1 r46ChildRetired r46BeforeRegistry

r46SourceFinalRegistry : Registry Nat R46Key R46Value Unit String
r46SourceFinalRegistry = replaceBinding 0 r46ParentLeaving r46AfterRetireRegistry

r46AfterEarlyLeaveRegistry : Registry Nat R46Key R46Value Unit String
r46AfterEarlyLeaveRegistry = replaceBinding 0 r46ParentLeaving r46BeforeRegistry

r46TargetFinalRegistry : Registry Nat R46Key R46Value Unit String
r46TargetFinalRegistry = replaceBinding 1 r46ChildRetired
  r46AfterEarlyLeaveRegistry

public export
r46Before : SystemState Nat R46Key R46Value Unit String
r46Before = MkSystemState () r46BeforeRegistry

public export
r46AfterRetire : SystemState Nat R46Key R46Value Unit String
r46AfterRetire = MkSystemState () r46AfterRetireRegistry

public export
r46SourceFinal : SystemState Nat R46Key R46Value Unit String
r46SourceFinal = MkSystemState () r46SourceFinalRegistry

public export
r46AfterEarlyLeave : SystemState Nat R46Key R46Value Unit String
r46AfterEarlyLeave = MkSystemState () r46AfterEarlyLeaveRegistry

public export
r46TargetFinal : SystemState Nat R46Key R46Value Unit String
r46TargetFinal = MkSystemState () r46TargetFinalRegistry

public export
0 r46BeforeWellFormed : registryWellFormed @{r46NameEq} @{r46KeyEq}
  r46Before = True
r46BeforeWellFormed = Refl

0 r46RetireRaw : applyAction @{r46NameEq} @{r46KeyEq} (ORetire 1) r46Before =
  Just (ORetireTag, r46AfterRetire)
r46RetireRaw = Refl

0 r46RetireChecked : checkedApplyAction @{r46NameEq} @{r46KeyEq} (ORetire 1)
  r46Before = Just (ORetireTag, r46AfterRetire)
r46RetireChecked = rewrite r46RetireRaw in Refl

0 r46LeaveRaw : applyAction @{r46NameEq} @{r46KeyEq} (LLeave 0)
  r46AfterRetire = Just (LLeaveTag, r46SourceFinal)
r46LeaveRaw = Refl

0 r46LeaveChecked : checkedApplyAction @{r46NameEq} @{r46KeyEq} (LLeave 0)
  r46AfterRetire = Just (LLeaveTag, r46SourceFinal)
r46LeaveChecked = rewrite r46LeaveRaw in Refl

0 r46EarlyLeaveRaw : applyAction @{r46NameEq} @{r46KeyEq} (LLeave 0)
  r46Before = Just (LLeaveTag, r46AfterEarlyLeave)
r46EarlyLeaveRaw = Refl

0 r46EarlyLeaveChecked : checkedApplyAction @{r46NameEq} @{r46KeyEq}
  (LLeave 0) r46Before = Just (LLeaveTag, r46AfterEarlyLeave)
r46EarlyLeaveChecked = rewrite r46EarlyLeaveRaw in Refl

0 r46MovedRetireRaw : applyAction @{r46NameEq} @{r46KeyEq} (ORetire 1)
  r46AfterEarlyLeave = Just (ORetireTag, r46TargetFinal)
r46MovedRetireRaw = Refl

0 r46MovedRetireChecked : checkedApplyAction @{r46NameEq} @{r46KeyEq}
  (ORetire 1) r46AfterEarlyLeave = Just (ORetireTag, r46TargetFinal)
r46MovedRetireChecked = rewrite r46MovedRetireRaw in Refl

public export
r46RetireChild : Transition r46Before r46AfterRetire
r46RetireChild = Fired r46NameEq r46KeyEq (ORetire 1) ORetireTag
  r46RetireChecked

public export
r46LeaveParent : Transition r46AfterRetire r46SourceFinal
r46LeaveParent = Fired r46NameEq r46KeyEq (LLeave 0) LLeaveTag
  r46LeaveChecked

public export
r46EarlyLeaveParent : Transition r46Before r46AfterEarlyLeave
r46EarlyLeaveParent = Fired r46NameEq r46KeyEq (LLeave 0) LLeaveTag
  r46EarlyLeaveChecked

public export
r46MovedRetireChild : Transition r46AfterEarlyLeave r46TargetFinal
r46MovedRetireChild = Fired r46NameEq r46KeyEq (ORetire 1) ORetireTag
  r46MovedRetireChecked

public export
0 r46OperationalEndpointsEqual : r46SourceFinal = r46TargetFinal
r46OperationalEndpointsEqual = Refl

public export
r46SourcePair : Transitions r46Before r46SourceFinal
r46SourcePair = MoreTransitions r46RetireChild
  (MoreTransitions r46LeaveParent NoTransitions)

public export
r46TargetPair : Transitions r46Before r46TargetFinal
r46TargetPair = MoreTransitions r46EarlyLeaveParent
  (MoreTransitions r46MovedRetireChild NoTransitions)

public export
0 r46SourceRetirementProvenance :
  ChildRetirementProvenance 0 1 r46SourcePair
r46SourceRetirementProvenance = ChildRetiredBeforeParent
  (ChildRetiresNow r46RetireChild
    (MoreTransitions r46LeaveParent NoTransitions) Refl)

0 parentRecoveryCannotRetire :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle : SystemState name key value world error} ->
  {parent, child : name} -> {transition : Transition first middle} ->
  ParentRecoveryStep parent transition ->
  transitionAction transition = ORetire child -> Void
parentRecoveryCannotRetire (ParentLeaves recovery) retire =
  case trans (sym recovery) retire of Refl impossible
parentRecoveryCannotRetire (ParentDivertsBefore recovery) retire =
  case trans (sym recovery) retire of Refl impossible
parentRecoveryCannotRetire (ParentDivertsAfter recovery tag) retire =
  case trans (sym recovery) retire of Refl impossible
parentRecoveryCannotRetire (ParentRaises recovery tag) retire =
  case trans (sym recovery) retire of Refl impossible

public export
0 r46TargetRetirementProvenanceImpossible :
  ChildRetirementProvenance 0 1 r46TargetPair -> Void
r46TargetRetirementProvenanceImpossible
  (ParentDoesNotRecover
    (NoParentRecoveryStep
      DGamma.R46RetirementRecoverySwapSafetyDesignPositive.r46EarlyLeaveParent
      (MoreTransitions
        DGamma.R46RetirementRecoverySwapSafetyDesignPositive.r46MovedRetireChild
        NoTransitions) noHead tail)) = noHead (ParentLeaves Refl)
r46TargetRetirementProvenanceImpossible
  (ChildRetiredBeforeParent
    (ChildRetiresNow
      DGamma.R46RetirementRecoverySwapSafetyDesignPositive.r46EarlyLeaveParent
      (MoreTransitions
        DGamma.R46RetirementRecoverySwapSafetyDesignPositive.r46MovedRetireChild
        NoTransitions) retires)) =
          parentRecoveryCannotRetire
            (the (ParentRecoveryStep 0 r46EarlyLeaveParent) (ParentLeaves Refl))
            retires
r46TargetRetirementProvenanceImpossible
  (ChildRetiredBeforeParent
    (ChildRetiresLater
      DGamma.R46RetirementRecoverySwapSafetyDesignPositive.r46EarlyLeaveParent
      (MoreTransitions
        DGamma.R46RetirementRecoverySwapSafetyDesignPositive.r46MovedRetireChild
        NoTransitions) noHead later)) = noHead (ParentLeaves Refl)

0 activationCannotLeave :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  {actor : name} ->
  (transition : Transition before afterState) ->
  PaperActivationStep transition ->
  transitionAction transition = LLeave actor -> Void
activationCannotLeave transition (PaperBeginStep action tag) leave =
  case trans (sym action) leave of Refl impossible
activationCannotLeave transition (PaperIterStep action tag) leave =
  case trans (sym action) leave of Refl impossible
activationCannotLeave transition (PaperFinishStep action tag) leave =
  case trans (sym action) leave of Refl impossible

0 orchestrationCannotLeave :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  {actor : name} ->
  (transition : Transition before afterState) ->
  PaperOrchestrationStep transition ->
  transitionAction transition = LLeave actor -> Void
orchestrationCannotLeave transition (PaperInsertStep action) leave =
  case trans (sym action) leave of Refl impossible
orchestrationCannotLeave transition (PaperRetireStep action) leave =
  case trans (sym action) leave of Refl impossible
orchestrationCannotLeave transition (PaperRemoveStep action) leave =
  case trans (sym action) leave of Refl impossible

0 activationCannotRecover :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  {parent : name} ->
  (transition : Transition before afterState) ->
  PaperActivationStep transition -> ParentRecoveryStep parent transition -> Void
activationCannotRecover transition activation (ParentLeaves action) =
  activationCannotLeave transition activation action
activationCannotRecover transition activation (ParentDivertsBefore action) =
  case activation of
    PaperBeginStep begin beginTag =>
      case trans (sym begin) action of Refl impossible
    PaperIterStep iter iterTag =>
      case trans (sym iter) action of Refl impossible
    PaperFinishStep finish finishTag =>
      case trans (sym finish) action of Refl impossible
activationCannotRecover transition activation
  (ParentDivertsAfter action recoveryTag) =
    case activation of
      PaperBeginStep begin beginTag =>
        case trans (sym begin) action of Refl impossible
      PaperIterStep iter iterTag =>
        case trans (sym iterTag) recoveryTag of Refl impossible
      PaperFinishStep finish finishTag =>
        case trans (sym finishTag) recoveryTag of Refl impossible
activationCannotRecover transition activation (ParentRaises action recoveryTag) =
  case activation of
    PaperBeginStep begin beginTag =>
      case trans (sym begin) action of Refl impossible
    PaperIterStep iter iterTag =>
      case trans (sym iterTag) recoveryTag of Refl impossible
    PaperFinishStep finish finishTag =>
      case trans (sym finishTag) recoveryTag of Refl impossible

0 orchestrationCannotRecover :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  {parent : name} ->
  (transition : Transition before afterState) ->
  PaperOrchestrationStep transition -> ParentRecoveryStep parent transition -> Void
orchestrationCannotRecover transition orchestration (ParentLeaves action) =
  orchestrationCannotLeave transition orchestration action
orchestrationCannotRecover transition orchestration
  (ParentDivertsBefore action) =
    case orchestration of
      PaperInsertStep insert => case trans (sym insert) action of Refl impossible
      PaperRetireStep retire => case trans (sym retire) action of Refl impossible
      PaperRemoveStep remove => case trans (sym remove) action of Refl impossible
orchestrationCannotRecover transition orchestration
  (ParentDivertsAfter action tag) =
    case orchestration of
      PaperInsertStep insert => case trans (sym insert) action of Refl impossible
      PaperRetireStep retire => case trans (sym retire) action of Refl impossible
      PaperRemoveStep remove => case trans (sym remove) action of Refl impossible
orchestrationCannotRecover transition orchestration (ParentRaises action tag) =
  case orchestration of
    PaperInsertStep insert => case trans (sym insert) action of Refl impossible
    PaperRetireStep retire => case trans (sym retire) action of Refl impossible
    PaperRemoveStep remove => case trans (sym remove) action of Refl impossible

public export
0 candidateSafetyExcludesParentRecovery :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {left : Transition first middle} ->
  {right : Transition middle finalState} ->
  CandidateRegistrationSwapSafety left right ->
  (child, parent : name) ->
  transitionAction left = ORetire child ->
  ParentRecoveryStep parent right -> Void
candidateSafetyExcludesParentRecovery
  (CandidateActivationActivation leftActivation rightActivation)
  child parent leftRetire rightRecovery =
    activationCannotRecover _ rightActivation rightRecovery
candidateSafetyExcludesParentRecovery
  (CandidateActivationOrchestration leftActivation rightOrchestration parentSafe)
  child parent leftRetire rightRecovery =
    orchestrationCannotRecover _ rightOrchestration rightRecovery
candidateSafetyExcludesParentRecovery
  (CandidateOrchestrationActivation leftOrchestration rightActivation childSafe
    parentSafe) child parent leftRetire rightRecovery =
      activationCannotRecover _ rightActivation rightRecovery
candidateSafetyExcludesParentRecovery
  (CandidateOrchestrationOrchestration leftOrchestration rightOrchestration
    childrenDistinct licensesDoNotCross) child parent leftRetire rightRecovery =
      orchestrationCannotRecover _ rightOrchestration rightRecovery

public export
0 r46NoLandedSafety :
  CandidateRegistrationSwapSafety r46RetireChild r46LeaveParent -> Void
r46NoLandedSafety safety = candidateSafetyExcludesParentRecovery safety 1 0 Refl
  (ParentLeaves Refl)

public export
0 r46NoLiveDiamond :
  LocalRelationalDiamond Nat R46Key Unit String R46Value r46NameEq r46KeyEq
    r46RetireChild r46LeaveParent -> Void
r46NoLiveDiamond diamond = r46NoLandedSafety (registrationSwapSafety diamond)

public export
0 r46LeaveCannotReachGenuineOAProducer :
  PaperActivationStep r46LeaveParent -> Void
r46LeaveCannotReachGenuineOAProducer activation =
  activationCannotLeave r46LeaveParent activation Refl

0 twoStepActionObservation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {selectedBefore, selectedAfter, first, middle, finalState :
    SystemState name key value world error} ->
  (selected : Transition selectedBefore selectedAfter) ->
  (left : Transition first middle) ->
  (right : Transition middle finalState) ->
  OccursIn selected (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  Either (transitionAction selected = transitionAction left)
    (transitionAction selected = transitionAction right)
twoStepActionObservation left left right OccursHere = Left Refl
twoStepActionObservation right left right (OccursLater OccursHere) = Right Refl
twoStepActionObservation selected left right
  (OccursLater (OccursLater later)) = void (noOccurrenceInEmpty later)

0 r46ActualGeneratorIdentity :
  {before, afterState : SystemState Nat R46Key R46Value Unit String} ->
  (nameEq : DecEq Nat) -> (keyEq : DecEq R46Key) ->
  (action : Action Nat R46Key R46Value Unit String) -> (tag : RuleTag) ->
  (equation : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (occurs : OccursIn (Fired {before = before} {afterState = afterState} nameEq keyEq action tag equation) r46SourcePair) ->
  (state : EffectState Nat R46Key R46Value Unit) ->
  partialEffectMapFor nameEq keyEq action tag before state = Just state
r46ActualGeneratorIdentity nameEq keyEq action tag equation occurs state =
  case twoStepActionObservation _ r46RetireChild r46LeaveParent occurs of
    Left actionSame => rewrite actionSame in Refl
    Right actionSame => rewrite actionSame in Refl

0 r46NoAdvanceInPair :
  {before, afterState : SystemState Nat R46Key R46Value Unit String} ->
  (nameEq : DecEq Nat) -> (keyEq : DecEq R46Key) -> (actor : Nat) ->
  (tag : RuleTag) ->
  (equation : checkedApplyAction @{nameEq} @{keyEq} (LAdvance actor) before =
    Just (tag, afterState)) ->
  (occurs : OccursIn (Fired {before = before} {afterState = afterState} nameEq keyEq (LAdvance actor) tag equation)
    r46SourcePair) -> Void
r46NoAdvanceInPair nameEq keyEq actor tag equation occurs =
  case twoStepActionObservation _ r46RetireChild r46LeaveParent occurs of
    Left actionSame => case actionSame of Refl impossible
    Right actionSame => case actionSame of Refl impossible

0 r46GeneratorIdentity :
  {actor : Nat} ->
  (generator : TraceEffectGenerator Nat R46Key Unit String R46Value actor
    r46SourcePair) ->
  (state : EffectState Nat R46Key R46Value Unit) ->
  traceGeneratorMap generator state = Just state
r46GeneratorIdentity
  (ActualForwardGenerator before afterState nameEq keyEq action tag equation
    occurs actorMatches) state =
      r46ActualGeneratorIdentity nameEq keyEq action tag equation occurs state
r46GeneratorIdentity
  (IteratorForwardGenerator
    (StageFromAdvance nameEq keyEq actor tag equation occurs fiber found
      remaining accumulator view lifecycle step rest suffix)) state =
        void (r46NoAdvanceInPair nameEq keyEq actor tag equation occurs)
r46GeneratorIdentity
  (IteratorYieldedGenerator
    (StageFromAdvance nameEq keyEq actor tag equation occurs fiber found
      remaining accumulator view lifecycle step rest suffix) origin) state =
        void (r46NoAdvanceInPair nameEq keyEq actor tag equation occurs)

0 r46TransformationIdentity :
  {actor : Nat} ->
  (transformation : TraceEffectTransformation Nat R46Key Unit String R46Value
    actor r46SourcePair) ->
  (state : EffectState Nat R46Key R46Value Unit) ->
  runTraceEffectTransformation transformation state = Just state
r46TransformationIdentity TraceIdentity state = Refl
r46TransformationIdentity (TraceGenerator generator) state =
  r46GeneratorIdentity generator state
r46TransformationIdentity (TraceCompose after before) state =
  rewrite r46TransformationIdentity before state in
    r46TransformationIdentity after state

public export
0 r46PairIndependent : TraceIndependent Nat R46Key Unit String R46Value r46KeyEq
  r46SourcePair
r46PairIndependent = MkTraceIndependent commute stable
  where
  0 commute :
    (leftActor, rightActor : Nat) -> Not (leftActor = rightActor) ->
    (leftT : TraceEffectTransformation Nat R46Key Unit String R46Value
      leftActor r46SourcePair) ->
    (rightT : TraceEffectTransformation Nat R46Key Unit String R46Value
      rightActor r46SourcePair) ->
    PartialCommute (EffectStateEquivalence r46KeyEq)
      (runTraceEffectTransformation leftT) (runTraceEffectTransformation rightT)
  commute leftActor rightActor distinct leftT rightT =
    effectIdentityOnLeftCommutes r46KeyEq (runTraceEffectTransformation leftT)
      (r46TransformationIdentity leftT) (runTraceEffectTransformation rightT)

  0 stable :
    (leftActor, rightActor : Nat) -> Not (leftActor = rightActor) ->
    (stage : IteratorStage Nat R46Key Unit String R46Value leftActor
      r46SourcePair) ->
    (foreign : TraceEffectTransformation Nat R46Key Unit String R46Value
      rightActor r46SourcePair) ->
    (origin : EffectState Nat R46Key R46Value Unit) ->
    IteratorOutcomeStableUnder r46KeyEq stage
      (runTraceEffectTransformation foreign) origin
  stable leftActor rightActor distinct stage foreign origin =
    rewrite r46TransformationIdentity foreign origin in
      iteratorOutcomeAgreementReflexive r46KeyEq stage origin

public export
0 r46SourcePairAligned : AlignedTransitions Nat R46Key Unit String R46Value
  r46NameEq r46KeyEq r46SourcePair
r46SourcePairAligned = AlignedStep (ORetire 1) ORetireTag r46RetireChecked _
  (AlignedStep (LLeave 0) LLeaveTag r46LeaveChecked NoTransitions AlignedEnd)

public export
0 r46EarlyLeaveAligned : AlignedTransitions Nat R46Key Unit String R46Value
  r46NameEq r46KeyEq (MoreTransitions r46EarlyLeaveParent NoTransitions)
r46EarlyLeaveAligned = AlignedStep (LLeave 0) LLeaveTag
  r46EarlyLeaveChecked NoTransitions AlignedEnd

public export
0 r46LeftOrchestration : PaperOrchestrationStep r46RetireChild
r46LeftOrchestration = PaperRetireStep Refl

public export
0 r46DistinctActors : Not (transitionActor r46RetireChild =
  transitionActor r46LeaveParent)
r46DistinctActors same = case same of Refl impossible

public export
0 r46ChildSafeVacuous :
  (child : Nat) -> (parent : Parent Nat) ->
  (component : Component R46Key R46Value Unit String) ->
  transitionAction r46RetireChild = OInsert child parent component ->
  Not (transitionActor r46LeaveParent = child)
r46ChildSafeVacuous child parent component insertion =
  case insertion of Refl impossible

public export
0 r46ParentSafeVacuous :
  (child, parent : Nat) ->
  (component : Component R46Key R46Value Unit String) ->
  transitionAction r46RetireChild = OInsert child (ChildOf parent) component ->
  Not (transitionActor r46LeaveParent = parent)
r46ParentSafeVacuous child parent component insertion =
  case insertion of Refl impossible

public export
record CandidateRetirementRecoverySafe
  {name, key, world, error : Type} {value : key -> Type}
  {first, middle, finalState : SystemState name key value world error}
  (left : Transition first middle) (right : Transition middle finalState) where
  constructor MkCandidateRetirementRecoverySafe
  0 noRetirementCrossesRecovery :
    (child, parent : name) ->
    transitionAction left = ORetire child ->
    ParentRecoveryStep parent right -> Void

public export
0 retainCandidateRetirementRecoverySafety :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {left : Transition first middle} -> {right : Transition middle finalState} ->
  CandidateRegistrationSwapSafety left right ->
  CandidateRetirementRecoverySafe left right
retainCandidateRetirementRecoverySafety safety =
  MkCandidateRetirementRecoverySafe
    (candidateSafetyExcludesParentRecovery safety)

public export
record CandidateSelectorRestrictedDiamond
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {first, middle, finalState : SystemState name key value world error}
  (left : Transition first middle) (right : Transition middle finalState) where
  constructor MkCandidateSelectorRestrictedDiamond
  candidateBaseDiamond : LocalRelationalDiamond name key world error value nameEq
    keyEq left right
  0 candidateRetirementSafe : CandidateRetirementRecoverySafe left right

public export
0 restrictExistingDiamond :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, finalState : SystemState name key value world error} ->
  {left : Transition first middle} -> {right : Transition middle finalState} ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  CandidateSelectorRestrictedDiamond name key world error value nameEq keyEq
    left right
restrictExistingDiamond nameEq keyEq diamond =
  MkCandidateSelectorRestrictedDiamond diamond
    (retainCandidateRetirementRecoverySafety (registrationSwapSafety diamond))

public export
0 projectRestrictedDiamond :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {left : Transition first middle} -> {right : Transition middle finalState} ->
  CandidateSelectorRestrictedDiamond name key world error value nameEq keyEq
    left right ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
projectRestrictedDiamond restricted = candidateBaseDiamond restricted

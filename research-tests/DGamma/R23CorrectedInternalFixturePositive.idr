module DGamma.R23CorrectedInternalFixturePositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import DGamma.CP3
import DGamma.CP3StatementChecks
import DGamma.CP3Support
import DGamma.CP4Support
import DGamma.CP4SupportSolution
import DGamma.CP4SupportQuiescence
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorEndpoint
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R18ExternalOrderProducerPositive
import DGamma.R21MovedOutputAlignmentScopingPositive
import DGamma.R22QuietnessDomainAuditPositive
import Decidable.Equality
import Data.List.Elem
import Data.Maybe

%default total
%unbound_implicits off

public export
data R23Key : Type where

public export
implementation DecEq R23Key where
  decEq key impossible

public export
R23Value : R23Key -> Type
R23Value key impossible

public export
r23Component : Component R23Key R23Value Unit Unit
r23Component = MkComponent emptySpec emptySpec []

public export
r23Protocol : RegistrationProtocol R23Key R23Value Unit Unit
r23Protocol = MkRegistrationProtocol
  (\tag => Nothing)
  (\component => Just Z)
  (\parent, child, step, tag, parentRank, childRank, occurs, parentRanked,
    childRanked, yields, catalog => case catalog of Refl impossible)
  (\provider, consumer, providerRank, consumerRank, providerRanked,
    consumerRanked, key, provided, required => case key of _ impossible)

public export
r23NameEq : DecEq Nat
r23NameEq = %search

public export
r23KeyEq : DecEq R23Key
r23KeyEq = %search

r23Fresh : Fiber Nat R23Key R23Value Unit Unit
r23Fresh = freshFiber r23Component Root

r23Begun : Fiber Nat R23Key R23Value Unit Unit
r23Begun = setFiberLifecycle r23Fresh (Reloading [] id EmptyView)

r23Active : Fiber Nat R23Key R23Value Unit Unit
r23Active = setFiberLifecycle r23Begun (Active id EmptyView)

r23InitialRegistry : Registry Nat R23Key R23Value Unit Unit
r23InitialRegistry = emptyContext

r23AfterInsert1Registry : Registry Nat R23Key R23Value Unit Unit
r23AfterInsert1Registry = insertBinding 1 r23Fresh r23InitialRegistry Refl

r23AfterInsert2Registry : Registry Nat R23Key R23Value Unit Unit
r23AfterInsert2Registry = insertBinding 2 r23Fresh r23AfterInsert1Registry Refl

r23AfterBegin1Registry : Registry Nat R23Key R23Value Unit Unit
r23AfterBegin1Registry = replaceBinding 1 r23Begun r23AfterInsert2Registry

r23AfterPairRegistry : Registry Nat R23Key R23Value Unit Unit
r23AfterPairRegistry = replaceBinding 2 r23Begun r23AfterBegin1Registry

r23AfterEarlyBegin2Registry : Registry Nat R23Key R23Value Unit Unit
r23AfterEarlyBegin2Registry = replaceBinding 2 r23Begun r23AfterInsert2Registry

r23AfterSwappedPairRegistry : Registry Nat R23Key R23Value Unit Unit
r23AfterSwappedPairRegistry = replaceBinding 1 r23Begun r23AfterEarlyBegin2Registry

r23AfterAdvance1Registry : Registry Nat R23Key R23Value Unit Unit
r23AfterAdvance1Registry = replaceBinding 1 r23Active r23AfterPairRegistry

r23FinalRegistry : Registry Nat R23Key R23Value Unit Unit
r23FinalRegistry = replaceBinding 2 r23Active r23AfterAdvance1Registry

r23Initial : SystemState Nat R23Key R23Value Unit Unit
r23Initial = MkSystemState () r23InitialRegistry

r23AfterInsert1 : SystemState Nat R23Key R23Value Unit Unit
r23AfterInsert1 = MkSystemState () r23AfterInsert1Registry

r23AfterInsert2 : SystemState Nat R23Key R23Value Unit Unit
r23AfterInsert2 = MkSystemState () r23AfterInsert2Registry

r23AfterBegin1 : SystemState Nat R23Key R23Value Unit Unit
r23AfterBegin1 = MkSystemState () r23AfterBegin1Registry

r23AfterPair : SystemState Nat R23Key R23Value Unit Unit
r23AfterPair = MkSystemState () r23AfterPairRegistry

r23AfterEarlyBegin2 : SystemState Nat R23Key R23Value Unit Unit
r23AfterEarlyBegin2 = MkSystemState () r23AfterEarlyBegin2Registry

r23AfterSwappedPair : SystemState Nat R23Key R23Value Unit Unit
r23AfterSwappedPair = MkSystemState () r23AfterSwappedPairRegistry

r23AfterAdvance1 : SystemState Nat R23Key R23Value Unit Unit
r23AfterAdvance1 = MkSystemState () r23AfterAdvance1Registry

r23Final : SystemState Nat R23Key R23Value Unit Unit
r23Final = MkSystemState () r23FinalRegistry

0 r23InitialWellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23Initial = True
r23InitialWellFormed = Refl

0 r23Insert1Raw :
  applyAction @{r23NameEq} @{r23KeyEq} (OInsert 1 Root r23Component)
    r23Initial = Just (OInsertTag, r23AfterInsert1)
r23Insert1Raw = Refl

0 r23AfterInsert1WellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23AfterInsert1 = True
r23AfterInsert1WellFormed = preservationTheoremProof r23NameEq r23KeyEq
  (OInsert 1 Root r23Component) r23Initial r23AfterInsert1 OInsertTag
  r23InitialWellFormed r23Insert1Raw

0 r23Insert1Checked :
  checkedApplyAction @{r23NameEq} @{r23KeyEq} (OInsert 1 Root r23Component)
    r23Initial = Just (OInsertTag, r23AfterInsert1)
r23Insert1Checked = rewrite r23Insert1Raw in Refl

0 r23Insert2Raw :
  applyAction @{r23NameEq} @{r23KeyEq} (OInsert 2 Root r23Component)
    r23AfterInsert1 = Just (OInsertTag, r23AfterInsert2)
r23Insert2Raw = Refl

0 r23AfterInsert2WellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23AfterInsert2 = True
r23AfterInsert2WellFormed = preservationTheoremProof r23NameEq r23KeyEq
  (OInsert 2 Root r23Component) r23AfterInsert1 r23AfterInsert2 OInsertTag
  r23AfterInsert1WellFormed r23Insert2Raw

0 r23Insert2Checked :
  checkedApplyAction @{r23NameEq} @{r23KeyEq} (OInsert 2 Root r23Component)
    r23AfterInsert1 = Just (OInsertTag, r23AfterInsert2)
r23Insert2Checked = rewrite r23Insert2Raw in Refl

0 r23Begin1Raw : applyAction @{r23NameEq} @{r23KeyEq} (LBegin 1)
  r23AfterInsert2 = Just (LBeginTag, r23AfterBegin1)
r23Begin1Raw = Refl

0 r23AfterBegin1WellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23AfterBegin1 = True
r23AfterBegin1WellFormed = preservationTheoremProof r23NameEq r23KeyEq
  (LBegin 1) r23AfterInsert2 r23AfterBegin1 LBeginTag
  r23AfterInsert2WellFormed r23Begin1Raw

0 r23Begin1Checked :
  checkedApplyAction @{r23NameEq} @{r23KeyEq} (LBegin 1) r23AfterInsert2 =
    Just (LBeginTag, r23AfterBegin1)
r23Begin1Checked = rewrite r23Begin1Raw in Refl

0 r23Begin2Raw : applyAction @{r23NameEq} @{r23KeyEq} (LBegin 2)
  r23AfterBegin1 = Just (LBeginTag, r23AfterPair)
r23Begin2Raw = Refl

0 r23AfterPairWellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23AfterPair = True
r23AfterPairWellFormed = preservationTheoremProof r23NameEq r23KeyEq
  (LBegin 2) r23AfterBegin1 r23AfterPair LBeginTag
  r23AfterBegin1WellFormed r23Begin2Raw

0 r23Begin2Checked :
  checkedApplyAction @{r23NameEq} @{r23KeyEq} (LBegin 2) r23AfterBegin1 =
    Just (LBeginTag, r23AfterPair)
r23Begin2Checked = rewrite r23Begin2Raw in Refl

0 r23EarlyBegin2Raw : applyAction @{r23NameEq} @{r23KeyEq} (LBegin 2)
  r23AfterInsert2 = Just (LBeginTag, r23AfterEarlyBegin2)
r23EarlyBegin2Raw = Refl

0 r23AfterEarlyBegin2WellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23AfterEarlyBegin2 = True
r23AfterEarlyBegin2WellFormed = preservationTheoremProof r23NameEq r23KeyEq
  (LBegin 2) r23AfterInsert2 r23AfterEarlyBegin2 LBeginTag
  r23AfterInsert2WellFormed r23EarlyBegin2Raw

0 r23EarlyBegin2Checked :
  checkedApplyAction @{r23NameEq} @{r23KeyEq} (LBegin 2) r23AfterInsert2 =
    Just (LBeginTag, r23AfterEarlyBegin2)
r23EarlyBegin2Checked = rewrite r23EarlyBegin2Raw in Refl

0 r23MovedBegin1Raw : applyAction @{r23NameEq} @{r23KeyEq} (LBegin 1)
  r23AfterEarlyBegin2 = Just (LBeginTag, r23AfterSwappedPair)
r23MovedBegin1Raw = Refl

0 r23AfterSwappedPairWellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23AfterSwappedPair = True
r23AfterSwappedPairWellFormed = preservationTheoremProof r23NameEq r23KeyEq
  (LBegin 1) r23AfterEarlyBegin2 r23AfterSwappedPair LBeginTag
  r23AfterEarlyBegin2WellFormed r23MovedBegin1Raw

0 r23MovedBegin1Checked :
  checkedApplyAction @{r23NameEq} @{r23KeyEq} (LBegin 1) r23AfterEarlyBegin2 =
    Just (LBeginTag, r23AfterSwappedPair)
r23MovedBegin1Checked = rewrite r23MovedBegin1Raw in Refl

0 r23PairEndpointsEqual : r23AfterSwappedPair = r23AfterPair
r23PairEndpointsEqual = Refl

0 r23Advance1Raw : applyAction @{r23NameEq} @{r23KeyEq} (LAdvance 1)
  r23AfterPair = Just (LFinishTag, r23AfterAdvance1)
r23Advance1Raw = Refl

0 r23AfterAdvance1WellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23AfterAdvance1 = True
r23AfterAdvance1WellFormed = preservationTheoremProof r23NameEq r23KeyEq
  (LAdvance 1) r23AfterPair r23AfterAdvance1 LFinishTag
  r23AfterPairWellFormed r23Advance1Raw

0 r23Advance1Checked :
  checkedApplyAction @{r23NameEq} @{r23KeyEq} (LAdvance 1) r23AfterPair =
    Just (LFinishTag, r23AfterAdvance1)
r23Advance1Checked = rewrite r23Advance1Raw in Refl

0 r23Advance2Raw : applyAction @{r23NameEq} @{r23KeyEq} (LAdvance 2)
  r23AfterAdvance1 = Just (LFinishTag, r23Final)
r23Advance2Raw = Refl

0 r23FinalWellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23Final = True
r23FinalWellFormed = preservationTheoremProof r23NameEq r23KeyEq
  (LAdvance 2) r23AfterAdvance1 r23Final LFinishTag
  r23AfterAdvance1WellFormed r23Advance2Raw

0 r23Advance2Checked :
  checkedApplyAction @{r23NameEq} @{r23KeyEq} (LAdvance 2) r23AfterAdvance1 =
    Just (LFinishTag, r23Final)
r23Advance2Checked = rewrite r23Advance2Raw in Refl

r23Insert1 : Transition r23Initial r23AfterInsert1
r23Insert1 = Fired r23NameEq r23KeyEq (OInsert 1 Root r23Component) OInsertTag
  (rewrite r23Insert1Raw in Refl)

r23Insert2 : Transition r23AfterInsert1 r23AfterInsert2
r23Insert2 = Fired r23NameEq r23KeyEq (OInsert 2 Root r23Component) OInsertTag
  (rewrite r23Insert2Raw in Refl)

r23Begin1 : Transition r23AfterInsert2 r23AfterBegin1
r23Begin1 = Fired r23NameEq r23KeyEq (LBegin 1) LBeginTag
  (rewrite r23Begin1Raw in Refl)

r23Begin2 : Transition r23AfterBegin1 r23AfterPair
r23Begin2 = Fired r23NameEq r23KeyEq (LBegin 2) LBeginTag
  (rewrite r23Begin2Raw in Refl)

r23EarlyBegin2 : Transition r23AfterInsert2 r23AfterEarlyBegin2
r23EarlyBegin2 = Fired r23NameEq r23KeyEq (LBegin 2) LBeginTag
  (rewrite r23EarlyBegin2Raw in Refl)

r23MovedBegin1 : Transition r23AfterEarlyBegin2 r23AfterSwappedPair
r23MovedBegin1 = Fired r23NameEq r23KeyEq (LBegin 1) LBeginTag
  (rewrite r23MovedBegin1Raw in Refl)

r23Advance1 : Transition r23AfterPair r23AfterAdvance1
r23Advance1 = Fired r23NameEq r23KeyEq (LAdvance 1) LFinishTag
  (rewrite r23Advance1Raw in Refl)

r23Advance2 : Transition r23AfterAdvance1 r23Final
r23Advance2 = Fired r23NameEq r23KeyEq (LAdvance 2) LFinishTag
  (rewrite r23Advance2Raw in Refl)

public export
r23SourceTrace : Transitions r23Initial r23Final
r23SourceTrace = MoreTransitions r23Insert1
  (MoreTransitions r23Insert2
    (MoreTransitions r23Begin1
      (MoreTransitions r23Begin2
        (MoreTransitions r23Advance1
          (MoreTransitions r23Advance2 NoTransitions)))))

public export
r23PairPrefix : Transitions r23Initial r23AfterInsert2
r23PairPrefix = MoreTransitions r23Insert1 (MoreTransitions r23Insert2 NoTransitions)

public export
r23Suffix : Transitions r23AfterPair r23Final
r23Suffix = MoreTransitions r23Advance1 (MoreTransitions r23Advance2 NoTransitions)

0 r23ExactDecomposition :
  appendTransitions r23PairPrefix
    (MoreTransitions r23Begin1 (MoreTransitions r23Begin2 r23Suffix)) =
  r23SourceTrace
r23ExactDecomposition = Refl

0 r23Begin1Node : O19BlockNode 1 r23Begin1
r23Begin1Node = O19LifecycleNode Refl

0 r23Begin2Node : O19BlockNode 2 r23Begin2
r23Begin2Node = O19LifecycleNode Refl


0 r23PairAligned : AlignedTransitions Nat R23Key Unit Unit R23Value r23NameEq
  r23KeyEq (MoreTransitions r23Begin1 (MoreTransitions r23Begin2 NoTransitions))
r23PairAligned = AlignedStep (LBegin 1) LBeginTag r23Begin1Checked
  (MoreTransitions r23Begin2 NoTransitions)
  (AlignedStep (LBegin 2) LBeginTag r23Begin2Checked NoTransitions AlignedEnd)

0 r23EarlyBegin2Aligned : AlignedTransitions Nat R23Key Unit Unit R23Value
  r23NameEq r23KeyEq (MoreTransitions r23EarlyBegin2 NoTransitions)
r23EarlyBegin2Aligned = AlignedStep (LBegin 2) LBeginTag
  r23EarlyBegin2Checked NoTransitions AlignedEnd

0 twoStepActionTagObservation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {selectedBefore, selectedAfter, first, middle, finalState :
    SystemState name key value world error} ->
  (selected : Transition selectedBefore selectedAfter) ->
  (left : Transition first middle) ->
  (right : Transition middle finalState) ->
  OccursIn selected (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  Either
    (transitionAction selected = transitionAction left,
     transitionTag selected = transitionTag left)
    (transitionAction selected = transitionAction right,
     transitionTag selected = transitionTag right)
twoStepActionTagObservation left left right OccursHere = Left (Refl, Refl)
twoStepActionTagObservation right left right (OccursLater OccursHere) =
  Right (Refl, Refl)
twoStepActionTagObservation selected left right
  (OccursLater (OccursLater later)) = void (noOccurrenceInEmpty later)

0 r23ActualPairGeneratorIdentity :
  {before, afterState : SystemState Nat R23Key R23Value Unit Unit} ->
  (nameEq : DecEq Nat) -> (keyEq : DecEq R23Key) ->
  (action : Action Nat R23Key R23Value Unit Unit) -> (tag : RuleTag) ->
  (equation : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (occurs : OccursIn (Fired {before = before} {afterState = afterState}
    nameEq keyEq action tag equation)
    (MoreTransitions r23Begin1 (MoreTransitions r23Begin2 NoTransitions))) ->
  (state : EffectState Nat R23Key R23Value Unit) ->
  partialEffectMapFor nameEq keyEq action tag before state = Just state
r23ActualPairGeneratorIdentity nameEq keyEq action tag equation occurs state =
  case twoStepActionTagObservation _ r23Begin1 r23Begin2 occurs of
    Left (actionSame, tagSame) => rewrite actionSame in Refl
    Right (actionSame, tagSame) => rewrite actionSame in Refl

0 r23NoAdvanceInPair :
  {before, afterState : SystemState Nat R23Key R23Value Unit Unit} ->
  (nameEq : DecEq Nat) -> (keyEq : DecEq R23Key) -> (actor : Nat) ->
  (tag : RuleTag) ->
  (equation : checkedApplyAction @{nameEq} @{keyEq} (LAdvance actor) before =
    Just (tag, afterState)) ->
  (occurs : OccursIn (Fired {before = before} {afterState = afterState}
    nameEq keyEq (LAdvance actor) tag equation)
    (MoreTransitions r23Begin1 (MoreTransitions r23Begin2 NoTransitions))) -> Void
r23NoAdvanceInPair nameEq keyEq actor tag equation occurs =
  case twoStepActionTagObservation _ r23Begin1 r23Begin2 occurs of
    Left (actionSame, tagSame) => case actionSame of Refl impossible
    Right (actionSame, tagSame) => case actionSame of Refl impossible

0 r23PairGeneratorIdentity :
  {actor : Nat} ->
  (generator : TraceEffectGenerator Nat R23Key Unit Unit R23Value actor
    (MoreTransitions r23Begin1 (MoreTransitions r23Begin2 NoTransitions))) ->
  (state : EffectState Nat R23Key R23Value Unit) ->
  traceGeneratorMap generator state = Just state
r23PairGeneratorIdentity
  (ActualForwardGenerator before afterState nameEq keyEq action tag equation
    occurs actorMatches) state =
      r23ActualPairGeneratorIdentity nameEq keyEq action tag equation occurs state
r23PairGeneratorIdentity
  (IteratorForwardGenerator
    (StageFromAdvance nameEq keyEq actor tag equation occurs fiber found
      remaining accumulator view lifecycle step rest suffix)) state =
        void (r23NoAdvanceInPair nameEq keyEq actor tag equation occurs)
r23PairGeneratorIdentity
  (IteratorYieldedGenerator
    (StageFromAdvance nameEq keyEq actor tag equation occurs fiber found
      remaining accumulator view lifecycle step rest suffix) origin) state =
        void (r23NoAdvanceInPair nameEq keyEq actor tag equation occurs)

0 r23PairTransformationIdentity :
  {actor : Nat} ->
  (transformation : TraceEffectTransformation Nat R23Key Unit Unit R23Value actor
    (MoreTransitions r23Begin1 (MoreTransitions r23Begin2 NoTransitions))) ->
  (state : EffectState Nat R23Key R23Value Unit) ->
  runTraceEffectTransformation transformation state = Just state
r23PairTransformationIdentity TraceIdentity state = Refl
r23PairTransformationIdentity (TraceGenerator generator) state =
  r23PairGeneratorIdentity generator state
r23PairTransformationIdentity (TraceCompose after before) state =
  rewrite r23PairTransformationIdentity before state in
    r23PairTransformationIdentity after state

0 r23PairIndependent : TraceIndependent Nat R23Key Unit Unit R23Value r23KeyEq
  (MoreTransitions r23Begin1 (MoreTransitions r23Begin2 NoTransitions))
r23PairIndependent = MkTraceIndependent commute stable
  where
  0 commute :
    (left, right : Nat) -> Not (left = right) ->
    (leftT : TraceEffectTransformation Nat R23Key Unit Unit R23Value left
      (MoreTransitions r23Begin1 (MoreTransitions r23Begin2 NoTransitions))) ->
    (rightT : TraceEffectTransformation Nat R23Key Unit Unit R23Value right
      (MoreTransitions r23Begin1 (MoreTransitions r23Begin2 NoTransitions))) ->
    PartialCommute (EffectStateEquivalence r23KeyEq)
      (runTraceEffectTransformation leftT) (runTraceEffectTransformation rightT)
  commute left right distinct leftT rightT =
    effectIdentityOnLeftCommutes r23KeyEq (runTraceEffectTransformation leftT)
      (r23PairTransformationIdentity leftT)
      (runTraceEffectTransformation rightT)

  0 stable :
    (left, right : Nat) -> Not (left = right) ->
    (stage : IteratorStage Nat R23Key Unit Unit R23Value left
      (MoreTransitions r23Begin1 (MoreTransitions r23Begin2 NoTransitions))) ->
    (foreign : TraceEffectTransformation Nat R23Key Unit Unit R23Value right
      (MoreTransitions r23Begin1 (MoreTransitions r23Begin2 NoTransitions))) ->
    (origin : EffectState Nat R23Key R23Value Unit) ->
    IteratorOutcomeStableUnder r23KeyEq stage
      (runTraceEffectTransformation foreign) origin
  stable left right distinct stage foreign origin =
    rewrite r23PairTransformationIdentity foreign origin in
      iteratorOutcomeAgreementReflexive r23KeyEq stage origin

public export
0 r23Diamond : LocalRelationalDiamond Nat R23Key Unit Unit R23Value r23NameEq
  r23KeyEq r23Begin1 r23Begin2
r23Diamond = activationActivationDiamondSpike r23NameEq r23KeyEq r23Begin1
  r23Begin2 r23EarlyBegin2 r23PairAligned r23EarlyBegin2Aligned Refl Refl
  (PaperBeginStep Refl Refl) (PaperBeginStep Refl Refl)
  (\same => case same of Refl impossible) r23AfterInsert2WellFormed
  r23PairIndependent

||| Revision 25 test-local prototype of combined-boundary field A.  The base is
||| definitionally the existing R23 diamond; its erased alignment is populated
||| only from the exact moved-left checked equation created by that same concrete
||| A/A producer invocation and the already checked early-right singleton.
0 r25SealConcreteMoved :
  (moved : Transition (swappedMiddle r23Diamond) (swappedFinal r23Diamond)) ->
  (0 exactMoved : moved === movedLeft r23Diamond) ->
  CandidateAlignedLocalRelationalDiamond Nat R23Key Unit Unit R23Value
    r23NameEq r23KeyEq r23Begin1 r23Begin2
r25SealConcreteMoved
  (Fired storedNameEq storedKeyEq movedAction movedTag movedChecked) exactMoved =
    case exactMoved of
      Refl => sealAlignedLocalRelationalDiamond r23Diamond
        (activationActivationConstructorMovedAlignment r23NameEq r23KeyEq
          r23EarlyBegin2 r23EarlyBegin2Aligned movedAction movedTag movedChecked)

public export
0 r25AlignedDiamond : CandidateAlignedLocalRelationalDiamond Nat R23Key Unit Unit
  R23Value r23NameEq r23KeyEq r23Begin1 r23Begin2
r25AlignedDiamond = r25SealConcreteMoved (movedLeft r23Diamond) Refl

||| The envelope is a conservative producer wrapper, not a second diamond.
||| All existing replay terms continue to index the very same base projection.
public export
0 r25BaseIsR23 : baseDiamond r25AlignedDiamond = r23Diamond
r25BaseIsR23 = Refl

0 r23PairExternalOrder : SameExternalOrchestration r23NameEq
  (MoreTransitions r23Begin1 (MoreTransitions r23Begin2 NoTransitions))
  (MoreTransitions (movedRight r23Diamond)
    (MoreTransitions (movedLeft r23Diamond) NoTransitions))
r23PairExternalOrder =
  let 0 movedRightInternal : RootOrchestrationStep r23NameEq
          (movedRight r23Diamond) -> Void
      movedRightInternal = lifecycleCannotBeRoot (movedRight r23Diamond)
        (trans (cong isLifecycleAction (movedRightAction r23Diamond)) Refl)
      0 movedLeftInternal : RootOrchestrationStep r23NameEq
          (movedLeft r23Diamond) -> Void
      movedLeftInternal = lifecycleCannotBeRoot (movedLeft r23Diamond)
        (trans (cong isLifecycleAction (movedLeftAction r23Diamond)) Refl)
  in SkipLeftInternal r23Begin1 (MoreTransitions r23Begin2 NoTransitions)
       (lifecycleCannotBeRoot r23Begin1 Refl)
       (SkipLeftInternal r23Begin2 NoTransitions
         (lifecycleCannotBeRoot r23Begin2 Refl)
         (SkipRightInternal (movedRight r23Diamond)
           (MoreTransitions (movedLeft r23Diamond) NoTransitions)
           movedRightInternal
           (SkipRightInternal (movedLeft r23Diamond) NoTransitions
             movedLeftInternal SameExternalOrchestrationEnd)))


0 r23SourceAligned : AlignedTransitions Nat R23Key Unit Unit R23Value r23NameEq
  r23KeyEq r23SourceTrace
r23SourceAligned = AlignedStep (OInsert 1 Root r23Component) OInsertTag
  r23Insert1Checked _
  (AlignedStep (OInsert 2 Root r23Component) OInsertTag r23Insert2Checked _
    (AlignedStep (LBegin 1) LBeginTag r23Begin1Checked _
      (AlignedStep (LBegin 2) LBeginTag r23Begin2Checked _
        (AlignedStep (LAdvance 1) LFinishTag r23Advance1Checked _
          (AlignedStep (LAdvance 2) LFinishTag r23Advance2Checked
            NoTransitions AlignedEnd)))))

0 r23SourceDiscipline : RegistrationDiscipline r23Protocol r23NameEq
  r23SourceTrace
r23SourceDiscipline = RegistrationDisciplineStep r23Insert1 _ (Z ** Refl)
  (RegistrationDisciplineStep r23Insert2 _ (Z ** Refl)
    (RegistrationDisciplineStep r23Begin1 _ ()
      (RegistrationDisciplineStep r23Begin2 _ ()
        (RegistrationDisciplineStep r23Advance1 _ ()
          (RegistrationDisciplineStep r23Advance2 NoTransitions ()
            RegistrationDisciplineEnd)))))

0 r23InitialEmpty : bindings (registry r23Initial) = []
r23InitialEmpty = Refl

0 r23FinalQuiet : quiet @{r23NameEq} @{r23KeyEq} r23Final = True
r23FinalQuiet = Refl

0 r23FinalNoFailure : noFailedFibers r23Final = True
r23FinalNoFailure = Refl

0 r23AnyTransitionTotal :
  {before, afterState : SystemState Nat R23Key R23Value Unit Unit} ->
  (transition : Transition before afterState) ->
  TransitionComponentTotal r23NameEq r23KeyEq transition
r23AnyTransitionTotal transition fiber found active key occurrence =
  case key of _ impossible

0 r23Insert1Total : TransitionComponentTotal r23NameEq r23KeyEq r23Insert1
r23Insert1Total = r23AnyTransitionTotal r23Insert1

0 r23Insert2Total : TransitionComponentTotal r23NameEq r23KeyEq r23Insert2
r23Insert2Total = r23AnyTransitionTotal r23Insert2

0 r23Begin1Total : TransitionComponentTotal r23NameEq r23KeyEq r23Begin1
r23Begin1Total = r23AnyTransitionTotal r23Begin1

0 r23Begin2Total : TransitionComponentTotal r23NameEq r23KeyEq r23Begin2
r23Begin2Total = r23AnyTransitionTotal r23Begin2

0 r23Advance1Total : TransitionComponentTotal r23NameEq r23KeyEq r23Advance1
r23Advance1Total = r23AnyTransitionTotal r23Advance1

0 r23Advance2Total : TransitionComponentTotal r23NameEq r23KeyEq r23Advance2
r23Advance2Total = r23AnyTransitionTotal r23Advance2

0 r23SourceTotal : TraceComponentsTotal r23NameEq r23KeyEq r23SourceTrace
r23SourceTotal = TraceComponentsTotalStep r23Insert1 _ r23Insert1Total
  (TraceComponentsTotalStep r23Insert2 _ r23Insert2Total
    (TraceComponentsTotalStep r23Begin1 _ r23Begin1Total
      (TraceComponentsTotalStep r23Begin2 _ r23Begin2Total
        (TraceComponentsTotalStep r23Advance1 _ r23Advance1Total
          (TraceComponentsTotalStep r23Advance2 NoTransitions r23Advance2Total
            TraceComponentsTotalEnd)))))


public export
record TransitionBoundaryObservation
  {name, key, world, error : Type} {value : key -> Type}
  {selectedBefore, selectedAfter, headBefore, headAfter :
    SystemState name key value world error}
  (selected : Transition selectedBefore selectedAfter)
  (head : Transition headBefore headAfter) where
  constructor MkTransitionBoundaryObservation
  0 boundaryBeforeExact : selectedBefore = headBefore
  0 boundaryActionExact : transitionAction selected = transitionAction head
  0 boundaryTagExact : transitionTag selected = transitionTag head

0 headOrTailBoundaryObservation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {selectedBefore, selectedAfter, first, middle, finalState :
    SystemState name key value world error} ->
  (selected : Transition selectedBefore selectedAfter) ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  OccursIn selected (MoreTransitions head rest) ->
  Either (TransitionBoundaryObservation selected head) (OccursIn selected rest)
headOrTailBoundaryObservation head head rest OccursHere =
  Left (MkTransitionBoundaryObservation Refl Refl Refl)
headOrTailBoundaryObservation selected head rest (OccursLater later) = Right later

public export
data R23SourcePosition :
  SystemState Nat R23Key R23Value Unit Unit ->
  Action Nat R23Key R23Value Unit Unit -> RuleTag -> Type where
  R23AtInsert1 : R23SourcePosition r23Initial
    (OInsert 1 Root r23Component) OInsertTag
  R23AtInsert2 : R23SourcePosition r23AfterInsert1
    (OInsert 2 Root r23Component) OInsertTag
  R23AtBegin1 : R23SourcePosition r23AfterInsert2 (LBegin 1) LBeginTag
  R23AtBegin2 : R23SourcePosition r23AfterBegin1 (LBegin 2) LBeginTag
  R23AtAdvance1 : R23SourcePosition r23AfterPair (LAdvance 1) LFinishTag
  R23AtAdvance2 : R23SourcePosition r23AfterAdvance1 (LAdvance 2) LFinishTag

0 r23ObserveAs :
  {before, expectedBefore : SystemState Nat R23Key R23Value Unit Unit} ->
  {action, expectedAction : Action Nat R23Key R23Value Unit Unit} ->
  {tag, expectedTag : RuleTag} ->
  before = expectedBefore -> action = expectedAction -> tag = expectedTag ->
  R23SourcePosition expectedBefore expectedAction expectedTag ->
  R23SourcePosition before action tag
r23ObserveAs Refl Refl Refl position = position

0 r23SourceOccurrencePosition :
  {before, afterState : SystemState Nat R23Key R23Value Unit Unit} ->
  (nameEq : DecEq Nat) -> (keyEq : DecEq R23Key) ->
  (action : Action Nat R23Key R23Value Unit Unit) -> (tag : RuleTag) ->
  (equation : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  OccursIn (Fired {before = before} {afterState = afterState}
    nameEq keyEq action tag equation) r23SourceTrace ->
  R23SourcePosition before action tag
r23SourceOccurrencePosition nameEq keyEq action tag equation occurs =
  case headOrTailBoundaryObservation _ r23Insert1 _ occurs of
    Left observation => r23ObserveAs (boundaryBeforeExact observation)
      (boundaryActionExact observation) (boundaryTagExact observation)
      R23AtInsert1
    Right afterInsert1 =>
      case headOrTailBoundaryObservation _ r23Insert2 _ afterInsert1 of
        Left observation => r23ObserveAs (boundaryBeforeExact observation)
          (boundaryActionExact observation) (boundaryTagExact observation)
          R23AtInsert2
        Right afterInsert2 =>
          case headOrTailBoundaryObservation _ r23Begin1 _ afterInsert2 of
            Left observation => r23ObserveAs (boundaryBeforeExact observation)
              (boundaryActionExact observation) (boundaryTagExact observation)
              R23AtBegin1
            Right afterBegin1 =>
              case headOrTailBoundaryObservation _ r23Begin2 _ afterBegin1 of
                Left observation => r23ObserveAs
                  (boundaryBeforeExact observation)
                  (boundaryActionExact observation) (boundaryTagExact observation)
                  R23AtBegin2
                Right afterPair =>
                  case headOrTailBoundaryObservation _ r23Advance1 _ afterPair of
                    Left observation => r23ObserveAs
                      (boundaryBeforeExact observation)
                      (boundaryActionExact observation)
                      (boundaryTagExact observation) R23AtAdvance1
                    Right afterAdvance1 =>
                      case headOrTailBoundaryObservation _ r23Advance2 _
                        afterAdvance1 of
                        Left observation => r23ObserveAs
                          (boundaryBeforeExact observation)
                          (boundaryActionExact observation)
                          (boundaryTagExact observation) R23AtAdvance2
                        Right empty => void (noOccurrenceInEmpty empty)

0 iteratorBoundaryImpossible :
  {before, afterState : SystemState Nat R23Key R23Value Unit Unit} ->
  (transition : Transition before afterState) -> Type
iteratorBoundaryImpossible {before}
  (Fired nameEq keyEq action tag equation) =
  (actor : Nat) -> action = LAdvance actor ->
  (fiber : Fiber Nat R23Key R23Value Unit Unit) ->
  lookupFiber @{nameEq} actor (registry before) = Just fiber ->
  (remaining : List (StepEffect R23Key R23Value Unit Unit
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)))) ->
  (accumulator : LocalState R23Key R23Value Unit
    (componentProvisions (fiberComponent fiber)) ->
    LocalState R23Key R23Value Unit
      (componentProvisions (fiberComponent fiber))) ->
  (view : View Nat
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  fiberLifecycle fiber = Reloading remaining accumulator view ->
  (step : StepEffect R23Key R23Value Unit Unit
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (rest : List (StepEffect R23Key R23Value Unit Unit
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)))) ->
  ReachableSuffix remaining (step :: rest) -> Void

0 r23Insert1NotAdvance :
  (actor : Nat) -> transitionAction r23Insert1 = LAdvance actor -> Void
r23Insert1NotAdvance actor Refl impossible

0 r23Insert2NotAdvance :
  (actor : Nat) -> transitionAction r23Insert2 = LAdvance actor -> Void
r23Insert2NotAdvance actor Refl impossible

0 r23Begin1NotAdvance :
  (actor : Nat) -> transitionAction r23Begin1 = LAdvance actor -> Void
r23Begin1NotAdvance actor Refl impossible

0 r23Begin2NotAdvance :
  (actor : Nat) -> transitionAction r23Begin2 = LAdvance actor -> Void
r23Begin2NotAdvance actor Refl impossible

0 r23Insert1BoundaryImpossible : iteratorBoundaryImpossible r23Insert1
r23Insert1BoundaryImpossible actor actionSame fiber found remaining accumulator
  view lifecycle step rest suffix = r23Insert1NotAdvance actor actionSame

0 r23Insert2BoundaryImpossible : iteratorBoundaryImpossible r23Insert2
r23Insert2BoundaryImpossible actor actionSame fiber found remaining accumulator
  view lifecycle step rest suffix = r23Insert2NotAdvance actor actionSame

0 r23Begin1BoundaryImpossible : iteratorBoundaryImpossible r23Begin1
r23Begin1BoundaryImpossible actor actionSame fiber found remaining accumulator
  view lifecycle step rest suffix = r23Begin1NotAdvance actor actionSame

0 r23Begin2BoundaryImpossible : iteratorBoundaryImpossible r23Begin2
r23Begin2BoundaryImpossible actor actionSame fiber found remaining accumulator
  view lifecycle step rest suffix = r23Begin2NotAdvance actor actionSame

0 noNonemptyReachableFromEmpty :
  {a : Type} -> {step : a} -> {rest : List a} ->
  ReachableSuffix [] (step :: rest) -> Void
noNonemptyReachableFromEmpty SuffixHere impossible

0 r23Advance1BoundaryImpossible : iteratorBoundaryImpossible r23Advance1
r23Advance1BoundaryImpossible actor actionSame fiber found remaining accumulator
  view lifecycle step rest suffix = case actionSame of
    Refl => case found of
      Refl => case lifecycle of
        Refl => noNonemptyReachableFromEmpty suffix

0 r23Advance2BoundaryImpossible : iteratorBoundaryImpossible r23Advance2
r23Advance2BoundaryImpossible actor actionSame fiber found remaining accumulator
  view lifecycle step rest suffix = case actionSame of
    Refl => case found of
      Refl => case lifecycle of
        Refl => noNonemptyReachableFromEmpty suffix

public export
data IteratorFreeTrace :
  {first, finalState : SystemState Nat R23Key R23Value Unit Unit} ->
  Transitions first finalState -> Type where
  IteratorFreeEnd : {state : SystemState Nat R23Key R23Value Unit Unit} ->
    IteratorFreeTrace (NoTransitions {state = state})
  IteratorFreeStep :
    {first, middle, finalState : SystemState Nat R23Key R23Value Unit Unit} ->
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    iteratorBoundaryImpossible transition ->
    IteratorFreeTrace rest ->
    IteratorFreeTrace (MoreTransitions transition rest)

0 iteratorFreeTraceHasNoStage :
  {first, finalState : SystemState Nat R23Key R23Value Unit Unit} ->
  {trace : Transitions first finalState} -> {actor : Nat} ->
  (free : IteratorFreeTrace trace) ->
  IteratorStage Nat R23Key Unit Unit R23Value actor trace -> Void
iteratorFreeTraceHasNoStage IteratorFreeEnd
  (StageFromAdvance nameEq keyEq actor tag equation occurs fiber found remaining
    accumulator view lifecycle step tail suffix) = noOccurrenceInEmpty occurs
iteratorFreeTraceHasNoStage
  (IteratorFreeStep _ rest boundary freeRest)
  (StageFromAdvance nameEq keyEq actor tag equation OccursHere fiber found
    remaining accumulator view lifecycle step tail suffix) =
      boundary actor Refl fiber found remaining accumulator view lifecycle step
        tail suffix
iteratorFreeTraceHasNoStage
  (IteratorFreeStep _ rest boundary freeRest)
  (StageFromAdvance nameEq keyEq actor tag equation (OccursLater later) fiber found
    remaining accumulator view lifecycle step tail suffix) =
      iteratorFreeTraceHasNoStage freeRest
        (StageFromAdvance nameEq keyEq actor tag equation later fiber found
          remaining accumulator view lifecycle step tail suffix)

0 r23IteratorFree : IteratorFreeTrace r23SourceTrace
r23IteratorFree = IteratorFreeStep r23Insert1 _ r23Insert1BoundaryImpossible
  (IteratorFreeStep r23Insert2 _ r23Insert2BoundaryImpossible
    (IteratorFreeStep r23Begin1 _ r23Begin1BoundaryImpossible
      (IteratorFreeStep r23Begin2 _ r23Begin2BoundaryImpossible
        (IteratorFreeStep r23Advance1 _ r23Advance1BoundaryImpossible
          (IteratorFreeStep r23Advance2 NoTransitions
            r23Advance2BoundaryImpossible IteratorFreeEnd)))))

0 r23NoSourceIterator :
  {actor : Nat} ->
  IteratorStage Nat R23Key Unit Unit R23Value actor r23SourceTrace -> Void
r23NoSourceIterator = iteratorFreeTraceHasNoStage r23IteratorFree

0 transitionActualMapTotal :
  {before, afterState : SystemState Nat R23Key R23Value Unit Unit} ->
  (transition : Transition before afterState) -> Type
transitionActualMapTotal transition =
  (state : EffectState Nat R23Key R23Value Unit) ->
  (next : EffectState Nat R23Key R23Value Unit **
    partialEffectMap transition state = Just next)

public export
data ActualMapsTotalTrace :
  {first, finalState : SystemState Nat R23Key R23Value Unit Unit} ->
  Transitions first finalState -> Type where
  ActualMapsTotalEnd : {state : SystemState Nat R23Key R23Value Unit Unit} ->
    ActualMapsTotalTrace (NoTransitions {state = state})
  ActualMapsTotalStep :
    {first, middle, finalState : SystemState Nat R23Key R23Value Unit Unit} ->
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    transitionActualMapTotal transition ->
    ActualMapsTotalTrace rest ->
    ActualMapsTotalTrace (MoreTransitions transition rest)

public export
0 actualMapTotalFromTrace :
  {first, finalState : SystemState Nat R23Key R23Value Unit Unit} ->
  {trace : Transitions first finalState} ->
  (maps : ActualMapsTotalTrace trace) ->
  {before, afterState : SystemState Nat R23Key R23Value Unit Unit} ->
  (nameEq : DecEq Nat) -> (keyEq : DecEq R23Key) ->
  (action : Action Nat R23Key R23Value Unit Unit) -> (tag : RuleTag) ->
  (equation : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (occurs : OccursIn (Fired {before = before} {afterState = afterState}
    nameEq keyEq action tag equation) trace) ->
  (state : EffectState Nat R23Key R23Value Unit) ->
  (next : EffectState Nat R23Key R23Value Unit **
    partialEffectMapFor nameEq keyEq action tag before state = Just next)
actualMapTotalFromTrace ActualMapsTotalEnd nameEq keyEq action tag equation occurs
  state = void (noOccurrenceInEmpty occurs)
actualMapTotalFromTrace
  (ActualMapsTotalStep _ rest boundary totalRest)
  nameEq keyEq action tag equation OccursHere state = boundary state
actualMapTotalFromTrace
  (ActualMapsTotalStep _ rest boundary totalRest)
  nameEq keyEq action tag equation (OccursLater later) state =
    actualMapTotalFromTrace totalRest nameEq keyEq action tag equation later state

0 r23Insert1MapTotal : transitionActualMapTotal r23Insert1
r23Insert1MapTotal state = (_ ** Refl)

0 r23Insert2MapTotal : transitionActualMapTotal r23Insert2
r23Insert2MapTotal state = (_ ** Refl)

0 r23Begin1MapTotal : transitionActualMapTotal r23Begin1
r23Begin1MapTotal state = (state ** Refl)

0 r23Begin2MapTotal : transitionActualMapTotal r23Begin2
r23Begin2MapTotal state = (state ** Refl)

0 r23Advance1MapTotal : transitionActualMapTotal r23Advance1
r23Advance1MapTotal state = (state ** Refl)

0 r23Advance2MapTotal : transitionActualMapTotal r23Advance2
r23Advance2MapTotal state = (state ** Refl)

0 r23ActualMapsTotal : ActualMapsTotalTrace r23SourceTrace
r23ActualMapsTotal = ActualMapsTotalStep r23Insert1 _ r23Insert1MapTotal
  (ActualMapsTotalStep r23Insert2 _ r23Insert2MapTotal
    (ActualMapsTotalStep r23Begin1 _ r23Begin1MapTotal
      (ActualMapsTotalStep r23Begin2 _ r23Begin2MapTotal
        (ActualMapsTotalStep r23Advance1 _ r23Advance1MapTotal
          (ActualMapsTotalStep r23Advance2 NoTransitions r23Advance2MapTotal
            ActualMapsTotalEnd)))))

0 r23ActualSourceGeneratorTotal :
  {before, afterState : SystemState Nat R23Key R23Value Unit Unit} ->
  (nameEq : DecEq Nat) -> (keyEq : DecEq R23Key) ->
  (action : Action Nat R23Key R23Value Unit Unit) -> (tag : RuleTag) ->
  (equation : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (occurs : OccursIn (Fired {before = before} {afterState = afterState}
    nameEq keyEq action tag equation) r23SourceTrace) ->
  (state : EffectState Nat R23Key R23Value Unit) ->
  (next : EffectState Nat R23Key R23Value Unit **
    partialEffectMapFor nameEq keyEq action tag before state = Just next)
r23ActualSourceGeneratorTotal = actualMapTotalFromTrace r23ActualMapsTotal

0 r23SourceGeneratorTotal :
  {actor : Nat} ->
  (generator : TraceEffectGenerator Nat R23Key Unit Unit R23Value actor
    r23SourceTrace) ->
  (state : EffectState Nat R23Key R23Value Unit) ->
  (next : EffectState Nat R23Key R23Value Unit **
    traceGeneratorMap generator state = Just next)
r23SourceGeneratorTotal
  (ActualForwardGenerator before afterState nameEq keyEq action tag equation
    occurs actorMatches) state =
      r23ActualSourceGeneratorTotal nameEq keyEq action tag equation occurs state
r23SourceGeneratorTotal (IteratorForwardGenerator stage) state =
  void (r23NoSourceIterator stage)
r23SourceGeneratorTotal (IteratorYieldedGenerator stage origin) state =
  void (r23NoSourceIterator stage)

0 r23SourceTransformationTotal :
  {actor : Nat} ->
  (transformation : TraceEffectTransformation Nat R23Key Unit Unit R23Value actor
    r23SourceTrace) ->
  (state : EffectState Nat R23Key R23Value Unit) ->
  (next : EffectState Nat R23Key R23Value Unit **
    runTraceEffectTransformation transformation state = Just next)
r23SourceTransformationTotal TraceIdentity state = (state ** Refl)
r23SourceTransformationTotal (TraceGenerator generator) state =
  r23SourceGeneratorTotal generator state
r23SourceTransformationTotal (TraceCompose after before) state =
  case r23SourceTransformationTotal before state of
    (middle ** beforeRuns) =>
      case r23SourceTransformationTotal after middle of
        (finalState ** afterRuns) =>
          (finalState ** rewrite beforeRuns in rewrite afterRuns in Refl)

0 r23EmptyKeyContextBindings :
  (context : CoeffectContext R23Key R23Value) -> bindings context = []
r23EmptyKeyContextBindings (MkCoeffectContext [] unique) = Refl
r23EmptyKeyContextBindings (MkCoeffectContext (Bind key value :: rest) unique) =
  case key of _ impossible

0 r23AllEffectStatesRelated :
  (left, right : EffectState Nat R23Key R23Value Unit) ->
  EffectStateRelated r23KeyEq left right
r23AllEffectStatesRelated (MkEffectState () leftTables)
  (MkEffectState () rightTables) = MkEffectStateRelated Refl
    (\selected => trans (r23EmptyKeyContextBindings (leftTables selected))
      (sym (r23EmptyKeyContextBindings (rightTables selected))))

0 r23SourceIndependent : TraceIndependent Nat R23Key Unit Unit R23Value
  r23KeyEq r23SourceTrace
r23SourceIndependent = MkTraceIndependent commute stable
  where
  0 commute :
    (left, right : Nat) -> Not (left = right) ->
    (leftT : TraceEffectTransformation Nat R23Key Unit Unit R23Value left
      r23SourceTrace) ->
    (rightT : TraceEffectTransformation Nat R23Key Unit Unit R23Value right
      r23SourceTrace) ->
    PartialCommute (EffectStateEquivalence r23KeyEq)
      (runTraceEffectTransformation leftT) (runTraceEffectTransformation rightT)
  commute left right distinct leftT rightT state =
    case r23SourceTransformationTotal rightT state of
      (afterRight ** rightRuns) =>
        case r23SourceTransformationTotal leftT afterRight of
          (leftAfterRight ** leftAfterRightRuns) =>
            case r23SourceTransformationTotal leftT state of
              (afterLeft ** leftRuns) =>
                case r23SourceTransformationTotal rightT afterLeft of
                  (rightAfterLeft ** rightAfterLeftRuns) =>
                    rewrite rightRuns in rewrite leftAfterRightRuns in
                    rewrite leftRuns in rewrite rightAfterLeftRuns in
                      PartialDefined
                        (r23AllEffectStatesRelated leftAfterRight rightAfterLeft)

  0 stable :
    (left, right : Nat) -> Not (left = right) ->
    (stage : IteratorStage Nat R23Key Unit Unit R23Value left r23SourceTrace) ->
    (foreign : TraceEffectTransformation Nat R23Key Unit Unit R23Value right
      r23SourceTrace) ->
    (origin : EffectState Nat R23Key R23Value Unit) ->
    IteratorOutcomeStableUnder r23KeyEq stage
      (runTraceEffectTransformation foreign) origin
  stable left right distinct stage foreign origin = void (r23NoSourceIterator stage)


public export
0 r23SourceBundle : ReplayInvariantBundle Nat R23Key Unit Unit R23Value
  r23Protocol r23NameEq r23KeyEq r23SourceTrace
r23SourceBundle =
  let reached : ReachedFromEmpty Nat R23Key Unit Unit R23Value r23NameEq r23KeyEq
        r23Final
      reached = MkReachedFromEmpty r23Initial r23SourceTrace r23SourceAligned
        r23InitialEmpty r23InitialWellFormed
      0 provenance : RegistrationProvenance r23Protocol r23NameEq r23SourceTrace
      provenance = registrationDisciplineProvenance r23Protocol r23NameEq
        r23SourceTrace r23SourceDiscipline
      0 ranked : RegistryProtocolRanked r23Protocol r23NameEq r23Final
      ranked = reachedRegistryProtocolRanked r23Protocol r23NameEq r23KeyEq
        reached provenance
      0 parentRanks : RegistryParentRanksIncrease r23Protocol r23NameEq r23Final
      parentRanks = reachedRegistryParentRanksIncrease r23Protocol r23NameEq
        r23KeyEq reached provenance
      0 acyclic : PrecedenceAcyclic r23NameEq r23Final
      acyclic = disciplinedEndpointPrecedenceAcyclic r23Protocol r23NameEq
        r23KeyEq r23Final reached r23SourceDiscipline
      0 supportWellFounded : SupportWellFounded r23NameEq r23Final
      supportWellFounded = supportCombinedWellFounded r23Protocol r23NameEq
        r23Final ranked parentRanks
      0 supportMatches : SupportMatchesActive r23NameEq r23KeyEq r23Final
      supportMatches = deletionPremisesGiveSupportMatchesActive r23Protocol
        r23NameEq r23KeyEq r23Initial r23Final r23SourceTrace r23SourceAligned
        r23SourceDiscipline r23InitialWellFormed r23InitialEmpty r23FinalQuiet
        r23FinalNoFailure r23SourceTotal
  in MkReplayInvariantBundle r23SourceAligned r23SourceDiscipline
       r23InitialWellFormed r23InitialEmpty r23FinalWellFormed r23FinalQuiet
       r23FinalNoFailure r23SourceTotal r23SourceIndependent provenance ranked
       parentRanks acyclic supportWellFounded supportMatches


-- Revision 24: declaration-local, pointwise replay of the two checked suffix
-- heads.  Ordered registry control is deliberately absent from every type.

0 controlEquivalentAfterRelatedReplacement :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (leftWorld, rightWorld : world) ->
  (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftOld, rightOld, leftNext, rightNext : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor leftRegistry = Just leftOld ->
  lookupFiber @{nameEq} actor rightRegistry = Just rightOld ->
  FiberControlRelated leftNext rightNext ->
  ControlEquivalent name key world error value nameEq
    (MkSystemState leftWorld leftRegistry)
    (MkSystemState rightWorld rightRegistry) ->
  ControlEquivalent name key world error value nameEq
    (MkSystemState leftWorld
      (replaceBinding @{nameEq} actor leftNext leftRegistry))
    (MkSystemState rightWorld
      (replaceBinding @{nameEq} actor rightNext rightRegistry))
controlEquivalentAfterRelatedReplacement nameEq actor leftWorld rightWorld
  leftRegistry rightRegistry leftOld rightOld leftNext rightNext leftFound
  rightFound nextRelated controls = MkControlEquivalent pointwise
  where
  0 pointwise : (selected : name) -> FiberControlMaybeRelated
    {name = name} {key = key} {value = value} {world = world} {error = error}
    (lookupFiber @{nameEq} selected
      (replaceBinding @{nameEq} actor leftNext leftRegistry))
    (lookupFiber @{nameEq} selected
      (replaceBinding @{nameEq} actor rightNext rightRegistry))
  pointwise selected with (decEq @{nameEq} selected actor)
    pointwise selected | Yes same = case same of
      Refl => rewrite lookupReplacedFiber actor leftOld leftNext leftRegistry
        leftFound in rewrite lookupReplacedFiber actor rightOld rightNext
          rightRegistry rightFound in SomeControlFibers nextRelated
    pointwise selected | No distinct =
      rewrite lookupReplaceOther selected actor distinct leftNext leftRegistry in
      rewrite lookupReplaceOther selected actor distinct rightNext rightRegistry in
        controlPointwise controls selected

r24ReplaceActive : Nat -> Registry Nat R23Key R23Value Unit Unit ->
  Registry Nat R23Key R23Value Unit Unit
r24ReplaceActive actor registry = replaceBinding @{r23NameEq} actor r23Active
  registry

record R24DerivedTargetFinish
  (actor : Nat)
  (replayedBefore : SystemState Nat R23Key R23Value Unit Unit)
  (oldFiber : Fiber Nat R23Key R23Value Unit Unit)
  (oldFound : lookupFiber @{r23NameEq} actor (registry replayedBefore) =
    Just oldFiber) where
  constructor MkR24DerivedTargetFinish
  nextFiber : Fiber Nat R23Key R23Value Unit Unit
  targetState : SystemState Nat R23Key R23Value Unit Unit
  0 targetStateExact : targetState = MkSystemState (worldState replayedBefore)
    (replaceBinding @{r23NameEq} actor nextFiber (registry replayedBefore))
  0 targetRaw : applyAction @{r23NameEq} @{r23KeyEq} (LAdvance actor)
    replayedBefore = Just (LFinishTag, targetState)
  0 oldAccumulator : LocalState R23Key R23Value Unit
    (componentProvisions (fiberComponent oldFiber)) ->
    LocalState R23Key R23Value Unit
      (componentProvisions (fiberComponent oldFiber))
  0 oldView : View Nat
    (dependencies (componentDependencies (fiberComponent oldFiber)))
  0 oldLifecycleExact : fiberLifecycle oldFiber =
    Reloading [] oldAccumulator oldView
  0 sourceToNextControl : FiberControlRelated r23Active nextFiber

0 r24DeriveTargetFinish :
  (actor : Nat) ->
  (replayedBefore : SystemState Nat R23Key R23Value Unit Unit) ->
  (oldFiber : Fiber Nat R23Key R23Value Unit Unit) ->
  (oldFound : lookupFiber @{r23NameEq} actor (registry replayedBefore) =
    Just oldFiber) ->
  FiberControlRelated oldFiber r23Begun ->
  R24DerivedTargetFinish actor replayedBefore oldFiber oldFound
r24DeriveTargetFinish actor (MkSystemState replayedWorld replayedRegistry)
  (MkFiber _ targetParent targetRetired targetTable targetLifecycle)
  oldFound
  (FibersControlRelated targetParent Root targetRetired False targetTable
    _ targetLifecycle (Reloading [] _ EmptyView) parentSame
    retiredSame lifecycleRelated) = case retiredSame of
      Refl => case lifecycleRelated of
        ReloadingControls {leftAccumulator = targetAccumulator}
          {leftView = targetView} remainingSame accumulatorsSame viewSame =>
            case remainingSame of
              Refl => case viewSame of
                Refl =>
                  let next : Fiber Nat R23Key R23Value Unit Unit
                      next = MkFiber r23Component targetParent False targetTable
                        (Active targetAccumulator targetView)
                      after : SystemState Nat R23Key R23Value Unit Unit
                      after = MkSystemState replayedWorld
                        (replaceBinding @{r23NameEq} actor next replayedRegistry)
                      0 raw : applyAction @{r23NameEq} @{r23KeyEq}
                        (LAdvance actor)
                        (MkSystemState replayedWorld replayedRegistry) =
                          Just (LFinishTag, after)
                      raw = rewrite oldFound in Refl
                      0 nextRelated : FiberControlRelated r23Active next
                      nextRelated = FibersControlRelated Root targetParent False
                        False (fiberTable r23Begun) targetTable
                        (Active id EmptyView)
                        (Active targetAccumulator targetView) (sym parentSame)
                        Refl (ActiveControls {error = Unit}
                          (\input => localStateRuntimeSymmetric
                            (accumulatorsSame input)) Refl)
                  in MkR24DerivedTargetFinish next after Refl raw
                    targetAccumulator targetView Refl nextRelated

0 r24SingletonOccursSelected :
  {selectedBefore, selectedAfter, first, finalState :
    SystemState Nat R23Key R23Value Unit Unit} ->
  {selected : Transition selectedBefore selectedAfter} ->
  {only : Transition first finalState} ->
  OccursIn selected (MoreTransitions only NoTransitions) -> selected = only
r24SingletonOccursSelected OccursHere = Refl
r24SingletonOccursSelected (OccursLater later) impossible

0 r24EmptyFinishNoIterator :
  (actor : Nat) ->
  (before, afterState : SystemState Nat R23Key R23Value Unit Unit) ->
  (checked : checkedApplyAction @{r23NameEq} @{r23KeyEq} (LAdvance actor)
    before = Just (LFinishTag, afterState)) ->
  (oldFiber : Fiber Nat R23Key R23Value Unit Unit) ->
  (found : lookupFiber @{r23NameEq} actor (registry before) = Just oldFiber) ->
  (accumulator : LocalState R23Key R23Value Unit
    (componentProvisions (fiberComponent oldFiber)) ->
    LocalState R23Key R23Value Unit
      (componentProvisions (fiberComponent oldFiber))) ->
  (view : View Nat
    (dependencies (componentDependencies (fiberComponent oldFiber)))) ->
  fiberLifecycle oldFiber = Reloading [] accumulator view ->
  (selected : Nat) -> IteratorStage Nat R23Key Unit Unit R23Value selected
    (MoreTransitions
      (Fired {before = before} {afterState = afterState}
        r23NameEq r23KeyEq (LAdvance actor) LFinishTag checked)
      NoTransitions) -> Void
r24EmptyFinishNoIterator actor before afterState checked oldFiber found
  accumulator view lifecycle selected
  (StageFromAdvance storedNameEq storedKeyEq selected tag equation occurs fiber
    stageFound remaining stageAccumulator stageView stageLifecycle step rest
    suffix) = case r24SingletonOccursSelected occurs of
      Refl => case justInjective (trans (sym found) stageFound) of
        Refl => case trans (sym lifecycle) stageLifecycle of
          Refl => noNonemptyReachableFromEmpty suffix

r24FinishTransition :
  (actor : Nat) ->
  (before, afterState : SystemState Nat R23Key R23Value Unit Unit) ->
  checkedApplyAction @{r23NameEq} @{r23KeyEq} (LAdvance actor) before =
    Just (LFinishTag, afterState) -> Transition before afterState
r24FinishTransition actor before afterState checked =
  Fired r23NameEq r23KeyEq (LAdvance actor) LFinishTag checked

0 r24SingletonFinishGeneratorOrigin :
  (actor : Nat) ->
  (sourceBefore, sourceAfter, replayedBefore, replayedAfter :
    SystemState Nat R23Key R23Value Unit Unit) ->
  (sourceChecked : checkedApplyAction @{r23NameEq} @{r23KeyEq}
    (LAdvance actor) sourceBefore = Just (LFinishTag, sourceAfter)) ->
  (replayedChecked : checkedApplyAction @{r23NameEq} @{r23KeyEq}
    (LAdvance actor) replayedBefore = Just (LFinishTag, replayedAfter)) ->
  ((selected : Nat) -> IteratorStage Nat R23Key Unit Unit R23Value selected
    (MoreTransitions
      (r24FinishTransition actor replayedBefore replayedAfter replayedChecked)
      NoTransitions) -> Void) ->
  (selected : Nat) ->
  TraceEffectGenerator Nat R23Key Unit Unit R23Value selected
    (MoreTransitions
      (r24FinishTransition actor replayedBefore replayedAfter replayedChecked)
      NoTransitions) ->
  TraceEffectGenerator Nat R23Key Unit Unit R23Value selected
    (MoreTransitions
      (r24FinishTransition actor sourceBefore sourceAfter sourceChecked)
      NoTransitions)
r24SingletonFinishGeneratorOrigin actor sourceBefore sourceAfter replayedBefore
  replayedAfter sourceChecked replayedChecked noTargetIterator selected
  (ActualForwardGenerator before afterState storedNameEq storedKeyEq action tag
    equation occurs actorMatches) = case r24SingletonOccursSelected occurs of
      Refl => ActualForwardGenerator sourceBefore sourceAfter r23NameEq r23KeyEq
        (LAdvance actor) LFinishTag sourceChecked OccursHere actorMatches
r24SingletonFinishGeneratorOrigin actor sourceBefore sourceAfter replayedBefore
  replayedAfter sourceChecked replayedChecked noTargetIterator selected
  (IteratorForwardGenerator stage) = void (noTargetIterator selected stage)
r24SingletonFinishGeneratorOrigin actor sourceBefore sourceAfter replayedBefore
  replayedAfter sourceChecked replayedChecked noTargetIterator selected
  (IteratorYieldedGenerator stage origin) = void (noTargetIterator selected stage)

0 r24SingletonFinishGeneratorRunsIdentity :
  {before, afterState : SystemState Nat R23Key R23Value Unit Unit} ->
  {actor, selected : Nat} ->
  (finish : Transition before afterState) ->
  (actionExact : transitionAction finish = LAdvance actor) ->
  (tagExact : transitionTag finish = LFinishTag) ->
  ((selected : Nat) -> IteratorStage Nat R23Key Unit Unit R23Value selected
    (MoreTransitions finish NoTransitions) -> Void) ->
  ((state : EffectState Nat R23Key R23Value Unit) ->
    partialEffectMap finish state = Just state) ->
  (generator : TraceEffectGenerator Nat R23Key Unit Unit R23Value selected
    (MoreTransitions finish NoTransitions)) ->
  (state : EffectState Nat R23Key R23Value Unit) ->
  traceGeneratorMap generator state = Just state
r24SingletonFinishGeneratorRunsIdentity
  (Fired storedNameEq storedKeyEq action tag equation) actionExact tagExact
  noIterator mapIdentity
  (ActualForwardGenerator before afterState storedNameEq storedKeyEq action tag
    equation OccursHere actorMatches) state = mapIdentity state
r24SingletonFinishGeneratorRunsIdentity finish actionExact tagExact noIterator
  mapIdentity
  (ActualForwardGenerator before afterState storedNameEq storedKeyEq action tag
    equation (OccursLater later) actorMatches) state =
      void (noOccurrenceInEmpty later)
r24SingletonFinishGeneratorRunsIdentity finish actionExact tagExact noIterator
  mapIdentity (IteratorForwardGenerator stage) state =
    void (noIterator selected stage)
r24SingletonFinishGeneratorRunsIdentity finish actionExact tagExact noIterator
  mapIdentity (IteratorYieldedGenerator stage origin) state =
    void (noIterator selected stage)

0 r24SingletonFinishRAR :
  (actor : Nat) ->
  (sourceBefore, sourceAfter, replayedBefore, replayedAfter :
    SystemState Nat R23Key R23Value Unit Unit) ->
  (sourceChecked : checkedApplyAction @{r23NameEq} @{r23KeyEq}
    (LAdvance actor) sourceBefore = Just (LFinishTag, sourceAfter)) ->
  (replayedChecked : checkedApplyAction @{r23NameEq} @{r23KeyEq}
    (LAdvance actor) replayedBefore = Just (LFinishTag, replayedAfter)) ->
  ((selected : Nat) -> IteratorStage Nat R23Key Unit Unit R23Value selected
    (MoreTransitions
      (r24FinishTransition actor sourceBefore sourceAfter sourceChecked)
      NoTransitions) -> Void) ->
  ((selected : Nat) -> IteratorStage Nat R23Key Unit Unit R23Value selected
    (MoreTransitions
      (r24FinishTransition actor replayedBefore replayedAfter replayedChecked)
      NoTransitions) -> Void) ->
  ((state : EffectState Nat R23Key R23Value Unit) ->
    partialEffectMap
      (r24FinishTransition actor sourceBefore sourceAfter sourceChecked) state =
      Just state) ->
  ((state : EffectState Nat R23Key R23Value Unit) ->
    partialEffectMap
      (r24FinishTransition actor replayedBefore replayedAfter replayedChecked)
      state = Just state) ->
  RelationalReplayCorrespondence Nat R23Key Unit Unit R23Value
    (MoreTransitions
      (r24FinishTransition actor sourceBefore sourceAfter sourceChecked)
      NoTransitions)
    (MoreTransitions
      (r24FinishTransition actor replayedBefore replayedAfter replayedChecked)
      NoTransitions)
r24SingletonFinishRAR actor sourceBefore sourceAfter replayedBefore replayedAfter
  sourceChecked replayedChecked noSourceIterator noTargetIterator
  sourceIdentity targetIdentity =
    MkRelationalReplayCorrespondence
      (r24SingletonFinishGeneratorOrigin actor sourceBefore sourceAfter
        replayedBefore replayedAfter sourceChecked replayedChecked
        noTargetIterator)
      mapPreserved
      (\selected, stage => void (noTargetIterator selected stage))
      (\selected, stage, state => void (noTargetIterator selected stage))
  where
  0 mapPreserved : (selected : Nat) ->
    (generator : TraceEffectGenerator Nat R23Key Unit Unit R23Value selected
      (MoreTransitions
        (r24FinishTransition actor replayedBefore replayedAfter replayedChecked)
        NoTransitions)) ->
    (state : EffectState Nat R23Key R23Value Unit) ->
    traceGeneratorMap
      (r24SingletonFinishGeneratorOrigin actor sourceBefore sourceAfter
        replayedBefore replayedAfter sourceChecked replayedChecked
        noTargetIterator selected generator) state = traceGeneratorMap generator state
  mapPreserved selected
    (ActualForwardGenerator before afterState storedNameEq storedKeyEq action tag
      equation occurs actorMatches) state =
        case r24SingletonOccursSelected occurs of
          Refl => trans
            (r24SingletonFinishGeneratorRunsIdentity
              (r24FinishTransition actor sourceBefore sourceAfter sourceChecked)
              Refl Refl noSourceIterator sourceIdentity
              (r24SingletonFinishGeneratorOrigin actor sourceBefore sourceAfter
                replayedBefore replayedAfter sourceChecked replayedChecked
                noTargetIterator selected
                (ActualForwardGenerator before afterState storedNameEq storedKeyEq
                  action tag equation occurs actorMatches)) state)
            (sym (r24SingletonFinishGeneratorRunsIdentity
              (r24FinishTransition actor replayedBefore replayedAfter
                replayedChecked) Refl Refl noTargetIterator targetIdentity
              (ActualForwardGenerator before afterState storedNameEq storedKeyEq
                action tag equation occurs actorMatches) state))
  mapPreserved selected (IteratorForwardGenerator stage) state =
    void (noTargetIterator selected stage)
  mapPreserved selected (IteratorYieldedGenerator stage origin) state =
    void (noTargetIterator selected stage)

0 r24SingletonPrefixTooLong :
  {first, point, beforeLocated, afterLocated, finalState :
    SystemState Nat R23Key R23Value Unit Unit} ->
  (prefixStep : Transition first point) ->
  (prefixRest : Transitions point beforeLocated) ->
  (located : Transition beforeLocated afterLocated) ->
  (suffix : Transitions afterLocated finalState) ->
  (only : Transition first finalState) ->
  appendTransitions (MoreTransitions prefixStep prefixRest)
    (MoreTransitions located suffix) = MoreTransitions only NoTransitions -> Void
r24SingletonPrefixTooLong prefixStep NoTransitions located suffix only
  decomposition = case cong transitionCount decomposition of Refl impossible
r24SingletonPrefixTooLong prefixStep (MoreTransitions head tail) located suffix
  only decomposition = case cong transitionCount decomposition of Refl impossible

0 r24SingletonActionOrigin :
  {sourceBefore, sourceAfter, replayedBefore, replayedAfter :
    SystemState Nat R23Key R23Value Unit Unit} ->
  {actor : Nat} ->
  {action : Action Nat R23Key R23Value Unit Unit} ->
  (source : Transition sourceBefore sourceAfter) ->
  (replayed : Transition replayedBefore replayedAfter) ->
  (sourceAction : transitionAction source = LAdvance actor) ->
  (replayedAction : transitionAction replayed = LAdvance actor) ->
  LocatedActionOccurrence action (MoreTransitions replayed NoTransitions) ->
  LocatedActionOccurrence action (MoreTransitions source NoTransitions)
r24SingletonActionOrigin source replayed sourceAction replayedAction
  (MkLocatedActionOccurrence _ _ NoTransitions _ NoTransitions same Refl) =
    MkLocatedActionOccurrence _ _ NoTransitions source NoTransitions
      (trans sourceAction (trans (sym replayedAction) same)) Refl
r24SingletonActionOrigin source replayed sourceAction replayedAction
  (MkLocatedActionOccurrence _ _ (MoreTransitions head tail) located suffix same
    decomposition) = void (r24SingletonPrefixTooLong head tail located suffix
      replayed decomposition)

0 r24SingletonTagPreserved :
  {sourceBefore, sourceAfter, replayedBefore, replayedAfter :
    SystemState Nat R23Key R23Value Unit Unit} ->
  {actor : Nat} ->
  {action : Action Nat R23Key R23Value Unit Unit} ->
  (source : Transition sourceBefore sourceAfter) ->
  (replayed : Transition replayedBefore replayedAfter) ->
  (sourceAction : transitionAction source = LAdvance actor) ->
  (replayedAction : transitionAction replayed = LAdvance actor) ->
  transitionTag source = LFinishTag -> transitionTag replayed = LFinishTag ->
  (occurrence : LocatedActionOccurrence action
    (MoreTransitions replayed NoTransitions)) ->
  transitionTag (locatedTransition
    (r24SingletonActionOrigin source replayed sourceAction replayedAction
      occurrence)) = transitionTag (locatedTransition occurrence)
r24SingletonTagPreserved source replayed sourceAction replayedAction sourceTag
  replayedTag (MkLocatedActionOccurrence _ _ NoTransitions _ NoTransitions same
    Refl) = trans sourceTag (sym replayedTag)
r24SingletonTagPreserved source replayed sourceAction replayedAction sourceTag
  replayedTag (MkLocatedActionOccurrence _ _ (MoreTransitions head tail) located
    suffix same decomposition) = void (r24SingletonPrefixTooLong head tail located
      suffix replayed decomposition)

0 r24SingletonOccurrenceAction :
  {replayedBefore, replayedAfter :
    SystemState Nat R23Key R23Value Unit Unit} ->
  {actor : Nat} ->
  {action : Action Nat R23Key R23Value Unit Unit} ->
  (replayed : Transition replayedBefore replayedAfter) ->
  transitionAction replayed = LAdvance actor ->
  LocatedActionOccurrence action (MoreTransitions replayed NoTransitions) ->
  action = LAdvance actor
r24SingletonOccurrenceAction replayed replayedAction
  (MkLocatedActionOccurrence _ _ NoTransitions _ NoTransitions same Refl) =
    trans (sym same) replayedAction
r24SingletonOccurrenceAction replayed replayedAction
  (MkLocatedActionOccurrence _ _ (MoreTransitions head tail) located suffix same
    decomposition) = void (r24SingletonPrefixTooLong head tail located suffix
      replayed decomposition)

0 r24SingletonNoGenerated :
  {replayedBefore, replayedAfter :
    SystemState Nat R23Key R23Value Unit Unit} ->
  {actor, child, parent : Nat} ->
  {component : Component R23Key R23Value Unit Unit} ->
  (replayed : Transition replayedBefore replayedAfter) ->
  transitionAction replayed = LAdvance actor ->
  LocatedGeneratedRegistration child parent component
    (MoreTransitions replayed NoTransitions) -> Void
r24SingletonNoGenerated replayed replayedAction generated =
  case r24SingletonOccurrenceAction replayed replayedAction
    (generatedRegistrationActionOccurrence generated) of Refl impossible

0 r24SingletonOccurrences :
  {sourceBefore, sourceAfter, replayedBefore, replayedAfter :
    SystemState Nat R23Key R23Value Unit Unit} ->
  {actor : Nat} ->
  (source : Transition sourceBefore sourceAfter) ->
  (replayed : Transition replayedBefore replayedAfter) ->
  (sourceAction : transitionAction source = LAdvance actor) ->
  (replayedAction : transitionAction replayed = LAdvance actor) ->
  (sourceTag : transitionTag source = LFinishTag) ->
  (replayedTag : transitionTag replayed = LFinishTag) ->
  ActionRegistrationReplayCorrespondence Nat R23Key Unit Unit R23Value
    (MoreTransitions source NoTransitions)
    (MoreTransitions replayed NoTransitions)
r24SingletonOccurrences source replayed sourceAction replayedAction sourceTag
  replayedTag = MkActionRegistrationReplayCorrespondence
    identityRegistrationGenerationBijection
    (r24SingletonActionOrigin source replayed sourceAction replayedAction)
    (r24SingletonTagPreserved source replayed sourceAction replayedAction
      sourceTag replayedTag)
    (\generated => void (r24SingletonNoGenerated replayed replayedAction generated))
    (\generated => void (r24SingletonNoGenerated replayed replayedAction generated))
    (\generated => void (r24SingletonNoGenerated replayed replayedAction generated))

public export
record R24CheckedEmptyFinishReplay
  (actor : Nat)
  (sourceBefore, sourceAfter, replayedBefore :
    SystemState Nat R23Key R23Value Unit Unit)
  (sourceChecked : checkedApplyAction @{r23NameEq} @{r23KeyEq}
    (LAdvance actor) sourceBefore = Just (LFinishTag, sourceAfter)) where
  constructor MkR24CheckedEmptyFinishReplay
  replayedAfter : SystemState Nat R23Key R23Value Unit Unit
  0 replayedChecked : checkedApplyAction @{r23NameEq} @{r23KeyEq}
    (LAdvance actor) replayedBefore = Just (LFinishTag, replayedAfter)
  replayedTransition : Transition replayedBefore replayedAfter
  0 replayedTransitionExact : replayedTransition =
    r24FinishTransition actor replayedBefore replayedAfter replayedChecked
  0 replayedActionExact : transitionAction replayedTransition = LAdvance actor
  0 replayedTagExact : transitionTag replayedTransition = LFinishTag
  0 replayedSingletonAligned : AlignedTransitions Nat R23Key Unit Unit R23Value
    r23NameEq r23KeyEq (MoreTransitions replayedTransition NoTransitions)
  0 replayedEndpoint : RelationalReplayEndpoint Nat R23Key Unit Unit R23Value
    r23NameEq r23KeyEq sourceAfter replayedAfter
  0 perStepRAR : RelationalReplayCorrespondence Nat R23Key Unit Unit R23Value
    (MoreTransitions
      (r24FinishTransition actor sourceBefore sourceAfter sourceChecked)
      NoTransitions)
    (MoreTransitions replayedTransition NoTransitions)
  0 perStepOccurrence : ActionRegistrationReplayCorrespondence Nat R23Key Unit
    Unit R23Value
    (MoreTransitions
      (r24FinishTransition actor sourceBefore sourceAfter sourceChecked)
      NoTransitions)
    (MoreTransitions replayedTransition NoTransitions)
  0 perStepRelativeOrdinal :
    {action : Action Nat R23Key R23Value Unit Unit} ->
    (occurrence : LocatedActionOccurrence action
      (MoreTransitions replayedTransition NoTransitions)) ->
    locatedActionOrdinal occurrence = locatedActionOrdinal
      (replayActionOrigin perStepOccurrence occurrence)

||| Test-local candidate for frozen interface item E.  The existing replay is
||| retained definitionally while the exact target map theorem remains indexed
||| by that replay's owned checked transition.
public export
record R27MapRetainedFinishReplay
  (actor : Nat)
  (sourceBefore, sourceAfter, replayedBefore :
    SystemState Nat R23Key R23Value Unit Unit)
  (sourceChecked : checkedApplyAction @{r23NameEq} @{r23KeyEq}
    (LAdvance actor) sourceBefore = Just (LFinishTag, sourceAfter)) where
  constructor MkR27MapRetainedFinishReplay
  baseFinishReplay : R24CheckedEmptyFinishReplay actor sourceBefore sourceAfter
    replayedBefore sourceChecked
  0 retainedTargetMapIdentity :
    (state : EffectState Nat R23Key R23Value Unit) ->
    partialEffectMap (replayedTransition baseFinishReplay) state = Just state

0 r27ProduceMapRetainedFinish :
  (actor : Nat) ->
  (sourceBefore, sourceAfter, replayedBefore :
    SystemState Nat R23Key R23Value Unit Unit) ->
  (sourceChecked : checkedApplyAction @{r23NameEq} @{r23KeyEq}
    (LAdvance actor) sourceBefore = Just (LFinishTag, sourceAfter)) ->
  registryWellFormed @{r23NameEq} @{r23KeyEq} sourceBefore = True ->
  lookupFiber @{r23NameEq} actor (registry sourceBefore) = Just r23Begun ->
  RelationalReplayEndpoint Nat R23Key Unit Unit R23Value r23NameEq r23KeyEq
    sourceBefore replayedBefore ->
  R27MapRetainedFinishReplay actor sourceBefore sourceAfter replayedBefore
    sourceChecked
r27ProduceMapRetainedFinish actor
  (MkSystemState sourceWorld sourceRegistry) sourceAfter
  (MkSystemState replayedWorld replayedRegistry) sourceChecked sourceWellFormed
  sourceFound beforeEndpoint =
    case controlEquivalentTargetHasSource r23NameEq
      (MkSystemState replayedWorld replayedRegistry)
      (MkSystemState sourceWorld sourceRegistry)
      (controlEquivalentSymmetric (replayedControls beforeEndpoint)) actor
      r23Begun sourceFound of
      MkControlledSourceForTarget replayedFiber replayedFound targetToSource =>
        case r24DeriveTargetFinish actor
          (MkSystemState replayedWorld replayedRegistry) replayedFiber
          replayedFound targetToSource of
          MkR24DerivedTargetFinish rightNext targetAfter targetStateExact
            targetRaw targetAccumulator targetView targetLifecycle
            nextLifecycle =>
              let 0 targetWellFormed : (registryWellFormed
                    @{r23NameEq} @{r23KeyEq} targetAfter = True)
                  targetWellFormed = preservationTheoremProof r23NameEq
                    r23KeyEq (LAdvance actor)
                    (MkSystemState replayedWorld replayedRegistry) targetAfter
                    LFinishTag (replayedWellFormed beforeEndpoint) targetRaw
                  0 targetChecked : checkedApplyAction @{r23NameEq} @{r23KeyEq}
                    (LAdvance actor)
                    (MkSystemState replayedWorld replayedRegistry) =
                      Just (LFinishTag, targetAfter)
                  targetChecked = rewrite targetRaw in
                    rewrite targetWellFormed in Refl
                  0 nextControlsConcrete : ControlEquivalent Nat R23Key Unit Unit
                    R23Value r23NameEq
                    (MkSystemState sourceWorld
                      (replaceBinding @{r23NameEq} actor r23Active
                        sourceRegistry)) targetAfter
                  nextControlsConcrete = replace
                    {p = \observed => ControlEquivalent Nat R23Key Unit Unit
                      R23Value r23NameEq
                      (MkSystemState sourceWorld
                        (replaceBinding @{r23NameEq} actor r23Active
                          sourceRegistry)) observed}
                    (sym targetStateExact)
                    (controlEquivalentAfterRelatedReplacement r23NameEq actor
                      sourceWorld replayedWorld sourceRegistry replayedRegistry
                      r23Begun replayedFiber r23Active rightNext sourceFound
                      replayedFound nextLifecycle
                      (replayedControls beforeEndpoint))
                  0 sourceRaw : applyAction @{r23NameEq} @{r23KeyEq}
                    (LAdvance actor) (MkSystemState sourceWorld sourceRegistry) =
                      Just (LFinishTag, sourceAfter)
                  sourceRaw = checkedActionProjects r23NameEq r23KeyEq
                    (LAdvance actor) (MkSystemState sourceWorld sourceRegistry)
                    sourceAfter LFinishTag sourceChecked
                  0 sourceConcrete : applyAction @{r23NameEq} @{r23KeyEq}
                    (LAdvance actor) (MkSystemState sourceWorld sourceRegistry) =
                      Just (LFinishTag,
                        the (SystemState Nat R23Key R23Value Unit Unit)
                          (MkSystemState sourceWorld
                            (r24ReplaceActive actor sourceRegistry)))
                  sourceConcrete = rewrite sourceFound in Refl
                  0 sourceAfterExact : MkSystemState sourceWorld
                    (replaceBinding @{r23NameEq} actor r23Active sourceRegistry) =
                      sourceAfter
                  sourceAfterExact = cong snd
                    (justInjective (trans (sym sourceConcrete) sourceRaw))
                  0 nextControls : ControlEquivalent Nat R23Key Unit Unit
                    R23Value r23NameEq sourceAfter targetAfter
                  nextControls = replace
                    {p = \observed => ControlEquivalent Nat R23Key Unit Unit
                      R23Value r23NameEq observed targetAfter}
                    sourceAfterExact nextControlsConcrete
                  0 nextEffects : EffectStateRelated r23KeyEq
                    (projectEffectState @{r23NameEq} sourceAfter)
                    (projectEffectState @{r23NameEq} targetAfter)
                  nextEffects = r23AllEffectStatesRelated _ _
                  targetTransition : Transition
                    (MkSystemState replayedWorld replayedRegistry) targetAfter
                  targetTransition = r24FinishTransition actor
                    (MkSystemState replayedWorld replayedRegistry) targetAfter
                    targetChecked
                  sourceTransition : Transition
                    (MkSystemState sourceWorld sourceRegistry) sourceAfter
                  sourceTransition = r24FinishTransition actor
                    (MkSystemState sourceWorld sourceRegistry) sourceAfter
                    sourceChecked
                  0 sourceNoIterator : (selected : Nat) -> IteratorStage Nat
                    R23Key Unit Unit R23Value selected
                    (MoreTransitions sourceTransition NoTransitions) -> Void
                  sourceNoIterator = r24EmptyFinishNoIterator actor
                    (MkSystemState sourceWorld sourceRegistry) sourceAfter
                    sourceChecked r23Begun sourceFound id EmptyView Refl
                  0 targetNoIterator : (selected : Nat) -> IteratorStage Nat
                    R23Key Unit Unit R23Value selected
                    (MoreTransitions targetTransition NoTransitions) -> Void
                  targetNoIterator = r24EmptyFinishNoIterator actor
                    (MkSystemState replayedWorld replayedRegistry) targetAfter
                    targetChecked replayedFiber replayedFound targetAccumulator
                    targetView targetLifecycle
                  0 sourceMapIdentity :
                    (state : EffectState Nat R23Key R23Value Unit) ->
                    partialEffectMap sourceTransition state = Just state
                  sourceMapIdentity state = rewrite sourceFound in Refl
                  0 targetMapIdentity :
                    (state : EffectState Nat R23Key R23Value Unit) ->
                    partialEffectMap targetTransition state = Just state
                  targetMapIdentity state = rewrite replayedFound in
                    rewrite targetLifecycle in Refl
                  0 rar : RelationalReplayCorrespondence Nat R23Key Unit Unit
                    R23Value (MoreTransitions sourceTransition NoTransitions)
                    (MoreTransitions targetTransition NoTransitions)
                  rar = r24SingletonFinishRAR actor
                    (MkSystemState sourceWorld sourceRegistry) sourceAfter
                    (MkSystemState replayedWorld replayedRegistry) targetAfter
                    sourceChecked targetChecked sourceNoIterator targetNoIterator
                    sourceMapIdentity targetMapIdentity
                  0 occurrence : ActionRegistrationReplayCorrespondence Nat
                    R23Key Unit Unit R23Value
                    (MoreTransitions sourceTransition NoTransitions)
                    (MoreTransitions targetTransition NoTransitions)
                  occurrence = r24SingletonOccurrences sourceTransition
                    targetTransition Refl Refl Refl Refl
                  0 ordinal :
                    {action : Action Nat R23Key R23Value Unit Unit} ->
                    (located : LocatedActionOccurrence action
                      (MoreTransitions targetTransition NoTransitions)) ->
                    locatedActionOrdinal located = locatedActionOrdinal
                      (replayActionOrigin occurrence located)
                  ordinal
                    (MkLocatedActionOccurrence _ _ NoTransitions _ NoTransitions
                      same Refl) = Refl
                  ordinal
                    (MkLocatedActionOccurrence _ _ (MoreTransitions head tail)
                      located suffix same decomposition) =
                        void (r24SingletonPrefixTooLong head tail located suffix
                          targetTransition decomposition)
              in MkR27MapRetainedFinishReplay
                (MkR24CheckedEmptyFinishReplay targetAfter targetChecked
                  targetTransition Refl Refl Refl
                  (AlignedStep (LAdvance actor) LFinishTag targetChecked
                    NoTransitions AlignedEnd)
                  (MkRelationalReplayEndpoint nextEffects nextControls
                    targetWellFormed) rar occurrence ordinal)
                targetMapIdentity

||| The revision-24 projection is intentionally definition-only.  Existing
||| clients therefore keep their exact terms while revision 27 retains the
||| additional producer proof.
0 r24ProduceEmptyFinish :
  (actor : Nat) ->
  (sourceBefore, sourceAfter, replayedBefore :
    SystemState Nat R23Key R23Value Unit Unit) ->
  (sourceChecked : checkedApplyAction @{r23NameEq} @{r23KeyEq}
    (LAdvance actor) sourceBefore = Just (LFinishTag, sourceAfter)) ->
  registryWellFormed @{r23NameEq} @{r23KeyEq} sourceBefore = True ->
  lookupFiber @{r23NameEq} actor (registry sourceBefore) = Just r23Begun ->
  RelationalReplayEndpoint Nat R23Key Unit Unit R23Value r23NameEq r23KeyEq
    sourceBefore replayedBefore ->
  R24CheckedEmptyFinishReplay actor sourceBefore sourceAfter replayedBefore
    sourceChecked
r24ProduceEmptyFinish actor sourceBefore sourceAfter replayedBefore sourceChecked
  sourceWellFormed sourceFound beforeEndpoint = baseFinishReplay
    (r27ProduceMapRetainedFinish actor sourceBefore sourceAfter replayedBefore
      sourceChecked sourceWellFormed sourceFound beforeEndpoint)

0 r24PairEndpoint : RelationalReplayEndpoint Nat R23Key Unit Unit R23Value
  r23NameEq r23KeyEq r23AfterPair (swappedFinal r23Diamond)
r24PairEndpoint = MkRelationalReplayEndpoint (swappedEffects r23Diamond)
  (swappedControlEquivalent r23Diamond) (swappedWellFormed r23Diamond)

public export
0 r24FirstFinishReplay : R24CheckedEmptyFinishReplay 1 r23AfterPair
  r23AfterAdvance1 (swappedFinal r23Diamond) r23Advance1Checked
r24FirstFinishReplay = r24ProduceEmptyFinish 1 r23AfterPair r23AfterAdvance1
  (swappedFinal r23Diamond) r23Advance1Checked r23AfterPairWellFormed Refl
  r24PairEndpoint

public export
0 r24SecondFinishReplay : R24CheckedEmptyFinishReplay 2 r23AfterAdvance1
  r23Final (replayedAfter r24FirstFinishReplay) r23Advance2Checked
r24SecondFinishReplay = r24ProduceEmptyFinish 2 r23AfterAdvance1 r23Final
  (replayedAfter r24FirstFinishReplay) r23Advance2Checked
  r23AfterAdvance1WellFormed Refl (replayedEndpoint r24FirstFinishReplay)

public export
0 r27FirstFinishEnvelope : R27MapRetainedFinishReplay 1 r23AfterPair
  r23AfterAdvance1 (swappedFinal r23Diamond) r23Advance1Checked
r27FirstFinishEnvelope = r27ProduceMapRetainedFinish 1 r23AfterPair
  r23AfterAdvance1 (swappedFinal r23Diamond) r23Advance1Checked
  r23AfterPairWellFormed Refl r24PairEndpoint

public export
0 r27FirstBaseIsR24 : baseFinishReplay r27FirstFinishEnvelope =
  r24FirstFinishReplay
r27FirstBaseIsR24 = Refl

public export
0 r27SecondFinishEnvelope : R27MapRetainedFinishReplay 2 r23AfterAdvance1
  r23Final (replayedAfter (baseFinishReplay r27FirstFinishEnvelope))
  r23Advance2Checked
r27SecondFinishEnvelope = r27ProduceMapRetainedFinish 2 r23AfterAdvance1 r23Final
  (replayedAfter (baseFinishReplay r27FirstFinishEnvelope)) r23Advance2Checked
  r23AfterAdvance1WellFormed Refl
  (replayedEndpoint (baseFinishReplay r27FirstFinishEnvelope))

public export
0 r27SecondBaseIsR24 : baseFinishReplay r27SecondFinishEnvelope =
  r24SecondFinishReplay
r27SecondBaseIsR24 = Refl

public export
0 r27FinalEndpoint : RelationalReplayEndpoint Nat R23Key Unit Unit R23Value
  r23NameEq r23KeyEq r23Final
  (replayedAfter (baseFinishReplay r27SecondFinishEnvelope))
r27FinalEndpoint = replayedEndpoint (baseFinishReplay r27SecondFinishEnvelope)

public export
0 r24ReplayedSuffix : Transitions (swappedFinal r23Diamond)
  (replayedAfter r24SecondFinishReplay)
r24ReplayedSuffix = MoreTransitions
  (replayedTransition r24FirstFinishReplay)
  (MoreTransitions (replayedTransition r24SecondFinishReplay) NoTransitions)

record R24CheckedTwoHeadSuffix where
  constructor MkR24CheckedTwoHeadSuffix
  0 firstHead : R24CheckedEmptyFinishReplay 1 r23AfterPair r23AfterAdvance1
    (swappedFinal r23Diamond) r23Advance1Checked
  0 secondHead : R24CheckedEmptyFinishReplay 2 r23AfterAdvance1 r23Final
    (replayedAfter firstHead) r23Advance2Checked
  0 exactSourceSuffix : Transitions r23AfterPair r23Final
  0 exactTargetSuffix : Transitions (swappedFinal r23Diamond)
    (replayedAfter secondHead)
  0 sourceSuffixExact : exactSourceSuffix = r23Suffix
  0 targetSuffixExact : exactTargetSuffix = MoreTransitions
    (replayedTransition firstHead)
    (MoreTransitions (replayedTransition secondHead) NoTransitions)

0 r24SealedSuffix : R24CheckedTwoHeadSuffix
r24SealedSuffix = MkR24CheckedTwoHeadSuffix r24FirstFinishReplay
  r24SecondFinishReplay r23Suffix r24ReplayedSuffix Refl Refl

public export
0 r24WholeTargetTrace : Transitions r23Initial
  (replayedAfter r24SecondFinishReplay)
r24WholeTargetTrace = MoreTransitions r23Insert1
  (MoreTransitions r23Insert2
    (MoreTransitions (movedRight r23Diamond)
      (MoreTransitions (movedLeft r23Diamond) r24ReplayedSuffix)))

0 r24PrefixAligned : AlignedTransitions Nat R23Key Unit Unit R23Value
  r23NameEq r23KeyEq r23PairPrefix
r24PrefixAligned = AlignedStep (OInsert 1 Root r23Component) OInsertTag
  r23Insert1Checked _ (AlignedStep (OInsert 2 Root r23Component) OInsertTag
    r23Insert2Checked NoTransitions AlignedEnd)

0 prependAlignedSingleton :
  {first, middle, finalState : SystemState Nat R23Key R23Value Unit Unit} ->
  {step : Transition first middle} ->
  {tail : Transitions middle finalState} ->
  AlignedTransitions Nat R23Key Unit Unit R23Value r23NameEq r23KeyEq
    (MoreTransitions step NoTransitions) ->
  AlignedTransitions Nat R23Key Unit Unit R23Value r23NameEq r23KeyEq tail ->
  AlignedTransitions Nat R23Key Unit Unit R23Value r23NameEq r23KeyEq
    (MoreTransitions step tail)
prependAlignedSingleton
  (AlignedStep action tag checked NoTransitions AlignedEnd) tailAligned =
    AlignedStep action tag checked tail tailAligned

0 r24SuffixAligned : AlignedTransitions Nat R23Key Unit Unit R23Value
  r23NameEq r23KeyEq r24ReplayedSuffix
r24SuffixAligned = prependAlignedSingleton
  (replayedSingletonAligned r24FirstFinishReplay)
  (replayedSingletonAligned r24SecondFinishReplay)

public export
0 r24FinalEndpoint : RelationalReplayEndpoint Nat R23Key Unit Unit R23Value
  r23NameEq r23KeyEq r23Final (replayedAfter r24SecondFinishReplay)
r24FinalEndpoint = replayedEndpoint r24SecondFinishReplay

||| Definition-only transfer checks for the corrected envelope.  These RHSs
||| contain no rewrite, transport lemma, or reconstructed replay proof.
||| Public test-local normalization of the authenticated replay transition.  It
||| exposes no new caller premise: it is exactly the producer-owned transition
||| equality with the transparent canonical constructor made explicit.
public export
0 r25CanonicalTransitionExact :
  {actor : Nat} ->
  {sourceBefore, sourceAfter, replayedBefore :
    SystemState Nat R23Key R23Value Unit Unit} ->
  {sourceChecked : checkedApplyAction @{r23NameEq} @{r23KeyEq}
    (LAdvance actor) sourceBefore = Just (LFinishTag, sourceAfter)} ->
  (replay : R24CheckedEmptyFinishReplay actor sourceBefore sourceAfter
    replayedBefore sourceChecked) ->
  replayedTransition replay =
    Fired r23NameEq r23KeyEq (LAdvance actor) LFinishTag
      (replayedChecked replay)
r25CanonicalTransitionExact replay = replayedTransitionExact replay

public export
0 r25FirstFinishReplay : R24CheckedEmptyFinishReplay 1 r23AfterPair
  r23AfterAdvance1 (swappedFinal (baseDiamond r25AlignedDiamond))
  r23Advance1Checked
r25FirstFinishReplay = r24FirstFinishReplay

public export
0 r25SecondFinishReplay : R24CheckedEmptyFinishReplay 2 r23AfterAdvance1 r23Final
  (replayedAfter r25FirstFinishReplay) r23Advance2Checked
r25SecondFinishReplay = r24SecondFinishReplay

public export
0 r25FinalEndpoint : RelationalReplayEndpoint Nat R23Key Unit Unit R23Value
  r23NameEq r23KeyEq r23Final (replayedAfter r25SecondFinishReplay)
r25FinalEndpoint = r24FinalEndpoint

public export
0 r25WholeTargetTrace : Transitions r23Initial
  (replayedAfter r25SecondFinishReplay)
r25WholeTargetTrace = MoreTransitions r23Insert1
  (MoreTransitions r23Insert2
    (MoreTransitions (movedRight (baseDiamond r25AlignedDiamond))
      (MoreTransitions (movedLeft (baseDiamond r25AlignedDiamond))
        (MoreTransitions (replayedTransition r25FirstFinishReplay)
          (MoreTransitions (replayedTransition r25SecondFinishReplay)
            NoTransitions)))))

0 r25AppendAligned :
  {first, middle, finalState : SystemState Nat R23Key R23Value Unit Unit} ->
  {left : Transitions first middle} ->
  {right : Transitions middle finalState} ->
  AlignedTransitions Nat R23Key Unit Unit R23Value r23NameEq r23KeyEq left ->
  AlignedTransitions Nat R23Key Unit Unit R23Value r23NameEq r23KeyEq right ->
  AlignedTransitions Nat R23Key Unit Unit R23Value r23NameEq r23KeyEq
    (appendTransitions left right)
r25AppendAligned AlignedEnd rightAligned = rightAligned
r25AppendAligned (AlignedStep action tag checked rest restAligned) rightAligned =
  AlignedStep action tag checked (appendTransitions rest right)
    (r25AppendAligned restAligned rightAligned)

0 r25WholeAligned : AlignedTransitions Nat R23Key Unit Unit R23Value r23NameEq
  r23KeyEq r25WholeTargetTrace
r25WholeAligned = r25AppendAligned r24PrefixAligned
  (r25AppendAligned (movedPairAligned r25AlignedDiamond) r24SuffixAligned)

0 r25FinishStepDiscipline :
  {actor : Nat} ->
  {sourceBefore, sourceAfter, replayedBefore :
    SystemState Nat R23Key R23Value Unit Unit} ->
  {finalState : SystemState Nat R23Key R23Value Unit Unit} ->
  {sourceChecked : checkedApplyAction @{r23NameEq} @{r23KeyEq}
    (LAdvance actor) sourceBefore = Just (LFinishTag, sourceAfter)} ->
  (replay : R24CheckedEmptyFinishReplay actor sourceBefore sourceAfter
    replayedBefore sourceChecked) ->
  (rest : Transitions (replayedAfter replay) finalState) ->
  RegistrationStepDiscipline r23Protocol r23NameEq
    (transitionAction (replayedTransition replay)) replayedBefore rest
r25FinishStepDiscipline replay rest = rewrite replayedActionExact replay in ()

0 r25WholeDiscipline : RegistrationDiscipline r23Protocol r23NameEq
  r25WholeTargetTrace
r25WholeDiscipline = RegistrationDisciplineStep r23Insert1 _ (Z ** Refl)
  (RegistrationDisciplineStep r23Insert2 _ (Z ** Refl)
    (RegistrationDisciplineStep
      (movedRight (baseDiamond r25AlignedDiamond)) _ ()
      (RegistrationDisciplineStep
        (movedLeft (baseDiamond r25AlignedDiamond)) _ ()
        (RegistrationDisciplineStep
          (replayedTransition r25FirstFinishReplay) _
          (r25FinishStepDiscipline r25FirstFinishReplay _)
          (RegistrationDisciplineStep
            (replayedTransition r25SecondFinishReplay) NoTransitions
            (r25FinishStepDiscipline r25SecondFinishReplay NoTransitions)
            RegistrationDisciplineEnd)))))

0 r25InitialWellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23Initial = True
r25InitialWellFormed = r23InitialWellFormed

0 r25InitialEmpty : bindings (registry r23Initial) = []
r25InitialEmpty = r23InitialEmpty

0 r25FinalWellFormed : registryWellFormed @{r23NameEq} @{r23KeyEq}
  (replayedAfter r25SecondFinishReplay) = True
r25FinalWellFormed = replayedWellFormed r25FinalEndpoint

0 r25BindingKeyElem :
  (entry : Binding Nat (FiberAt Nat R23Key R23Value Unit Unit)) ->
  (entries : List (Binding Nat (FiberAt Nat R23Key R23Value Unit Unit))) ->
  Elem entry entries -> Elem (bindingKey entry) (bindingKeys entries)
r25BindingKeyElem entry (entry :: rest) Here = Here
r25BindingKeyElem entry (other :: rest) (There later) =
  There (r25BindingKeyElem entry rest later)

0 r25LookupEntry :
  (entries : List (Binding Nat (FiberAt Nat R23Key R23Value Unit Unit))) ->
  UniqueKeys (bindingKeys entries) ->
  (selected : Nat) -> (fiber : Fiber Nat R23Key R23Value Unit Unit) ->
  Elem (Bind selected fiber) entries ->
  lookupEntries @{r23NameEq} selected entries = Just fiber
r25LookupEntry [] UniqueNil selected fiber present impossible
r25LookupEntry (Bind current observed :: rest)
  (UniqueCons headFresh tailUnique) selected fiber present
  with (decEq @{r23NameEq} selected current)
  r25LookupEntry (Bind selected observed :: rest)
    (UniqueCons headFresh tailUnique) selected fiber present | Yes Refl =
      case present of
        Here => Refl
        There later => void (headFresh
          (r25BindingKeyElem (Bind selected fiber) rest later))
  r25LookupEntry (Bind current observed :: rest)
    (UniqueCons headFresh tailUnique) selected fiber present | No distinct =
      case present of
        Here => void (distinct Refl)
        There later => r25LookupEntry rest tailUnique selected fiber later

0 r25SourceFoundIsActive :
  (selected : Nat) -> (fiber : Fiber Nat R23Key R23Value Unit Unit) ->
  lookupFiber @{r23NameEq} selected (registry r23Final) = Just fiber ->
  fiber = r23Active
r25SourceFoundIsActive selected fiber found
  with (decEq @{r23NameEq} selected 2)
  r25SourceFoundIsActive 2 fiber found | Yes Refl = case found of Refl => Refl
  r25SourceFoundIsActive selected fiber found | No notTwo
    with (decEq @{r23NameEq} selected 1)
    r25SourceFoundIsActive 1 fiber found | No notTwo | Yes Refl =
      case found of Refl => Refl
    r25SourceFoundIsActive selected fiber found | No notTwo | No notOne =
      case found of Refl impossible

0 r25ActiveControlQuiet :
  (targetFiber : Fiber Nat R23Key R23Value Unit Unit) ->
  FiberControlRelated r23Active targetFiber ->
  (targetRegistry : Registry Nat R23Key R23Value Unit Unit) ->
  quietFiber @{r23NameEq} @{r23KeyEq} targetFiber targetRegistry = True
r25ActiveControlQuiet targetFiber related targetRegistry = case related of
  FibersControlRelated _ targetParent _ targetRetired _ targetTable _
    targetLifecycle _ retiredSame lifecycleRelated =>
      case retiredSame of
        Refl => case lifecycleRelated of
          ActiveControls accumulatorRelated viewSame => case viewSame of
            Refl => Refl

0 r25AllTargetEntriesQuiet :
  (targetWorld : Unit) ->
  (targetEntries : List
    (Binding Nat (FiberAt Nat R23Key R23Value Unit Unit))) ->
  (targetUnique : UniqueKeys (bindingKeys targetEntries)) ->
  ControlEquivalent Nat R23Key Unit Unit R23Value r23NameEq r23Final
    (MkSystemState targetWorld (MkCoeffectContext targetEntries targetUnique)) ->
  (remaining : List
    (Binding Nat (FiberAt Nat R23Key R23Value Unit Unit))) ->
  ((entry : Binding Nat (FiberAt Nat R23Key R23Value Unit Unit)) ->
    Elem entry remaining -> Elem entry targetEntries) ->
  allRecursive
    (quietEntryFor {name = Nat} {key = R23Key} {value = R23Value}
      {world = Unit} {error = Unit}
      (MkCoeffectContext targetEntries targetUnique)) remaining = True
r25AllTargetEntriesQuiet targetWorld targetEntries targetUnique controls []
  member = Refl
r25AllTargetEntriesQuiet targetWorld targetEntries targetUnique controls
  (Bind selected targetFiber :: rest) member =
    let 0 targetFound : lookupFiber @{r23NameEq} selected
          (MkCoeffectContext targetEntries targetUnique) === Just targetFiber
        targetFound = r25LookupEntry targetEntries targetUnique selected targetFiber
          (member (Bind selected targetFiber) Here)
    in case controlEquivalentTargetHasSource r23NameEq r23Final
      (MkSystemState targetWorld (MkCoeffectContext targetEntries targetUnique))
      controls selected targetFiber targetFound of
      MkControlledSourceForTarget sourceFiber sourceFound targetControl =>
        let 0 sourceExact : sourceFiber === r23Active
            sourceExact = r25SourceFoundIsActive selected sourceFiber sourceFound
            0 activeControl : FiberControlRelated r23Active targetFiber
            activeControl = replace
              {p = \observed => FiberControlRelated observed targetFiber}
              sourceExact targetControl
            0 headQuiet : quietFiber @{r23NameEq} @{r23KeyEq} targetFiber
              (MkCoeffectContext targetEntries targetUnique) = True
            headQuiet = r25ActiveControlQuiet targetFiber activeControl
              (MkCoeffectContext targetEntries targetUnique)
            0 restQuiet : allRecursive
              (quietEntryFor {name = Nat} {key = R23Key} {value = R23Value}
                {world = Unit} {error = Unit}
                (MkCoeffectContext targetEntries targetUnique)) rest = True
            restQuiet = r25AllTargetEntriesQuiet targetWorld targetEntries
              targetUnique controls rest (\entry, later => member entry (There later))
        in rewrite headQuiet in rewrite restQuiet in Refl

0 r25TargetQuiet : quiet @{r23NameEq} @{r23KeyEq}
  (replayedAfter r25SecondFinishReplay) = True
r25TargetQuiet with (replayedAfter r25SecondFinishReplay) proof targetExact
  r25TargetQuiet | MkSystemState targetWorld
    (MkCoeffectContext targetEntries targetUnique) =
      let 0 controls : ControlEquivalent Nat R23Key Unit Unit R23Value
            r23NameEq r23Final
            (MkSystemState targetWorld
              (MkCoeffectContext targetEntries targetUnique))
          controls = replace
            {p = \target => ControlEquivalent Nat R23Key Unit Unit R23Value
              r23NameEq r23Final target}
            targetExact (replayedControls r25FinalEndpoint)
      in r25AllTargetEntriesQuiet targetWorld targetEntries targetUnique controls
           targetEntries (\entry, present => present)

0 r25AllTargetEntriesNoFailure :
  (targetWorld : Unit) ->
  (targetEntries : List
    (Binding Nat (FiberAt Nat R23Key R23Value Unit Unit))) ->
  (targetUnique : UniqueKeys (bindingKeys targetEntries)) ->
  ControlEquivalent Nat R23Key Unit Unit R23Value r23NameEq r23Final
    (MkSystemState targetWorld (MkCoeffectContext targetEntries targetUnique)) ->
  (remaining : List
    (Binding Nat (FiberAt Nat R23Key R23Value Unit Unit))) ->
  ((entry : Binding Nat (FiberAt Nat R23Key R23Value Unit Unit)) ->
    Elem entry remaining -> Elem entry targetEntries) ->
  allList (notFailedEntry {name = Nat} {key = R23Key} {value = R23Value}
    {world = Unit} {error = Unit}) remaining = True
r25AllTargetEntriesNoFailure targetWorld targetEntries targetUnique controls []
  member = Refl
r25AllTargetEntriesNoFailure targetWorld targetEntries targetUnique controls
  (Bind selected targetFiber :: rest) member =
    let 0 targetFound : lookupFiber @{r23NameEq} selected
          (MkCoeffectContext targetEntries targetUnique) === Just targetFiber
        targetFound = r25LookupEntry targetEntries targetUnique selected targetFiber
          (member (Bind selected targetFiber) Here)
        0 headSafe : fiberNotFailed targetFiber = True
        headSafe = targetEntryNotFailedFromSource r23NameEq r23Final
          (MkSystemState targetWorld
            (MkCoeffectContext targetEntries targetUnique)) controls
          r23FinalNoFailure selected targetFiber targetFound
        0 restSafe : allList
          (notFailedEntry {name = Nat} {key = R23Key} {value = R23Value}
            {world = Unit} {error = Unit}) rest = True
        restSafe = r25AllTargetEntriesNoFailure targetWorld targetEntries
          targetUnique controls rest (\entry, later => member entry (There later))
    in rewrite headSafe in rewrite restSafe in Refl

0 r25TargetNoFailure : noFailedFibers
  (replayedAfter r25SecondFinishReplay) = True
r25TargetNoFailure with (replayedAfter r25SecondFinishReplay) proof targetExact
  r25TargetNoFailure | MkSystemState targetWorld
    (MkCoeffectContext targetEntries targetUnique) =
      let 0 controls : ControlEquivalent Nat R23Key Unit Unit R23Value
            r23NameEq r23Final
            (MkSystemState targetWorld
              (MkCoeffectContext targetEntries targetUnique))
          controls = replace
            {p = \target => ControlEquivalent Nat R23Key Unit Unit R23Value
              r23NameEq r23Final target}
            targetExact (replayedControls r25FinalEndpoint)
      in r25AllTargetEntriesNoFailure targetWorld targetEntries targetUnique
           controls targetEntries (\entry, present => present)

0 r25TraceTotal :
  {first, finalState : SystemState Nat R23Key R23Value Unit Unit} ->
  (trace : Transitions first finalState) ->
  TraceComponentsTotal r23NameEq r23KeyEq trace
r25TraceTotal NoTransitions = TraceComponentsTotalEnd
r25TraceTotal (MoreTransitions transition rest) =
  TraceComponentsTotalStep transition rest (r23AnyTransitionTotal transition)
    (r25TraceTotal rest)

0 r25WholeTotal : TraceComponentsTotal r23NameEq r23KeyEq r25WholeTargetTrace
r25WholeTotal = r25TraceTotal r25WholeTargetTrace

||| Revision 27 projection audit. Every closed field is a direct alias; no
||| transport, rewrite, or reconstructed proof is permitted in this block.
public export
0 r27FinalEndpointIsR25 : r27FinalEndpoint = r25FinalEndpoint
r27FinalEndpointIsR25 = Refl

public export
0 r27WholeTargetTrace : Transitions r23Initial
  (replayedAfter (baseFinishReplay r27SecondFinishEnvelope))
r27WholeTargetTrace = r25WholeTargetTrace

0 r27WholeAligned : AlignedTransitions Nat R23Key Unit Unit R23Value r23NameEq
  r23KeyEq r27WholeTargetTrace
r27WholeAligned = r25WholeAligned

0 r27WholeDiscipline : RegistrationDiscipline r23Protocol r23NameEq
  r27WholeTargetTrace
r27WholeDiscipline = r25WholeDiscipline

0 r27InitialWellFormed :
  registryWellFormed @{r23NameEq} @{r23KeyEq} r23Initial = True
r27InitialWellFormed = r25InitialWellFormed

0 r27InitialEmpty : bindings (registry r23Initial) = []
r27InitialEmpty = r25InitialEmpty

0 r27FinalWellFormed : registryWellFormed @{r23NameEq} @{r23KeyEq}
  (replayedAfter (baseFinishReplay r27SecondFinishEnvelope)) = True
r27FinalWellFormed = r25FinalWellFormed

0 r27TargetQuiet : quiet @{r23NameEq} @{r23KeyEq}
  (replayedAfter (baseFinishReplay r27SecondFinishEnvelope)) = True
r27TargetQuiet = r25TargetQuiet

0 r27TargetNoFailure : noFailedFibers
  (replayedAfter (baseFinishReplay r27SecondFinishEnvelope)) = True
r27TargetNoFailure = r25TargetNoFailure

0 r27WholeTotal : TraceComponentsTotal r23NameEq r23KeyEq r27WholeTargetTrace
r27WholeTotal = r25WholeTotal

0 r27MovedRightBoundaryImpossible : iteratorBoundaryImpossible
  (movedRight (baseDiamond r25AlignedDiamond))
r27MovedRightBoundaryImpossible actor actionSame fiber found remaining accumulator
  view lifecycle step rest suffix = r23Begin2NotAdvance actor
    (trans (sym (movedRightAction (baseDiamond r25AlignedDiamond))) actionSame)

0 r27MovedLeftBoundaryImpossible : iteratorBoundaryImpossible
  (movedLeft (baseDiamond r25AlignedDiamond))
r27MovedLeftBoundaryImpossible actor actionSame fiber found remaining accumulator
  view lifecycle step rest suffix = r23Begin1NotAdvance actor
    (trans (sym (movedLeftAction (baseDiamond r25AlignedDiamond))) actionSame)

0 r27CanonicalFinishBoundary :
  {sourceActor : Nat} ->
  {sourceBefore, sourceAfter, replayedBefore :
    SystemState Nat R23Key R23Value Unit Unit} ->
  {sourceChecked : checkedApplyAction @{r23NameEq} @{r23KeyEq}
    (LAdvance sourceActor) sourceBefore = Just (LFinishTag, sourceAfter)} ->
  (replay : R24CheckedEmptyFinishReplay sourceActor sourceBefore sourceAfter
    replayedBefore sourceChecked) ->
  ((selected : Nat) -> IteratorStage Nat R23Key Unit Unit R23Value selected
    (MoreTransitions
      (r24FinishTransition sourceActor sourceBefore sourceAfter sourceChecked)
      NoTransitions) -> Void) ->
  iteratorBoundaryImpossible
    (Fired {before = replayedBefore} {afterState = replayedAfter replay}
      r23NameEq r23KeyEq (LAdvance sourceActor) LFinishTag
      (replayedChecked replay))
r27CanonicalFinishBoundary replay sourceNoIterator actor actionSame fiber found
  remaining accumulator view lifecycle step rest suffix = case actionSame of
    Refl =>
      let 0 canonicalStage : IteratorStage Nat R23Key Unit Unit R23Value actor
            (MoreTransitions
              (Fired {before = replayedBefore}
                {afterState = replayedAfter replay}
                r23NameEq r23KeyEq (LAdvance sourceActor) LFinishTag
                (replayedChecked replay)) NoTransitions)
          canonicalStage = StageFromAdvance r23NameEq r23KeyEq actor LFinishTag
            (replayedChecked replay) OccursHere fiber found remaining accumulator
            view lifecycle step rest suffix
          0 localStage : IteratorStage Nat R23Key Unit Unit R23Value actor
            (MoreTransitions (replayedTransition replay) NoTransitions)
          localStage = replace
            {p = \transition => IteratorStage Nat R23Key Unit Unit R23Value
              actor (MoreTransitions transition NoTransitions)}
            (sym (r25CanonicalTransitionExact replay)) canonicalStage
          0 sourceStage : IteratorStage Nat R23Key Unit Unit R23Value actor
            (MoreTransitions
              (r24FinishTransition sourceActor sourceBefore sourceAfter
                sourceChecked) NoTransitions)
          sourceStage = replayIteratorStageOrigin (perStepRAR replay) actor
            localStage
      in sourceNoIterator actor sourceStage

0 r27FinishBoundary :
  {sourceActor : Nat} ->
  {sourceBefore, sourceAfter, replayedBefore :
    SystemState Nat R23Key R23Value Unit Unit} ->
  {sourceChecked : checkedApplyAction @{r23NameEq} @{r23KeyEq}
    (LAdvance sourceActor) sourceBefore = Just (LFinishTag, sourceAfter)} ->
  (envelope : R27MapRetainedFinishReplay sourceActor sourceBefore sourceAfter
    replayedBefore sourceChecked) ->
  ((selected : Nat) -> IteratorStage Nat R23Key Unit Unit R23Value selected
    (MoreTransitions
      (r24FinishTransition sourceActor sourceBefore sourceAfter sourceChecked)
      NoTransitions) -> Void) ->
  iteratorBoundaryImpossible (replayedTransition (baseFinishReplay envelope))
r27FinishBoundary envelope sourceNoIterator = replace
  {p = \transition => iteratorBoundaryImpossible transition}
  (sym (r25CanonicalTransitionExact (baseFinishReplay envelope)))
  (r27CanonicalFinishBoundary (baseFinishReplay envelope) sourceNoIterator)

0 r27FirstBoundaryImpossible : iteratorBoundaryImpossible
  (replayedTransition (baseFinishReplay r27FirstFinishEnvelope))
r27FirstBoundaryImpossible = r27FinishBoundary r27FirstFinishEnvelope
  (r24EmptyFinishNoIterator 1 r23AfterPair r23AfterAdvance1
    r23Advance1Checked r23Begun Refl id EmptyView Refl)

0 r27SecondBoundaryImpossible : iteratorBoundaryImpossible
  (replayedTransition (baseFinishReplay r27SecondFinishEnvelope))
r27SecondBoundaryImpossible = r27FinishBoundary r27SecondFinishEnvelope
  (r24EmptyFinishNoIterator 2 r23AfterAdvance1 r23Final
    r23Advance2Checked r23Begun Refl id EmptyView Refl)

0 r27IteratorFree : IteratorFreeTrace r27WholeTargetTrace
r27IteratorFree = IteratorFreeStep r23Insert1 _ r23Insert1BoundaryImpossible
  (IteratorFreeStep r23Insert2 _ r23Insert2BoundaryImpossible
    (IteratorFreeStep (movedRight (baseDiamond r25AlignedDiamond)) _
      r27MovedRightBoundaryImpossible
      (IteratorFreeStep (movedLeft (baseDiamond r25AlignedDiamond)) _
        r27MovedLeftBoundaryImpossible
        (IteratorFreeStep
          (replayedTransition (baseFinishReplay r27FirstFinishEnvelope)) _
          r27FirstBoundaryImpossible
          (IteratorFreeStep
            (replayedTransition (baseFinishReplay r27SecondFinishEnvelope))
            NoTransitions r27SecondBoundaryImpossible IteratorFreeEnd)))))

public export
0 r27NoIterator :
  {actor : Nat} ->
  IteratorStage Nat R23Key Unit Unit R23Value actor r27WholeTargetTrace -> Void
r27NoIterator = iteratorFreeTraceHasNoStage r27IteratorFree

0 r27BeginMapIdentity :
  {before, afterState : SystemState Nat R23Key R23Value Unit Unit} ->
  (transition : Transition before afterState) ->
  (actor : Nat) ->
  transitionAction transition = LBegin actor ->
  (state : EffectState Nat R23Key R23Value Unit) ->
  partialEffectMap transition state = Just state
r27BeginMapIdentity (Fired nameEq keyEq action tag checked) actor actionExact
  state = case actionExact of Refl => Refl

0 r27MovedRightMapIdentity :
  (state : EffectState Nat R23Key R23Value Unit) ->
  partialEffectMap (movedRight (baseDiamond r25AlignedDiamond)) state = Just state
r27MovedRightMapIdentity = r27BeginMapIdentity
  (movedRight (baseDiamond r25AlignedDiamond)) 2
  (movedRightAction (baseDiamond r25AlignedDiamond))

0 r27MovedLeftMapIdentity :
  (state : EffectState Nat R23Key R23Value Unit) ->
  partialEffectMap (movedLeft (baseDiamond r25AlignedDiamond)) state = Just state
r27MovedLeftMapIdentity = r27BeginMapIdentity
  (movedLeft (baseDiamond r25AlignedDiamond)) 1
  (movedLeftAction (baseDiamond r25AlignedDiamond))

public export
0 r27ActualMapsTotal : ActualMapsTotalTrace r27WholeTargetTrace
r27ActualMapsTotal = ActualMapsTotalStep r23Insert1 _ r23Insert1MapTotal
  (ActualMapsTotalStep r23Insert2 _ r23Insert2MapTotal
    (ActualMapsTotalStep (movedRight (baseDiamond r25AlignedDiamond)) _
      (\state => (state ** r27MovedRightMapIdentity state))
      (ActualMapsTotalStep (movedLeft (baseDiamond r25AlignedDiamond)) _
        (\state => (state ** r27MovedLeftMapIdentity state))
        (ActualMapsTotalStep
          (replayedTransition (baseFinishReplay r27FirstFinishEnvelope)) _
          (\state => (state **
            retainedTargetMapIdentity r27FirstFinishEnvelope state))
          (ActualMapsTotalStep
            (replayedTransition (baseFinishReplay r27SecondFinishEnvelope))
            NoTransitions
            (\state => (state **
              retainedTargetMapIdentity r27SecondFinishEnvelope state))
            ActualMapsTotalEnd)))))

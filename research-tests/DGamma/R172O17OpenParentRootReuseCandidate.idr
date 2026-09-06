module DGamma.R172O17OpenParentRootReuseCandidate

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import DGamma.CP3
import DGamma.CP3Support
import DGamma.CP4Support
import DGamma.CP4TerminalRecovery
import DGamma.CP4RecoveryModelTrace
import DGamma.CP4RecoveryEffectRespect
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorEndpoint
import DGamma.CP4SupportSolution
import DGamma.CP4SupportQuiescence
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Candidate only: an open parent yields a child that is removed and reissued as a root.
||| Checked trace facts below are not by themselves a refutation of the full O17 telescope.

public export
r172ReuseRootFresh : Fiber Nat R45Key R45Value Unit String
r172ReuseRootFresh = freshFiber r45Child Root

public export
r172ReuseAfterRoot : SystemState Nat R45Key R45Value Unit String
r172ReuseAfterRoot = MkSystemState () (insertBinding @{r45NameEq} 1 r172ReuseRootFresh (registry r45AfterBegin) Refl)

public export
r172ReuseRootRetired : Fiber Nat R45Key R45Value Unit String
r172ReuseRootRetired = retireFiber r172ReuseRootFresh

public export
r172ReuseAfterRetire : SystemState Nat R45Key R45Value Unit String
r172ReuseAfterRetire = MkSystemState () (replaceBinding @{r45NameEq} 1 r172ReuseRootRetired (registry r172ReuseAfterRoot))

||| Use the actual checked evaluator output; the later checked equation excludes the default branch.
public export
r172ReuseFinal : SystemState Nat R45Key R45Value Unit String
r172ReuseFinal = maybe r45AfterBegin snd (checkedApplyAction @{r45NameEq} @{r45KeyEq} (LAdvance 0) r172ReuseAfterRetire)

public export
0 r172ReuseRemoveChecked : checkedApplyAction @{r45NameEq} @{r45KeyEq} (ORemove 1) r45SourceFinal = Just (ORemoveTag, r45AfterBegin)
r172ReuseRemoveChecked = Refl

public export
0 r172ReuseRootChecked : checkedApplyAction @{r45NameEq} @{r45KeyEq} (OInsert 1 Root r45Child) r45AfterBegin = Just (OInsertTag, r172ReuseAfterRoot)
r172ReuseRootChecked = Refl

public export
0 r172ReuseRetireChecked : checkedApplyAction @{r45NameEq} @{r45KeyEq} (ORetire 1) r172ReuseAfterRoot = Just (ORetireTag, r172ReuseAfterRetire)
r172ReuseRetireChecked = Refl

public export
0 r172ReuseFinishChecked : checkedApplyAction @{r45NameEq} @{r45KeyEq} (LAdvance 0) r172ReuseAfterRetire = Just (LFinishTag, r172ReuseFinal)
r172ReuseFinishChecked = Refl

public export
r172ReuseRemove : Transition r45SourceFinal r45AfterBegin
r172ReuseRemove = Fired r45NameEq r45KeyEq (ORemove 1) ORemoveTag r172ReuseRemoveChecked

public export
r172ReuseRoot : Transition r45AfterBegin r172ReuseAfterRoot
r172ReuseRoot = Fired r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag r172ReuseRootChecked

public export
r172ReuseRetire : Transition r172ReuseAfterRoot r172ReuseAfterRetire
r172ReuseRetire = Fired r45NameEq r45KeyEq (ORetire 1) ORetireTag r172ReuseRetireChecked

public export
r172ReuseFinish : Transition r172ReuseAfterRetire r172ReuseFinal
r172ReuseFinish = Fired r45NameEq r45KeyEq (LAdvance 0) LFinishTag r172ReuseFinishChecked

public export
r172ReuseTail : Transitions r45SourceFinal r172ReuseFinal
r172ReuseTail = MoreTransitions r172ReuseRemove (MoreTransitions r172ReuseRoot
  (MoreTransitions r172ReuseRetire (MoreTransitions r172ReuseFinish NoTransitions)))

public export
r172ReuseTrace : Transitions r45Initial r172ReuseFinal
r172ReuseTrace = appendTransitions r45SourceTrace r172ReuseTail

public export
0 r172ReuseAligned : AlignedTransitions Nat R45Key Unit String R45Value r45NameEq r45KeyEq r172ReuseTrace
r172ReuseAligned = AlignedStep (OInsert 0 Root r45Parent) OInsertTag r45ParentInsertChecked _
  (AlignedStep (LBegin 0) LBeginTag r45BeginChecked _
    (AlignedStep (OInsert 1 (ChildOf 0) r45Child) OInsertTag r45ChildInsertChecked _
      (AlignedStep (ORetire 1) ORetireTag r45SourceRetireChecked _
        (AlignedStep (ORemove 1) ORemoveTag r172ReuseRemoveChecked _
          (AlignedStep (OInsert 1 Root r45Child) OInsertTag r172ReuseRootChecked _
            (AlignedStep (ORetire 1) ORetireTag r172ReuseRetireChecked _
              (AlignedStep (LAdvance 0) LFinishTag r172ReuseFinishChecked _ AlignedEnd)))))))

public export
0 r172ReuseDiscipline : RegistrationDiscipline r45Protocol r45NameEq r172ReuseTrace
r172ReuseDiscipline = RegistrationDisciplineStep r45ParentInsert _ (0 ** Refl)
  (RegistrationDisciplineStep r45Begin _ ()
    (RegistrationDisciplineStep r45ChildInsert _
      (r45SourceYield, ChildRetiredBeforeParent (ChildRetiresNow r45SourceRetire r172ReuseTail Refl))
      (RegistrationDisciplineStep r45SourceRetire _ ()
        (RegistrationDisciplineStep r172ReuseRemove _ ()
          (RegistrationDisciplineStep r172ReuseRoot _ (1 ** Refl)
            (RegistrationDisciplineStep r172ReuseRetire _ ()
              (RegistrationDisciplineStep r172ReuseFinish _ () RegistrationDisciplineEnd)))))))

public export
0 r172ReuseInitialWellFormed : registryWellFormed @{r45NameEq} @{r45KeyEq} r45Initial = True
r172ReuseInitialWellFormed = Refl

public export
0 r172ReuseInitialEmpty : bindings (registry r45Initial) = []
r172ReuseInitialEmpty = Refl

public export
0 r172ReuseFinalWellFormed : registryWellFormed @{r45NameEq} @{r45KeyEq} r172ReuseFinal = True
r172ReuseFinalWellFormed = Refl

public export
0 r172ReuseQuiet : quiet @{r45NameEq} @{r45KeyEq} r172ReuseFinal = True
r172ReuseQuiet = Refl

public export
0 r172ReuseNoFailure : noFailedFibers r172ReuseFinal = True
r172ReuseNoFailure = Refl

public export
0 r172ReuseSupportSet : supportSet @{r45NameEq} @{r45KeyEq} r172ReuseFinal = [0]
r172ReuseSupportSet = Refl

public export
0 r172ReuseAnyTransitionTotal :
  {before, afterState : SystemState Nat R45Key R45Value Unit String} ->
  (transition : Transition before afterState) ->
  TransitionComponentTotal r45NameEq r45KeyEq transition
r172ReuseAnyTransitionTotal transition fiber found active key occurrence = case key of _ impossible

public export
0 r172ReuseTotal : TraceComponentsTotal r45NameEq r45KeyEq r172ReuseTrace
r172ReuseTotal = TraceComponentsTotalStep r45ParentInsert _ (r172ReuseAnyTransitionTotal r45ParentInsert)
  (TraceComponentsTotalStep r45Begin _ (r172ReuseAnyTransitionTotal r45Begin)
    (TraceComponentsTotalStep r45ChildInsert _ (r172ReuseAnyTransitionTotal r45ChildInsert)
      (TraceComponentsTotalStep r45SourceRetire _ (r172ReuseAnyTransitionTotal r45SourceRetire)
        (TraceComponentsTotalStep r172ReuseRemove _ (r172ReuseAnyTransitionTotal r172ReuseRemove)
          (TraceComponentsTotalStep r172ReuseRoot _ (r172ReuseAnyTransitionTotal r172ReuseRoot)
            (TraceComponentsTotalStep r172ReuseRetire _ (r172ReuseAnyTransitionTotal r172ReuseRetire)
              (TraceComponentsTotalStep r172ReuseFinish _ (r172ReuseAnyTransitionTotal r172ReuseFinish) TraceComponentsTotalEnd)))))))

public export
0 r172ReuseEmptyKeyBindings : (context : CoeffectContext R45Key R45Value) -> bindings context = []
r172ReuseEmptyKeyBindings (MkCoeffectContext [] unique) = Refl
r172ReuseEmptyKeyBindings (MkCoeffectContext (Bind key value :: rest) unique) = case key of _ impossible

public export
0 r172ReuseAllEffectStatesRelated : (left, right : EffectState Nat R45Key R45Value Unit) -> EffectStateRelated r45KeyEq left right
r172ReuseAllEffectStatesRelated (MkEffectState () leftTables) (MkEffectState () rightTables) =
  MkEffectStateRelated Refl (\selected => trans (r172ReuseEmptyKeyBindings (leftTables selected)) (sym (r172ReuseEmptyKeyBindings (rightTables selected))))

public export
0 r172ReuseRelatedBind :
  (leftBefore, rightBefore : Maybe (EffectState Nat R45Key R45Value Unit)) ->
  (after : PartialMap (EffectState Nat R45Key R45Value Unit)) ->
  PartialMapsRelated (EffectStateEquivalence r45KeyEq) after after ->
  PartialRelated (EffectState Nat R45Key R45Value Unit) (EffectStateRelated r45KeyEq) leftBefore rightBefore ->
  PartialRelated (EffectState Nat R45Key R45Value Unit) (EffectStateRelated r45KeyEq)
    (case leftBefore of Nothing => Nothing; Just middle => after middle)
    (case rightBefore of Nothing => Nothing; Just middle => after middle)
r172ReuseRelatedBind Nothing Nothing after respects PartialUndefined = PartialUndefined
r172ReuseRelatedBind (Just left) (Just right) after respects (PartialDefined related) = respects related

public export
0 r172ReuseTransformationRespects : (actor : Nat) ->
  (transformation : TraceEffectTransformation Nat R45Key Unit String R45Value actor r172ReuseTrace) ->
  PartialMapsRelated (EffectStateEquivalence r45KeyEq)
    (runTraceEffectTransformation transformation) (runTraceEffectTransformation transformation)
r172ReuseTransformationRespects actor TraceIdentity related = PartialDefined related
r172ReuseTransformationRespects actor (TraceGenerator generator) related = replayTraceGeneratorMapRespects r45KeyEq generator related
r172ReuseTransformationRespects actor (TraceCompose after before) {x} {y} related =
  composed (runTraceEffectTransformation before x) (runTraceEffectTransformation before y)
    Refl Refl (r172ReuseTransformationRespects actor before related)
  where
  0 composed :
    (leftMiddle, rightMiddle : Maybe (EffectState Nat R45Key R45Value Unit)) ->
    runTraceEffectTransformation before x = leftMiddle ->
    runTraceEffectTransformation before y = rightMiddle ->
    PartialRelated (EffectState Nat R45Key R45Value Unit) (EffectStateRelated r45KeyEq) leftMiddle rightMiddle ->
    PartialRelated (EffectState Nat R45Key R45Value Unit) (EffectStateRelated r45KeyEq)
      (partialCompose (runTraceEffectTransformation after) (runTraceEffectTransformation before) x)
      (partialCompose (runTraceEffectTransformation after) (runTraceEffectTransformation before) y)
  composed Nothing Nothing leftRuns rightRuns PartialUndefined =
    rewrite leftRuns in rewrite rightRuns in PartialUndefined
  composed (Just left) (Just right) leftRuns rightRuns (PartialDefined middleRelated) =
    rewrite leftRuns in rewrite rightRuns in r172ReuseTransformationRespects actor after middleRelated

public export
0 r172ReuseUndefinedRight :
  {result : Maybe (EffectState Nat R45Key R45Value Unit)} ->
  PartialRelated (EffectState Nat R45Key R45Value Unit) (EffectStateRelated r45KeyEq) Nothing result ->
  result = Nothing
r172ReuseUndefinedRight PartialUndefined = Refl

public export
0 r172ReuseBothDefinedRelated :
  {first, second : EffectState Nat R45Key R45Value Unit} ->
  {leftResult, rightResult : Maybe (EffectState Nat R45Key R45Value Unit)} ->
  PartialRelated (EffectState Nat R45Key R45Value Unit) (EffectStateRelated r45KeyEq) (Just first) leftResult ->
  PartialRelated (EffectState Nat R45Key R45Value Unit) (EffectStateRelated r45KeyEq) (Just second) rightResult ->
  PartialRelated (EffectState Nat R45Key R45Value Unit) (EffectStateRelated r45KeyEq) leftResult rightResult
r172ReuseBothDefinedRelated (PartialDefined firstRelated) (PartialDefined secondRelated) =
  PartialDefined (r172ReuseAllEffectStatesRelated _ _)

public export
0 r172ReuseCommuteAt :
  (left, right : PartialMap (EffectState Nat R45Key R45Value Unit)) ->
  PartialMapsRelated (EffectStateEquivalence r45KeyEq) left left ->
  PartialMapsRelated (EffectStateEquivalence r45KeyEq) right right ->
  (origin : EffectState Nat R45Key R45Value Unit) ->
  (leftResult, rightResult : Maybe (EffectState Nat R45Key R45Value Unit)) ->
  left origin = leftResult -> right origin = rightResult ->
  PartialRelated (EffectState Nat R45Key R45Value Unit) (EffectStateRelated r45KeyEq)
    (partialCompose left right origin) (partialCompose right left origin)
r172ReuseCommuteAt left right leftRespects rightRespects origin Nothing Nothing leftRuns rightRuns =
  rewrite rightRuns in rewrite leftRuns in PartialUndefined
r172ReuseCommuteAt left right leftRespects rightRespects origin Nothing (Just afterRight) leftRuns rightRuns =
  rewrite rightRuns in rewrite leftRuns in
  rewrite r172ReuseUndefinedRight (replace
    {p = \output => PartialRelated (EffectState Nat R45Key R45Value Unit) (EffectStateRelated r45KeyEq) output (left afterRight)}
    leftRuns (leftRespects (r172ReuseAllEffectStatesRelated origin afterRight))) in PartialUndefined
r172ReuseCommuteAt left right leftRespects rightRespects origin (Just afterLeft) Nothing leftRuns rightRuns =
  rewrite rightRuns in rewrite leftRuns in
  rewrite r172ReuseUndefinedRight (replace
    {p = \output => PartialRelated (EffectState Nat R45Key R45Value Unit) (EffectStateRelated r45KeyEq) output (right afterLeft)}
    rightRuns (rightRespects (r172ReuseAllEffectStatesRelated origin afterLeft))) in PartialUndefined
r172ReuseCommuteAt left right leftRespects rightRespects origin (Just afterLeft) (Just afterRight) leftRuns rightRuns =
  rewrite rightRuns in rewrite leftRuns in r172ReuseBothDefinedRelated
    (replace {p = \output => PartialRelated (EffectState Nat R45Key R45Value Unit) (EffectStateRelated r45KeyEq) output (left afterRight)}
      leftRuns (leftRespects (r172ReuseAllEffectStatesRelated origin afterRight)))
    (replace {p = \output => PartialRelated (EffectState Nat R45Key R45Value Unit) (EffectStateRelated r45KeyEq) output (right afterLeft)}
      rightRuns (rightRespects (r172ReuseAllEffectStatesRelated origin afterLeft)))

public export
0 r172ReuseMapsCommute :
  (left, right : PartialMap (EffectState Nat R45Key R45Value Unit)) ->
  PartialMapsRelated (EffectStateEquivalence r45KeyEq) left left ->
  PartialMapsRelated (EffectStateEquivalence r45KeyEq) right right ->
  PartialCommute (EffectStateEquivalence r45KeyEq) left right
r172ReuseMapsCommute left right leftRespects rightRespects origin =
  r172ReuseCommuteAt left right leftRespects rightRespects origin (left origin) (right origin) Refl Refl

public export
0 r172ReuseIteratorStableAt : (actor : Nat) ->
  (stage : IteratorStage Nat R45Key Unit String R45Value actor r172ReuseTrace) ->
  (foreign : PartialMap (EffectState Nat R45Key R45Value Unit)) ->
  (origin : EffectState Nat R45Key R45Value Unit) ->
  (moved : Maybe (EffectState Nat R45Key R45Value Unit)) ->
  foreign origin = moved -> IteratorOutcomeStableUnder r45KeyEq stage foreign origin
r172ReuseIteratorStableAt actor stage foreign origin Nothing runs = rewrite runs in ()
r172ReuseIteratorStableAt actor stage foreign origin (Just moved) runs =
  rewrite runs in iteratorStageOutcomeRelated r45KeyEq stage moved origin (r172ReuseAllEffectStatesRelated moved origin)

public export
0 r172ReuseIndependent : TraceIndependent Nat R45Key Unit String R45Value r45KeyEq r172ReuseTrace
r172ReuseIndependent = MkTraceIndependent
  (\left, right, distinct, leftT, rightT => r172ReuseMapsCommute
    (runTraceEffectTransformation leftT) (runTraceEffectTransformation rightT)
    (r172ReuseTransformationRespects left leftT) (r172ReuseTransformationRespects right rightT))
  (\left, right, distinct, stage, foreign, origin => r172ReuseIteratorStableAt left stage
    (runTraceEffectTransformation foreign) origin (runTraceEffectTransformation foreign origin) Refl)

public export
0 r172ReuseReached : ReachedFromEmpty Nat R45Key Unit String R45Value r45NameEq r45KeyEq r172ReuseFinal
r172ReuseReached = MkReachedFromEmpty r45Initial r172ReuseTrace r172ReuseAligned r172ReuseInitialEmpty r172ReuseInitialWellFormed

public export
0 r172ReuseProvenance : RegistrationProvenance r45Protocol r45NameEq r172ReuseTrace
r172ReuseProvenance = registrationDisciplineProvenance r45Protocol r45NameEq r172ReuseTrace r172ReuseDiscipline

public export
0 r172ReuseBundle : ReplayInvariantBundle Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq r172ReuseTrace
r172ReuseBundle = MkReplayInvariantBundle r172ReuseAligned r172ReuseDiscipline
  r172ReuseInitialWellFormed r172ReuseInitialEmpty r172ReuseFinalWellFormed r172ReuseQuiet
  r172ReuseNoFailure r172ReuseTotal r172ReuseIndependent r172ReuseProvenance
  (reachedRegistryProtocolRanked r45Protocol r45NameEq r45KeyEq r172ReuseReached r172ReuseProvenance)
  (reachedRegistryParentRanksIncrease r45Protocol r45NameEq r45KeyEq r172ReuseReached r172ReuseProvenance)
  (disciplinedEndpointPrecedenceAcyclic r45Protocol r45NameEq r45KeyEq r172ReuseFinal r172ReuseReached r172ReuseDiscipline)
  (supportCombinedWellFounded r45Protocol r45NameEq r172ReuseFinal
    (reachedRegistryProtocolRanked r45Protocol r45NameEq r45KeyEq r172ReuseReached r172ReuseProvenance)
    (reachedRegistryParentRanksIncrease r45Protocol r45NameEq r45KeyEq r172ReuseReached r172ReuseProvenance))
  (deletionPremisesGiveSupportMatchesActive r45Protocol r45NameEq r45KeyEq r45Initial r172ReuseFinal
    r172ReuseTrace r172ReuseAligned r172ReuseDiscipline r172ReuseInitialWellFormed r172ReuseInitialEmpty
    r172ReuseQuiet r172ReuseNoFailure r172ReuseTotal)

public export
0 r172ReuseNoUnload :
  {before, afterState : SystemState Nat R45Key R45Value Unit String} ->
  (transition : Transition before afterState) -> transitionTag transition = LUnloadTag ->
  OccursIn transition r172ReuseTrace -> Void
r172ReuseNoUnload _ Refl OccursHere impossible
r172ReuseNoUnload _ Refl (OccursLater OccursHere) impossible
r172ReuseNoUnload _ Refl (OccursLater (OccursLater OccursHere)) impossible
r172ReuseNoUnload _ Refl (OccursLater (OccursLater (OccursLater OccursHere))) impossible
r172ReuseNoUnload _ Refl (OccursLater (OccursLater (OccursLater (OccursLater OccursHere)))) impossible
r172ReuseNoUnload _ Refl (OccursLater (OccursLater (OccursLater (OccursLater (OccursLater OccursHere))))) impossible
r172ReuseNoUnload _ Refl (OccursLater (OccursLater (OccursLater (OccursLater (OccursLater (OccursLater OccursHere)))))) impossible
r172ReuseNoUnload _ Refl (OccursLater (OccursLater (OccursLater (OccursLater (OccursLater (OccursLater (OccursLater OccursHere))))))) impossible
r172ReuseNoUnload transition tag (OccursLater (OccursLater (OccursLater (OccursLater (OccursLater (OccursLater (OccursLater (OccursLater later)))))))) = case later of OccursHere impossible; OccursLater rest impossible

public export
0 r172ReuseAppendRightOccurrence :
  {first, middle, finalState, before, afterState : SystemState Nat R45Key R45Value Unit String} ->
  (left : Transitions first middle) -> (right : Transitions middle finalState) ->
  (transition : Transition before afterState) -> OccursIn transition right ->
  OccursIn transition (appendTransitions left right)
r172ReuseAppendRightOccurrence NoTransitions right transition occurs = occurs
r172ReuseAppendRightOccurrence (MoreTransitions head rest) right transition occurs =
  OccursLater (r172ReuseAppendRightOccurrence rest right transition occurs)

public export
0 r172ReuseClosingOccurs :
  {selected : Nat} -> {initial, finalState : SystemState Nat R45Key R45Value Unit String} ->
  {trace : Transitions initial finalState} ->
  (located : LocatedClosedEpisode Nat R45Key Unit String R45Value r45NameEq r45KeyEq selected trace) ->
  OccursIn (unloadTransition (closing (locatedEpisode located))) trace
r172ReuseClosingOccurs (MkLocatedClosedEpisode pre after earlier episode suffix decomposition) =
  replace {p = \global => OccursIn (unloadTransition (closing episode)) global} decomposition
    (r172ReuseAppendRightOccurrence earlier _ _
      (OccursLater (appendLeftOccurrenceEmbedding (closedTransitions episode) suffix _
        (r172ReuseAppendRightOccurrence (closedInside episode)
          (MoreTransitions (unloadTransition (closing episode)) NoTransitions) _ OccursHere))))

public export
0 r172ReuseNoClosing : NoClosingEpisodes Nat R45Key Unit String R45Value r45NameEq r45KeyEq r172ReuseTrace
r172ReuseNoClosing selected located = r172ReuseNoUnload
  (unloadTransition (closing (locatedEpisode located))) Refl (r172ReuseClosingOccurs located)

public export
0 r172ReuseShape : ClosingFreeTraceShape Nat R45Key Unit String R45Value r45NameEq r45KeyEq r172ReuseTrace
r172ReuseShape = closingFreeTraceShapeSpike r45NameEq r45KeyEq r45Protocol r172ReuseTrace r172ReuseNoClosing r172ReuseBundle

public export
0 r172ReuseOrdering : SupportOrderingCapital Nat R45Key Unit String R45Value r45NameEq r45KeyEq r172ReuseFinal
r172ReuseOrdering = supportOrderingSpike r45NameEq r45KeyEq r45Protocol r172ReuseTrace r172ReuseBundle

||| The identity/terminal route is genuinely unavailable; this is not a global sorting refutation.
public export
0 r172ReuseSourceNotRootFirst : RootInputsBeforeLifecycle r45NameEq r172ReuseTrace -> Void
r172ReuseSourceNotRootFirst
  (RootInputsBeforeLifecycleStep _ _ _ (RootInputsBeforeLifecycleStep _ _ noRoot later)) =
    forbiddenRoot _ (noRoot Refl) r172ReuseRoot
      (OccursLater (OccursLater (OccursLater OccursHere))) (RootInsertStep Refl)
  where
  0 forbiddenRoot :
    {first, finalState, before, afterState : SystemState Nat R45Key R45Value Unit String} ->
    (trace : Transitions first finalState) -> NoRootOrchestration r45NameEq trace ->
    (transition : Transition before afterState) -> OccursIn transition trace ->
    RootOrchestrationStep r45NameEq transition -> Void
  forbiddenRoot (MoreTransitions transition rest) (NoRootOrchestrationStep _ _ excluded later)
    transition OccursHere root = excluded root
  forbiddenRoot (MoreTransitions head rest) (NoRootOrchestrationStep _ _ excluded later)
    transition (OccursLater occurs) root = forbiddenRoot rest later transition occurs root
  forbiddenRoot NoTransitions NoRootOrchestrationEnd transition occurs root =
    case occurs of OccursHere impossible; OccursLater later impossible

||| The later same-name root cannot be hoisted across its immediate child removal.
public export
0 r172ReuseRootBeforeRemoveRejected : checkedApplyAction @{r45NameEq} @{r45KeyEq}
  (OInsert 1 Root r45Child) r45SourceFinal = Nothing
r172ReuseRootBeforeRemoveRejected = Refl

public export
0 r172ReuseMovedRootImpossible :
  {middle, finalState : SystemState Nat R45Key R45Value Unit String} ->
  (moved : Transition r45SourceFinal middle) -> (rest : Transitions middle finalState) ->
  AlignedTransitions Nat R45Key Unit String R45Value r45NameEq r45KeyEq (MoreTransitions moved rest) ->
  transitionAction moved = OInsert 1 Root r45Child -> Void
r172ReuseMovedRootImpossible _ rest (AlignedStep action tag checked _ later) same =
  case same of Refl => case trans (sym r172ReuseRootBeforeRemoveRejected) checked of Refl impossible

||| Exact local wall only: no conclusion about every finite sorting derivation is asserted.
public export
0 r172ReuseRemoveRootDiamondImpossible :
  LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq r172ReuseRemove r172ReuseRoot -> Void
r172ReuseRemoveRootDiamondImpossible diamond = r172ReuseMovedRootImpossible
  (movedRight diamond) (MoreTransitions (movedLeft diamond) NoTransitions)
  (movedPairAligned diamond) (movedRightAction diamond)

public export
0 r172ReuseOrderingIsParentOnly : orderedSupportNames r172ReuseOrdering = [0]
r172ReuseOrderingIsParentOnly = singletonEnumeration (orderedSupportNames r172ReuseOrdering)
  (orderUnique (orderedSupportLinearization r172ReuseOrdering))
  (\selected, present => onlyParent selected (orderSound (orderedSupportLinearization r172ReuseOrdering) selected present))
  (orderComplete (orderedSupportLinearization r172ReuseOrdering) 0 Refl)
  where
  0 onlyParent : (selected : Nat) -> isSupported @{r45NameEq} @{r45KeyEq} selected r172ReuseFinal = True -> selected = 0
  onlyParent Z supported = Refl
  onlyParent (S selected) supported = case supported of Refl impossible

  0 singletonEnumeration : (names : List Nat) -> UniqueKeys names ->
    ((selected : Nat) -> Elem selected names -> selected = 0) -> Elem 0 names -> names = [0]
  singletonEnumeration [] unique sound present = case present of Here impossible; There later impossible
  singletonEnumeration [selected] unique sound present = case sound selected Here of Refl => Refl
  singletonEnumeration (first :: second :: rest) (UniqueCons missing unique) sound present =
    void (missing (replace {p = \selected => Elem selected (second :: rest)}
      (trans (sound second (There Here)) (sym (sound first Here))) Here))

||| Precisely stated target only. No inhabitant or universal refutation is claimed here.
public export
0 R172ReuseGlobalSortingRefutation : Type
R172ReuseGlobalSortingRefutation =
  ((sorted : (SortedClosingFreeTrace Nat R45Key Unit String R45Value
    r45Protocol r45NameEq r45KeyEq r172ReuseTrace r172ReuseOrdering)) -> Void)

public export
0 r172ReuseConclusionRootFirst :
  (sorted : SortedClosingFreeTrace Nat R45Key Unit String R45Value
    r45Protocol r45NameEq r45KeyEq r172ReuseTrace r172ReuseOrdering) ->
  RootInputsBeforeLifecycle r45NameEq (sortedTrace sorted)
r172ReuseConclusionRootFirst sorted = allRootInputsFirst (sortedInputPlacement sorted)

public export
0 r172ReuseOriginalChildBirth : LocatedGeneratedRegistration 1 0 r45Child r172ReuseTrace
r172ReuseOriginalChildBirth = MkLocatedGeneratedRegistration r45AfterBegin r45SourcePairFinal
  (MoreTransitions r45ParentInsert (MoreTransitions r45Begin NoTransitions)) r45ChildInsert
  (MoreTransitions r45SourceRetire r172ReuseTail) Refl Refl

public export
0 r172ReuseConclusionChildBirth :
  (sorted : SortedClosingFreeTrace Nat R45Key Unit String R45Value
    r45Protocol r45NameEq r45KeyEq r172ReuseTrace r172ReuseOrdering) ->
  LocatedGeneratedRegistration 1 0 r45Child (sortedTrace sorted)
r172ReuseConclusionChildBirth sorted =
  case originalRegistrationAccounted (sortedRegistrationTree sorted) r172ReuseOriginalChildBirth of
    Left withdrawn => case replace
      {p = \omitted => Elem (registrationGeneration r172ReuseOriginalChildBirth) omitted}
      (sortedWithdrawsNoGenerations sorted) withdrawn of Here impossible; There later impossible
    Right (actual ** originalMatches) => actual

public export
0 r172ReuseExternalRootForward :
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState Nat R45Key R45Value Unit String} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  SameExternalOrchestration r45NameEq left right ->
  ActionOccurs (OInsert 1 Root r45Child) left -> ActionOccurs (OInsert 1 Root r45Child) right
r172ReuseExternalRootForward SameExternalOrchestrationEnd occurrence =
  case occurrence of ActionOccursHere _ _ _ impossible; ActionOccursLater _ _ _ impossible
r172ReuseExternalRootForward (SkipLeftInternal head rest excluded same) (ActionOccursHere _ _ rootAction) =
  void (excluded (RootInsertStep rootAction))
r172ReuseExternalRootForward (SkipLeftInternal head rest excluded same) (ActionOccursLater _ _ later) =
  r172ReuseExternalRootForward same later
r172ReuseExternalRootForward (SkipRightInternal head rest excluded same) occurrence =
  ActionOccursLater head rest (r172ReuseExternalRootForward same occurrence)
r172ReuseExternalRootForward
  (MatchExternalInput action left leftRest leftRoot right rightRest rightRoot leftAction rightAction same)
  (ActionOccursHere _ _ rootAction) =
    ActionOccursHere right rightRest (trans rightAction (trans (sym leftAction) rootAction))
r172ReuseExternalRootForward
  (MatchExternalInput action left leftRest leftRoot right rightRest rightRoot leftAction rightAction same)
  (ActionOccursLater _ _ later) = ActionOccursLater right rightRest (r172ReuseExternalRootForward same later)

public export
0 r172ReuseOriginalRootOccurs : ActionOccurs (OInsert 1 Root r45Child) r172ReuseTrace
r172ReuseOriginalRootOccurs = ActionOccursLater r45ParentInsert _ (ActionOccursLater r45Begin _
  (ActionOccursLater r45ChildInsert _ (ActionOccursLater r45SourceRetire _
    (ActionOccursLater r172ReuseRemove _ (ActionOccursHere r172ReuseRoot _ Refl)))))

public export
0 r172ReuseConclusionRootOccurs :
  (sorted : SortedClosingFreeTrace Nat R45Key Unit String R45Value
    r45Protocol r45NameEq r45KeyEq r172ReuseTrace r172ReuseOrdering) ->
  ActionOccurs (OInsert 1 Root r45Child) (sortedTrace sorted)
r172ReuseConclusionRootOccurs sorted = r172ReuseExternalRootForward (sortedSameInputs sorted) r172ReuseOriginalRootOccurs

public export
0 r172ReuseLocateAction :
  {first, finalState : SystemState Nat R45Key R45Value Unit String} ->
  {trace : Transitions first finalState} -> {action : Action Nat R45Key R45Value Unit String} ->
  ActionOccurs action trace -> LocatedActionOccurrence action trace
r172ReuseLocateAction (ActionOccursHere transition rest same) =
  MkLocatedActionOccurrence _ _ NoTransitions transition rest same Refl
r172ReuseLocateAction (ActionOccursLater head rest later) =
  case r172ReuseLocateAction later of
    MkLocatedActionOccurrence before after earlier transition suffix same decomposition =>
      MkLocatedActionOccurrence before after (MoreTransitions head earlier) transition suffix same
        (cong (MoreTransitions head) decomposition)

public export
0 r172ReuseConclusionRootBirth :
  (sorted : SortedClosingFreeTrace Nat R45Key Unit String R45Value
    r45Protocol r45NameEq r45KeyEq r172ReuseTrace r172ReuseOrdering) ->
  LocatedActionOccurrence (OInsert 1 Root r45Child) (sortedTrace sorted)
r172ReuseConclusionRootBirth sorted = r172ReuseLocateAction (r172ReuseConclusionRootOccurs sorted)

public export
0 r172ReuseRegistrationStepAt :
  {first, before, afterState, finalState : SystemState Nat R45Key R45Value Unit String} ->
  (earlier : Transitions first before) -> (transition : Transition before afterState) ->
  (later : Transitions afterState finalState) ->
  RegistrationDiscipline r45Protocol r45NameEq (appendTransitions earlier (MoreTransitions transition later)) ->
  RegistrationStepDiscipline r45Protocol r45NameEq (transitionAction transition) before later
r172ReuseRegistrationStepAt NoTransitions transition later (RegistrationDisciplineStep _ _ atStep rest) = atStep
r172ReuseRegistrationStepAt (MoreTransitions head tail) transition later (RegistrationDisciplineStep _ _ atStep rest) =
  r172ReuseRegistrationStepAt tail transition later rest

public export
0 r172ReuseConclusionChildYield :
  (sorted : SortedClosingFreeTrace Nat R45Key Unit String R45Value
    r45Protocol r45NameEq r45KeyEq r172ReuseTrace r172ReuseOrdering) ->
  (birth : LocatedGeneratedRegistration 1 0 r45Child (sortedTrace sorted)) ->
  ParentRegistrationYield r45Protocol r45NameEq 0 r45Child (registrationBefore birth)
r172ReuseConclusionChildYield sorted birth = fst (replace
  {p = \action => RegistrationStepDiscipline r45Protocol r45NameEq action (registrationBefore birth) (afterRegistration birth)}
  (registrationAction birth)
  (r172ReuseRegistrationStepAt (beforeRegistration birth) (registrationTransition birth) (afterRegistration birth)
    (replace {p = \trace => RegistrationDiscipline r45Protocol r45NameEq trace}
      (sym (registrationDecomposition birth)) (replayDiscipline (sortedPremises sorted)))))

public export
0 r172ReuseYieldParentInstalled : {before : SystemState Nat R45Key R45Value Unit String} ->
  ParentRegistrationYield r45Protocol r45NameEq 0 r45Child before -> installedAt @{r45NameEq} 0 before = True
r172ReuseYieldParentInstalled yielded =
  rewrite parentFoundAtYield yielded in rewrite parentAtYield yielded in Refl

public export
0 r172ReuseConclusionChildPrefixAligned :
  (sorted : SortedClosingFreeTrace Nat R45Key Unit String R45Value
    r45Protocol r45NameEq r45KeyEq r172ReuseTrace r172ReuseOrdering) ->
  (birth : LocatedGeneratedRegistration 1 0 r45Child (sortedTrace sorted)) ->
  AlignedTransitions Nat R45Key Unit String R45Value r45NameEq r45KeyEq (beforeRegistration birth)
r172ReuseConclusionChildPrefixAligned sorted birth = fst (alignedAppendSplit
  (beforeRegistration birth) (MoreTransitions (registrationTransition birth) (afterRegistration birth))
  (replace {p = \trace => AlignedTransitions Nat R45Key Unit String R45Value r45NameEq r45KeyEq trace}
    (sym (registrationDecomposition birth)) (replayAligned (sortedPremises sorted))))

public export
0 r172ReuseConclusionParentOpening :
  (sorted : SortedClosingFreeTrace Nat R45Key Unit String R45Value
    r45Protocol r45NameEq r45KeyEq r172ReuseTrace r172ReuseOrdering) ->
  (birth : LocatedGeneratedRegistration 1 0 r45Child (sortedTrace sorted)) ->
  LastOpeningResult Nat R45Key Unit String R45Value r45NameEq r45KeyEq 0 (beforeRegistration birth)
r172ReuseConclusionParentOpening sorted birth = extractLastOpening r45NameEq r45KeyEq 0
  (beforeRegistration birth) (r172ReuseConclusionChildPrefixAligned sorted birth)
  (emptyRegistryUninstalled r45NameEq 0 r45Initial r172ReuseInitialEmpty)
  (r172ReuseYieldParentInstalled (r172ReuseConclusionChildYield sorted birth))

public export
0 r172ReuseExtendLocatedRight :
  {first, middle, finalState : SystemState Nat R45Key R45Value Unit String} ->
  {action : Action Nat R45Key R45Value Unit String} ->
  (left : Transitions first middle) -> (right : Transitions middle finalState) ->
  (global : Transitions first finalState) -> appendTransitions left right = global ->
  LocatedActionOccurrence action left -> LocatedActionOccurrence action global
r172ReuseExtendLocatedRight left right global decomposition
  (MkLocatedActionOccurrence before after earlier transition later same located) =
    MkLocatedActionOccurrence before after earlier transition (appendTransitions later right) same
      (rewrite sym (appendTransitionsAssociative earlier (MoreTransitions transition later) right) in
       rewrite located in decomposition)

public export
0 r172ReuseLastOpeningLocated :
  {first, finalState : SystemState Nat R45Key R45Value Unit String} ->
  {trace : Transitions first finalState} ->
  LastOpeningResult Nat R45Key Unit String R45Value r45NameEq r45KeyEq 0 trace ->
  LocatedActionOccurrence (LBegin 0) trace
r172ReuseLastOpeningLocated (MkLastOpeningResult before after earlier opening later split installed) =
  MkLocatedActionOccurrence before after earlier (beginTransition opening) later Refl split

public export
0 r172ReuseConclusionParentBegin :
  (sorted : SortedClosingFreeTrace Nat R45Key Unit String R45Value
    r45Protocol r45NameEq r45KeyEq r172ReuseTrace r172ReuseOrdering) ->
  (birth : LocatedGeneratedRegistration 1 0 r45Child (sortedTrace sorted)) ->
  LocatedActionOccurrence (LBegin 0) (sortedTrace sorted)
r172ReuseConclusionParentBegin sorted birth = r172ReuseExtendLocatedRight
  (beforeRegistration birth) (MoreTransitions (registrationTransition birth) (afterRegistration birth))
  (sortedTrace sorted) (registrationDecomposition birth)
  (r172ReuseLastOpeningLocated (r172ReuseConclusionParentOpening sorted birth))

public export
0 r172ReuseCountAppend :
  {first, middle, finalState : SystemState Nat R45Key R45Value Unit String} ->
  (left : Transitions first middle) -> (right : Transitions middle finalState) ->
  transitionCount (appendTransitions left right) = transitionCount left + transitionCount right
r172ReuseCountAppend NoTransitions right = Refl
r172ReuseCountAppend (MoreTransitions head rest) right = cong S (r172ReuseCountAppend rest right)

public export
0 r172ReuseBeforeAppendSuccessor : (left, right : Nat) -> LT left (left + S right)
r172ReuseBeforeAppendSuccessor Z right = LTESucc LTEZero
r172ReuseBeforeAppendSuccessor (S left) right = LTESucc (r172ReuseBeforeAppendSuccessor left right)

public export
0 r172ReuseLastOpeningBeforeEnd :
  {first, finalState : SystemState Nat R45Key R45Value Unit String} ->
  {trace : Transitions first finalState} ->
  (opening : LastOpeningResult Nat R45Key Unit String R45Value r45NameEq r45KeyEq 0 trace) ->
  LT (locatedActionOrdinal (r172ReuseLastOpeningLocated opening)) (transitionCount trace)
r172ReuseLastOpeningBeforeEnd (MkLastOpeningResult before after earlier opening later split installed) =
  rewrite sym split in rewrite r172ReuseCountAppend earlier (MoreTransitions (beginTransition opening) later) in
    r172ReuseBeforeAppendSuccessor (transitionCount earlier) (transitionCount later)

public export
0 r172ReuseExtendLocatedOrdinal :
  {first, middle, finalState : SystemState Nat R45Key R45Value Unit String} ->
  {action : Action Nat R45Key R45Value Unit String} ->
  (left : Transitions first middle) -> (right : Transitions middle finalState) ->
  (global : Transitions first finalState) -> (split : appendTransitions left right = global) ->
  (occurrence : LocatedActionOccurrence action left) ->
  locatedActionOrdinal (r172ReuseExtendLocatedRight left right global split occurrence) = locatedActionOrdinal occurrence
r172ReuseExtendLocatedOrdinal left right global split (MkLocatedActionOccurrence before after earlier transition later same located) = Refl

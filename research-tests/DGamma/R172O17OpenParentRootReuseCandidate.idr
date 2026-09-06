module DGamma.R172O17OpenParentRootReuseCandidate

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import DGamma.CP3
import DGamma.CP3Support
import DGamma.CP4Support
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


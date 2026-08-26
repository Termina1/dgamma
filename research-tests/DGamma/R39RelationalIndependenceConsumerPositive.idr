module DGamma.R39RelationalIndependenceConsumerPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import DGamma.CP4DeletionSelectedForeignLifecycleAdvanceOutcome
import DGamma.CP4RecoveryEffectRespect
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R39RelationalMapAlgebraPositive
import DGamma.R39TraceGeneratorRespectPositive
import Decidable.Equality

%default total

0 r39EquivalentMapsSymmetric :
  PartialMapsEquivalent (EffectStateEquivalence keyEq) left right ->
  PartialMapsEquivalent (EffectStateEquivalence keyEq) right left
r39EquivalentMapsSymmetric maps input =
  r39EffectPartialSymmetric (maps input)

0 r39OutcomeAgreementSymmetric :
  IteratorOutcomeAgreement name key value world error keyEq left right ->
  IteratorOutcomeAgreement name key value world error keyEq right left
r39OutcomeAgreementSymmetric IteratorOutcomesUndefined =
  IteratorOutcomesUndefined
r39OutcomeAgreementSymmetric (IteratorFailuresAgree errorsSame) =
  IteratorFailuresAgree (sym errorsSame)
r39OutcomeAgreementSymmetric
  (IteratorSuccessfulYieldsAgree continuationSame undoMaps) =
    IteratorSuccessfulYieldsAgree (sym continuationSame)
      (r39EquivalentMapsSymmetric undoMaps)

||| Landed revision-20 RAR capital is consumed directly below.  The probe no
||| longer shadows the frozen record.
0 r39TransformationOrigin :
  RelationalReplayCorrespondence name key world error value source
    replayed ->
  TraceEffectTransformation name key world error value actor replayed ->
  TraceEffectTransformation name key world error value actor source
r39TransformationOrigin correspondence TraceIdentity = TraceIdentity
r39TransformationOrigin correspondence (TraceGenerator generator) =
  TraceGenerator (replayGeneratorOrigin correspondence actor generator)
r39TransformationOrigin correspondence (TraceCompose after before) =
  TraceCompose (r39TransformationOrigin correspondence after)
    (r39TransformationOrigin correspondence before)

||| Consumer probe for arbitrary monoid transformations, not just one head.
public export
0 r39TransformationMapsRelated :
  (correspondence : RelationalReplayCorrespondence name key world error value
    source replayed) ->
  (transformation : TraceEffectTransformation name key world error value actor
    replayed) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (runTraceEffectTransformation
      (r39TransformationOrigin correspondence transformation))
    (runTraceEffectTransformation transformation)
r39TransformationMapsRelated correspondence TraceIdentity =
  \inputs => PartialDefined inputs
r39TransformationMapsRelated correspondence (TraceGenerator generator) =
  replayGeneratorMapsRelated correspondence keyEq actor generator
r39TransformationMapsRelated correspondence (TraceCompose after before) =
  r39PartialMapsRelatedCompose
    (r39TransformationMapsRelated correspondence after)
    (r39TransformationMapsRelated correspondence before)

public export
0 r39IdentityRelationalReplayCorrespondence :
  (keyEq : DecEq key) ->
  (trace : Transitions first last) ->
  RelationalReplayCorrespondence name key world error value trace trace
r39IdentityRelationalReplayCorrespondence keyEq trace =
  MkRelationalReplayCorrespondence
    (\actor, generator => generator)
    (\observedKeyEq, actor, generator =>
      replayTraceGeneratorMapRespects observedKeyEq generator)
    (\actor, stage => stage)
    (\actor, stage, state => Refl)

public export
0 r39ComposeRelationalReplayCorrespondence :
  {source : Transitions sourceFirst sourceFinal} ->
  {middle : Transitions middleFirst middleFinal} ->
  {target : Transitions targetFirst targetFinal} ->
  RelationalReplayCorrespondence name key world error value source middle ->
  RelationalReplayCorrespondence name key world error value middle target ->
  RelationalReplayCorrespondence name key world error value source target
r39ComposeRelationalReplayCorrespondence = composeRelationalReplayCorrespondence

0 r39StageOutcomesRelatedFromExact :
  (keyEq : DecEq key) ->
  (sourceStage : IteratorStage name key world error value actor source) ->
  (targetStage : IteratorStage name key world error value actor replayed) ->
  ((state : EffectState name key value world) ->
    iteratorStageOutcome targetStage state =
      iteratorStageOutcome sourceStage state) ->
  {sourceInput, targetInput : EffectState name key value world} ->
  EffectStateRelated keyEq sourceInput targetInput ->
  IteratorOutcomeAgreement name key value world error keyEq
    (iteratorStageOutcome sourceStage sourceInput)
    (iteratorStageOutcome targetStage targetInput)
r39StageOutcomesRelatedFromExact keyEq sourceStage targetStage exact inputs =
  replace
    {p = \observed => IteratorOutcomeAgreement name key value world error keyEq
      observed (iteratorStageOutcome targetStage targetInput)}
    (exact sourceInput)
    (iteratorStageOutcomeRelated keyEq targetStage sourceInput targetInput inputs)

0 r39SourceStableAtExactRun :
  (keyEq : DecEq key) ->
  (stage : IteratorStage name key world error value actor trace) ->
  (foreign : PartialEffectMap name key value world) ->
  (origin, moved : EffectState name key value world) ->
  foreign origin = Just moved ->
  IteratorOutcomeStableUnder keyEq stage foreign origin ->
  IteratorOutcomeAgreement name key value world error keyEq
    (iteratorStageOutcome stage moved) (iteratorStageOutcome stage origin)
r39SourceStableAtExactRun keyEq stage foreign origin moved defined stable
  with (foreign origin) proof observed
  r39SourceStableAtExactRun keyEq stage foreign origin moved defined stable |
    Nothing = void (nothingIsNotJust defined)
  r39SourceStableAtExactRun keyEq stage foreign origin moved defined stable |
    Just actual = replace
      {p = \candidate => IteratorOutcomeAgreement name key value world error
        keyEq (iteratorStageOutcome stage candidate)
        (iteratorStageOutcome stage origin)}
      (justInjective defined) stable

0 r39IteratorStableFromRelationalMaps :
  (keyEq : DecEq key) ->
  (sourceStage : IteratorStage name key world error value left source) ->
  (targetStage : IteratorStage name key world error value left replayed) ->
  (sourceForeign, targetForeign : PartialEffectMap name key value world) ->
  PartialMapsRelated (EffectStateEquivalence keyEq) sourceForeign targetForeign ->
  ((origin : EffectState name key value world) ->
    IteratorOutcomeStableUnder keyEq sourceStage sourceForeign origin) ->
  ({sourceInput, targetInput : EffectState name key value world} ->
    EffectStateRelated keyEq sourceInput targetInput ->
    IteratorOutcomeAgreement name key value world error keyEq
      (iteratorStageOutcome sourceStage sourceInput)
      (iteratorStageOutcome targetStage targetInput)) ->
  (origin : EffectState name key value world) ->
  IteratorOutcomeStableUnder keyEq targetStage targetForeign origin
r39IteratorStableFromRelationalMaps keyEq sourceStage targetStage sourceForeign
  targetForeign mapsRelated sourceStable stagesRelated origin
  with (targetForeign origin) proof targetRun
  r39IteratorStableFromRelationalMaps keyEq sourceStage targetStage sourceForeign
    targetForeign mapsRelated sourceStable stagesRelated origin | Nothing = ()
  r39IteratorStableFromRelationalMaps keyEq sourceStage targetStage sourceForeign
    targetForeign mapsRelated sourceStable stagesRelated origin | Just targetMoved
    with (sourceForeign origin) proof sourceRun
    r39IteratorStableFromRelationalMaps keyEq sourceStage targetStage sourceForeign
      targetForeign mapsRelated sourceStable stagesRelated origin |
      Just targetMoved | Nothing =
        case r39PartialRewrite sourceRun targetRun
          (mapsRelated (effectStateReflexive keyEq origin)) of _ impossible
    r39IteratorStableFromRelationalMaps keyEq sourceStage targetStage sourceForeign
      targetForeign mapsRelated sourceStable stagesRelated origin |
      Just targetMoved | Just sourceMoved =
        let 0 movedInputs : EffectStateRelated keyEq sourceMoved targetMoved
            movedInputs = case r39PartialRewrite sourceRun targetRun
              (mapsRelated (effectStateReflexive keyEq origin)) of
                PartialDefined related => related
            0 targetMovedToSourceMoved : IteratorOutcomeAgreement name key value
              world error keyEq (iteratorStageOutcome targetStage targetMoved)
              (iteratorStageOutcome sourceStage sourceMoved)
            targetMovedToSourceMoved = r39OutcomeAgreementSymmetric
              (stagesRelated movedInputs)
            0 sourceMovedToSourceOrigin : IteratorOutcomeAgreement name key value
              world error keyEq (iteratorStageOutcome sourceStage sourceMoved)
              (iteratorStageOutcome sourceStage origin)
            sourceMovedToSourceOrigin = r39SourceStableAtExactRun keyEq
              sourceStage sourceForeign origin sourceMoved sourceRun
              (sourceStable origin)
            0 sourceOriginToTargetOrigin : IteratorOutcomeAgreement name key value
              world error keyEq (iteratorStageOutcome sourceStage origin)
              (iteratorStageOutcome targetStage origin)
            sourceOriginToTargetOrigin = stagesRelated
              (effectStateReflexive keyEq origin)
        in iteratorOutcomeAgreementTransitive targetMovedToSourceMoved
          (iteratorOutcomeAgreementTransitive sourceMovedToSourceOrigin
            sourceOriginToTargetOrigin)

||| Whole-bundle field 9 (`replayIndependent`) closes through the landed
||| revision-20 relational correspondence.
public export
0 r39TraceIndependentAfterRelationalReplay :
  (keyEq : DecEq key) ->
  {source : Transitions sourceFirst sourceFinal} ->
  {replayed : Transitions replayedFirst replayedFinal} ->
  RelationalReplayCorrespondence name key world error value source replayed ->
  TraceIndependent name key world error value keyEq source ->
  TraceIndependent name key world error value keyEq replayed
r39TraceIndependentAfterRelationalReplay =
  traceIndependentAfterRelationalReplaySpike

module DGamma.R28RetainedFinishIndependencePositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R21MovedOutputAlignmentScopingPositive
import DGamma.R23CorrectedInternalFixturePositive
import Decidable.Equality

%default total
%unbound_implicits off

0 r28ActualGeneratorTotal :
  {before, afterState : SystemState Nat R23Key R23Value Unit Unit} ->
  (nameEq : DecEq Nat) -> (keyEq : DecEq R23Key) ->
  (action : Action Nat R23Key R23Value Unit Unit) -> (tag : RuleTag) ->
  (equation : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (occurs : OccursIn (Fired {before = before} {afterState = afterState}
    nameEq keyEq action tag equation) r27WholeTargetTrace) ->
  (state : EffectState Nat R23Key R23Value Unit) ->
  (next : EffectState Nat R23Key R23Value Unit **
    partialEffectMapFor nameEq keyEq action tag before state = Just next)
r28ActualGeneratorTotal = actualMapTotalFromTrace r27ActualMapsTotal

0 r28GeneratorTotal :
  {actor : Nat} ->
  (generator : TraceEffectGenerator Nat R23Key Unit Unit R23Value actor
    r27WholeTargetTrace) ->
  (state : EffectState Nat R23Key R23Value Unit) ->
  (next : EffectState Nat R23Key R23Value Unit **
    traceGeneratorMap generator state = Just next)
r28GeneratorTotal
  (ActualForwardGenerator before afterState nameEq keyEq action tag equation
    occurs actorMatches) state =
      r28ActualGeneratorTotal nameEq keyEq action tag equation occurs state
r28GeneratorTotal (IteratorForwardGenerator stage) state =
  void (r27NoIterator stage)
r28GeneratorTotal (IteratorYieldedGenerator stage origin) state =
  void (r27NoIterator stage)

0 r28TransformationTotal :
  {actor : Nat} ->
  (transformation : TraceEffectTransformation Nat R23Key Unit Unit R23Value
    actor r27WholeTargetTrace) ->
  (state : EffectState Nat R23Key R23Value Unit) ->
  (next : EffectState Nat R23Key R23Value Unit **
    runTraceEffectTransformation transformation state = Just next)
r28TransformationTotal TraceIdentity state = (state ** Refl)
r28TransformationTotal (TraceGenerator generator) state =
  r28GeneratorTotal generator state
r28TransformationTotal (TraceCompose after before) state =
  case r28TransformationTotal before state of
    (middle ** beforeRuns) =>
      case r28TransformationTotal after middle of
        (finalState ** afterRuns) =>
          (finalState ** rewrite beforeRuns in rewrite afterRuns in Refl)

0 r28EmptyKeyContextBindings :
  (context : CoeffectContext R23Key R23Value) -> bindings context = []
r28EmptyKeyContextBindings (MkCoeffectContext [] unique) = Refl
r28EmptyKeyContextBindings (MkCoeffectContext (Bind key value :: rest) unique) =
  case key of _ impossible

0 r28AllEffectStatesRelated :
  (left, right : EffectState Nat R23Key R23Value Unit) ->
  EffectStateRelated r23KeyEq left right
r28AllEffectStatesRelated (MkEffectState () leftTables)
  (MkEffectState () rightTables) = MkEffectStateRelated Refl
    (\selected => trans (r28EmptyKeyContextBindings (leftTables selected))
      (sym (r28EmptyKeyContextBindings (rightTables selected))))

public export
0 r28WholeIndependent : TraceIndependent Nat R23Key Unit Unit R23Value
  r23KeyEq r27WholeTargetTrace
r28WholeIndependent = MkTraceIndependent commute stable
  where
  0 commute :
    (left, right : Nat) -> Not (left = right) ->
    (leftT : TraceEffectTransformation Nat R23Key Unit Unit R23Value left
      r27WholeTargetTrace) ->
    (rightT : TraceEffectTransformation Nat R23Key Unit Unit R23Value right
      r27WholeTargetTrace) ->
    PartialCommute (EffectStateEquivalence r23KeyEq)
      (runTraceEffectTransformation leftT) (runTraceEffectTransformation rightT)
  commute left right distinct leftT rightT state =
    case r28TransformationTotal rightT state of
      (afterRight ** rightRuns) =>
        case r28TransformationTotal leftT afterRight of
          (leftAfterRight ** leftAfterRightRuns) =>
            case r28TransformationTotal leftT state of
              (afterLeft ** leftRuns) =>
                case r28TransformationTotal rightT afterLeft of
                  (rightAfterLeft ** rightAfterLeftRuns) =>
                    rewrite rightRuns in rewrite leftAfterRightRuns in
                    rewrite leftRuns in rewrite rightAfterLeftRuns in
                      PartialDefined
                        (r28AllEffectStatesRelated leftAfterRight rightAfterLeft)

  0 stable :
    (left, right : Nat) -> Not (left = right) ->
    (stage : IteratorStage Nat R23Key Unit Unit R23Value left
      r27WholeTargetTrace) ->
    (foreign : TraceEffectTransformation Nat R23Key Unit Unit R23Value right
      r27WholeTargetTrace) ->
    (origin : EffectState Nat R23Key R23Value Unit) ->
    IteratorOutcomeStableUnder r23KeyEq stage
      (runTraceEffectTransformation foreign) origin
  stable left right distinct stage foreign origin = void (r27NoIterator stage)

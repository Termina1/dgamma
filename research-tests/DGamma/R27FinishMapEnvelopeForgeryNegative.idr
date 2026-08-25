module DGamma.R27FinishMapEnvelopeForgeryNegative

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.R23CorrectedInternalFixturePositive

%default total
%unbound_implicits off

||| A caller-selected proof for the canonical Fired transition cannot populate
||| the retained map field indexed by the replay producer's owned transition.
||| Only r27ProduceMapRetainedFinish may seal this equality before projection.
0 forgeFinishMapEnvelopeFromDetachedCanonicalMap :
  {actor : Nat} ->
  {sourceBefore, sourceAfter, replayedBefore :
    SystemState Nat R23Key R23Value Unit Unit} ->
  {sourceChecked : checkedApplyAction @{r23NameEq} @{r23KeyEq}
    (LAdvance actor) sourceBefore = Just (LFinishTag, sourceAfter)} ->
  (replay : R24CheckedEmptyFinishReplay actor sourceBefore sourceAfter
    replayedBefore sourceChecked) ->
  ((state : EffectState Nat R23Key R23Value Unit) ->
    partialEffectMap
      (Fired {before = replayedBefore} {afterState = replayedAfter replay}
        r23NameEq r23KeyEq (LAdvance actor) LFinishTag
        (replayedChecked replay)) state = Just state) ->
  R27MapRetainedFinishReplay actor sourceBefore sourceAfter replayedBefore
    sourceChecked
forgeFinishMapEnvelopeFromDetachedCanonicalMap replay detachedMap =
  MkR27MapRetainedFinishReplay replay
    (\state => case r25CanonicalTransitionExact replay of
      Refl => detachedMap state)

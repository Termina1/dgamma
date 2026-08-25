module DGamma.R26FinishMapProjectionNegative

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R23CorrectedInternalFixturePositive

%default total
%unbound_implicits off

||| The authenticated replay owns both an exact canonical transition equation
||| and a per-step RAR, but transporting an actual generator across that erased
||| projection does not make its executable map definitionally reduce back to
||| `partialEffectMap (replayedTransition replay)`.  A later independence proof
||| must retain this equality at the producer; it may not identify the stored
||| executable dictionaries after projection.
0 transportedFinishActualMapDoesNotReduce :
  {actor : Nat} ->
  {sourceBefore, sourceAfter, replayedBefore :
    SystemState Nat R23Key R23Value Unit Unit} ->
  {sourceChecked : checkedApplyAction @{r23NameEq} @{r23KeyEq}
    (LAdvance actor) sourceBefore = Just (LFinishTag, sourceAfter)} ->
  (replay : R24CheckedEmptyFinishReplay actor sourceBefore sourceAfter
    replayedBefore sourceChecked) ->
  (state : EffectState Nat R23Key R23Value Unit) ->
  let 0 canonical : Transition replayedBefore (replayedAfter replay)
      canonical = Fired r23NameEq r23KeyEq (LAdvance actor) LFinishTag
        (replayedChecked replay)
      0 canonicalGenerator : TraceEffectGenerator Nat R23Key Unit Unit R23Value
        actor (MoreTransitions canonical NoTransitions)
      canonicalGenerator = ActualForwardGenerator replayedBefore
        (replayedAfter replay) r23NameEq r23KeyEq (LAdvance actor) LFinishTag
        (replayedChecked replay) OccursHere Refl
      0 targetGenerator : TraceEffectGenerator Nat R23Key Unit Unit R23Value actor
        (MoreTransitions (replayedTransition replay) NoTransitions)
      targetGenerator = replace
        {p = \transition => TraceEffectGenerator Nat R23Key Unit Unit R23Value
          actor (MoreTransitions transition NoTransitions)}
        (sym (r25CanonicalTransitionExact replay)) canonicalGenerator
  in traceGeneratorMap targetGenerator state =
    partialEffectMap (replayedTransition replay) state
transportedFinishActualMapDoesNotReduce replay state =
  case r25CanonicalTransitionExact replay of Refl => Refl

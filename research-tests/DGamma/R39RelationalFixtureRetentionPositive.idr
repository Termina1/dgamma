module DGamma.R39RelationalFixtureRetentionPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import DGamma.CP4RecoveryEffectRespect
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R23CorrectedInternalFixturePositive
import DGamma.R28RetainedFinishIndependencePositive
import DGamma.R29RetainedFinishTargetBundlePositive
import DGamma.R39RelationalMapAlgebraPositive
import Decidable.Equality

%default total
%unbound_implicits off

||| Fixture consumers project the landed revision-20 RAR field directly.
public export
0 r39LandedFixtureRARFieldProjects :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {sourceFirst, sourceFinal, replayedFirst, replayedFinal :
    SystemState name key value world error} ->
  {source : Transitions sourceFirst sourceFinal} ->
  {replayed : Transitions replayedFirst replayedFinal} ->
  (correspondence : RelationalReplayCorrespondence name key world error value
    source replayed) ->
  (keyEq : DecEq key) -> (actor : name) ->
  (generator : TraceEffectGenerator name key world error value actor replayed) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (traceGeneratorMap (replayGeneratorOrigin correspondence actor generator))
    (traceGeneratorMap generator)
r39LandedFixtureRARFieldProjects correspondence keyEq actor generator =
  replayGeneratorMapsRelated correspondence keyEq actor generator

0 r39R27TargetMapRespects :
  {actor : Nat} ->
  {sourceBefore, sourceAfter, replayedBefore :
    SystemState Nat R23Key R23Value Unit Unit} ->
  {sourceChecked : checkedApplyAction @{r23NameEq} @{r23KeyEq}
    (LAdvance actor) sourceBefore = Just (LFinishTag, sourceAfter)} ->
  (envelope : R27MapRetainedFinishReplay actor sourceBefore sourceAfter
    replayedBefore sourceChecked) ->
  EffectPartialMapRespects r23KeyEq
    (partialEffectMap (replayedTransition (baseFinishReplay envelope)))
r39R27TargetMapRespects envelope left right inputs =
  r39PartialRewrite
    (sym (retainedTargetMapIdentity envelope left))
    (sym (retainedTargetMapIdentity envelope right))
    (PartialDefined inputs)

||| The R23/R27 fixture's producer-owned exact fields imply the relational
||| candidate.  The source map remains indexed by the fixture's private
||| `r24FinishTransition`; Idris infers it from the projection rather than
||| forging an independently oriented checked transition.
public export
0 r39R23FirstFixtureHeadRelationalMapConstructs : Unit
r39R23FirstFixtureHeadRelationalMapConstructs =
  let 0 relational = r39ExactMapsGivePartialMapsRelated _
        (partialEffectMap
          (replayedTransition (baseFinishReplay r27FirstFinishEnvelope)))
        (r39R27TargetMapRespects r27FirstFinishEnvelope)
        (retainedHeadMapPreserved r27FirstFinishEnvelope)
  in ()

public export
0 r39R23SecondFixtureHeadRelationalMapConstructs : Unit
r39R23SecondFixtureHeadRelationalMapConstructs =
  let 0 relational = r39ExactMapsGivePartialMapsRelated _
        (partialEffectMap
          (replayedTransition (baseFinishReplay r27SecondFinishEnvelope)))
        (r39R27TargetMapRespects r27SecondFinishEnvelope)
        (retainedHeadMapPreserved r27SecondFinishEnvelope)
  in ()

||| R27-style retention needs only existential target definedness for
||| `ActualMapsTotalTrace`; it does not need exact target identity.
public export
0 r39TargetDefinedFromRelatedSource :
  {name, key, world : Type} -> {value : key -> Type} ->
  {keyEq : DecEq key} ->
  (source, target : PartialEffectMap name key value world) ->
  PartialMapsRelated (EffectStateEquivalence keyEq) source target ->
  (state, sourceOutput : EffectState name key value world) ->
  source state = Just sourceOutput ->
  (targetOutput : EffectState name key value world **
    target state = Just targetOutput)
r39TargetDefinedFromRelatedSource source target mapsRelated state sourceOutput
  sourceRun with (target state) proof targetRun
  r39TargetDefinedFromRelatedSource source target mapsRelated state sourceOutput
    sourceRun | Nothing =
      case r39PartialRewrite sourceRun targetRun
        (mapsRelated (effectStateReflexive keyEq state)) of _ impossible
  r39TargetDefinedFromRelatedSource source target mapsRelated state sourceOutput
    sourceRun | Just targetOutput = (targetOutput ** Refl)

||| Generic R27 consumer shape.  A producer supplies only relational head
||| capital plus source totality; the exact existential target-total statement
||| consumed by `ActualMapsTotalStep` follows constructively.
public export
0 r39R27StyleTargetMapTotal :
  {name, key, world : Type} -> {value : key -> Type} ->
  {keyEq : DecEq key} ->
  (source, target : PartialEffectMap name key value world) ->
  PartialMapsRelated (EffectStateEquivalence keyEq) source target ->
  ((state : EffectState name key value world) ->
    (sourceOutput : EffectState name key value world **
      source state = Just sourceOutput)) ->
  (state : EffectState name key value world) ->
  (targetOutput : EffectState name key value world **
    target state = Just targetOutput)
r39R27StyleTargetMapTotal source target related sourceTotal state =
  case sourceTotal state of
    (sourceOutput ** sourceRun) => r39TargetDefinedFromRelatedSource source target
      related state sourceOutput sourceRun

||| The downstream R29 bundle's ninth field remains the same independently
||| checked theorem; only its future replay-transport producer changes.
public export
0 r39R29BundleField9StillAvailable :
  TraceIndependent Nat R23Key Unit Unit R23Value r23KeyEq r27WholeTargetTrace
r39R29BundleField9StillAvailable = r28WholeIndependent

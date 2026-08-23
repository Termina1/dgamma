module DGamma.CP5ConfluenceLocalDiamondSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Core
import DGamma.Unified
import DGamma.CP3
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4Support
import Data.Nat
import Decidable.Equality

%default total

||| Exactly the three paper-Lemma-71 activation rules.  The host collapses
||| L-Iter and L-Finish into the action LAdvance and distinguishes them by tag.
public export
data PaperActivationStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> Type where
  PaperBeginStep :
    transitionAction transition = LBegin actor ->
    transitionTag transition = LBeginTag ->
    PaperActivationStep transition
  PaperIterStep :
    transitionAction transition = LAdvance actor ->
    transitionTag transition = LIterTag ->
    PaperActivationStep transition
  PaperFinishStep :
    transitionAction transition = LAdvance actor ->
    transitionTag transition = LFinishTag ->
    PaperActivationStep transition

||| The three explicit host orchestration rules.
public export
data PaperOrchestrationStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> Type where
  PaperInsertStep :
    transitionAction transition = OInsert actor parent component ->
    PaperOrchestrationStep transition
  PaperRetireStep :
    transitionAction transition = ORetire actor ->
    PaperOrchestrationStep transition
  PaperRemoveStep :
    transitionAction transition = ORemove actor ->
    PaperOrchestrationStep transition

||| A reusable RAR correspondence, not a deletion-only embedding.  Every actual
||| or yielded generator and every iterator stage of the replayed trace is tied
||| to one generator/stage in the source trace with the same executable map or
||| outcome.  This is the exact capital needed to transport both fields of
||| `TraceIndependent` after deletion, suffix replay, and adjacent swaps.
public export
record RelationalReplayCorrespondence
  (name, key, world, error : Type) (value : key -> Type)
  {sourceFirst, sourceFinal, replayedFirst, replayedFinal :
    SystemState name key value world error}
  (source : Transitions sourceFirst sourceFinal)
  (replayed : Transitions replayedFirst replayedFinal) where
  constructor MkRelationalReplayCorrespondence
  replayGeneratorOrigin : (actor : name) ->
    TraceEffectGenerator name key world error value actor replayed ->
    TraceEffectGenerator name key world error value actor source
  0 replayGeneratorMapPreserved : (actor : name) ->
    (generator : TraceEffectGenerator name key world error value actor replayed) ->
    (state : EffectState name key value world) ->
    traceGeneratorMap (replayGeneratorOrigin actor generator) state =
      traceGeneratorMap generator state
  replayIteratorStageOrigin : (actor : name) ->
    IteratorStage name key world error value actor replayed ->
    IteratorStage name key world error value actor source
  0 replayIteratorOutcomePreserved : (actor : name) ->
    (stage : IteratorStage name key world error value actor replayed) ->
    (state : EffectState name key value world) ->
    iteratorStageOutcome stage state =
      iteratorStageOutcome (replayIteratorStageOrigin actor stage) state

0 replayTransformationOrigin :
  {source : Transitions sourceFirst sourceFinal} ->
  {replayed : Transitions replayedFirst replayedFinal} ->
  RelationalReplayCorrespondence name key world error value source replayed ->
  TraceEffectTransformation name key world error value actor replayed ->
  TraceEffectTransformation name key world error value actor source
replayTransformationOrigin correspondence TraceIdentity = TraceIdentity
replayTransformationOrigin correspondence (TraceGenerator generator) =
  TraceGenerator (replayGeneratorOrigin correspondence actor generator)
replayTransformationOrigin correspondence (TraceCompose after before) =
  TraceCompose (replayTransformationOrigin correspondence after)
    (replayTransformationOrigin correspondence before)

0 replayTransformationMapPreserved :
  {source : Transitions sourceFirst sourceFinal} ->
  {replayed : Transitions replayedFirst replayedFinal} ->
  (correspondence : RelationalReplayCorrespondence name key world error value
    source replayed) ->
  (transformation : TraceEffectTransformation name key world error value actor
    replayed) ->
  (state : EffectState name key value world) ->
  runTraceEffectTransformation
    (replayTransformationOrigin correspondence transformation) state =
  runTraceEffectTransformation transformation state
replayTransformationMapPreserved correspondence TraceIdentity state = Refl
replayTransformationMapPreserved correspondence (TraceGenerator generator) state =
  replayGeneratorMapPreserved correspondence actor generator state
replayTransformationMapPreserved correspondence (TraceCompose after before) state
  with (runTraceEffectTransformation
    (replayTransformationOrigin correspondence before) state) proof sourceRun
  replayTransformationMapPreserved correspondence (TraceCompose after before)
    state | Nothing =
      let targetRun = trans
            (sym (replayTransformationMapPreserved correspondence before state))
            sourceRun
      in rewrite targetRun in Refl
  replayTransformationMapPreserved correspondence (TraceCompose after before)
    state | Just middle =
      let targetRun = trans
            (sym (replayTransformationMapPreserved correspondence before state))
            sourceRun
      in rewrite targetRun in
        replayTransformationMapPreserved correspondence after middle

0 replayPartialComposeCong :
  (leftSource, leftTarget, rightSource, rightTarget :
    PartialEffectMap name key value world) ->
  ((state : EffectState name key value world) ->
    leftSource state = leftTarget state) ->
  ((state : EffectState name key value world) ->
    rightSource state = rightTarget state) ->
  (state : EffectState name key value world) ->
  partialCompose leftSource rightSource state =
    partialCompose leftTarget rightTarget state
replayPartialComposeCong leftSource leftTarget rightSource rightTarget leftSame
  rightSame state with (rightSource state) proof sourceRun
  replayPartialComposeCong leftSource leftTarget rightSource rightTarget leftSame
    rightSame state | Nothing =
      rewrite sym (rightSame state) in rewrite sourceRun in Refl
  replayPartialComposeCong leftSource leftTarget rightSource rightTarget leftSame
    rightSame state | Just middle =
      rewrite sym (rightSame state) in rewrite sourceRun in leftSame middle

0 replayPartialCommuteTransport :
  (leftSource, leftTarget, rightSource, rightTarget :
    PartialEffectMap name key value world) ->
  ((state : EffectState name key value world) ->
    leftSource state = leftTarget state) ->
  ((state : EffectState name key value world) ->
    rightSource state = rightTarget state) ->
  PartialCommute (EffectStateEquivalence keyEq) leftSource rightSource ->
  PartialCommute (EffectStateEquivalence keyEq) leftTarget rightTarget
replayPartialCommuteTransport leftSource leftTarget rightSource rightTarget
  leftSame rightSame commute state =
    let leftThenRight = replayPartialComposeCong leftSource leftTarget rightSource
          rightTarget leftSame rightSame state
        rightThenLeft = replayPartialComposeCong rightSource rightTarget leftSource
          leftTarget rightSame leftSame state
        relatedSource = commute state
        relatedRight = replace
          {p = \observed => PartialRelated (EffectState name key value world)
            (EffectStateRelated keyEq)
            (partialCompose leftSource rightSource state) observed}
          rightThenLeft relatedSource
    in replace
      {p = \observed => PartialRelated (EffectState name key value world)
        (EffectStateRelated keyEq) observed
        (partialCompose rightTarget leftTarget state)}
      leftThenRight relatedRight

0 replayOutcomeStableAtExactRun :
  (stage : IteratorStage name key world error value actor trace) ->
  (foreign : PartialEffectMap name key value world) ->
  (origin, moved : EffectState name key value world) ->
  foreign origin = Just moved ->
  IteratorOutcomeStableUnder keyEq stage foreign origin ->
  IteratorOutcomeAgreement name key value world error keyEq
    (iteratorStageOutcome stage moved) (iteratorStageOutcome stage origin)
replayOutcomeStableAtExactRun stage foreign origin moved defined stable
  with (foreign origin) proof observed
  replayOutcomeStableAtExactRun stage foreign origin moved defined stable |
    Nothing = void (nothingIsNotJust defined)
  replayOutcomeStableAtExactRun stage foreign origin moved defined stable |
    Just actual =
      replace
        {p = \candidate => IteratorOutcomeAgreement name key value world error
          keyEq (iteratorStageOutcome stage candidate)
          (iteratorStageOutcome stage origin)}
        (justInjective defined) stable

0 replayIteratorStable :
  {source : Transitions sourceFirst sourceFinal} ->
  {replayed : Transitions replayedFirst replayedFinal} ->
  (correspondence : RelationalReplayCorrespondence name key world error value
    source replayed) ->
  TraceIndependent name key world error value keyEq source ->
  (left, right : name) -> Not (left = right) ->
  (stage : IteratorStage name key world error value left replayed) ->
  (foreign : TraceEffectTransformation name key world error value right
    replayed) ->
  (origin : EffectState name key value world) ->
  IteratorOutcomeStableUnder keyEq stage
    (runTraceEffectTransformation foreign) origin
replayIteratorStable correspondence independent left right distinct stage foreign
  origin with (runTraceEffectTransformation foreign origin) proof targetRun
  replayIteratorStable correspondence independent left right distinct stage
    foreign origin | Nothing = ()
  replayIteratorStable correspondence independent left right distinct stage
    foreign origin | Just moved =
      let sourceRun : (runTraceEffectTransformation
            (replayTransformationOrigin correspondence foreign) origin =
              Just moved)
          sourceRun = trans
            (replayTransformationMapPreserved correspondence foreign origin)
            targetRun
          0 sourceStable : IteratorOutcomeStableUnder keyEq (replayIteratorStageOrigin correspondence left stage)
            (runTraceEffectTransformation
              (replayTransformationOrigin correspondence foreign)) origin
          sourceStable = iteratorYieldsStable independent left right distinct
            (replayIteratorStageOrigin correspondence left stage) (replayTransformationOrigin correspondence foreign) origin
          0 sourceAgreement : IteratorOutcomeAgreement name key value world error
            keyEq (iteratorStageOutcome (replayIteratorStageOrigin correspondence left stage) moved)
              (iteratorStageOutcome (replayIteratorStageOrigin correspondence left stage) origin)
          sourceAgreement = replayOutcomeStableAtExactRun (replayIteratorStageOrigin correspondence left stage)
            (runTraceEffectTransformation
              (replayTransformationOrigin correspondence foreign))
            origin moved sourceRun sourceStable
          0 originAdjusted : IteratorOutcomeAgreement name key value world error
            keyEq (iteratorStageOutcome (replayIteratorStageOrigin correspondence left stage) moved)
              (iteratorStageOutcome stage origin)
          originAdjusted = replace
            {p = \outcome => IteratorOutcomeAgreement name key value world error
              keyEq (iteratorStageOutcome (replayIteratorStageOrigin correspondence left stage) moved) outcome}
            (sym (replayIteratorOutcomePreserved correspondence left stage origin))
            sourceAgreement
      in replace
        {p = \outcome => IteratorOutcomeAgreement name key value world error
          keyEq outcome (iteratorStageOutcome stage origin)}
        (sym (replayIteratorOutcomePreserved correspondence left stage moved))
        originAdjusted

||| Generic independence transport.  Deletion and sorting must construct the
||| correspondence above as part of their internal replay result; this theorem
||| deliberately does not claim that an arbitrary public `DeletionResult`
||| contains enough evidence by itself.
public export
0 traceIndependentAfterRelationalReplaySpike :
  (keyEq : DecEq key) ->
  {source : Transitions sourceFirst sourceFinal} ->
  {replayed : Transitions replayedFirst replayedFinal} ->
  RelationalReplayCorrespondence name key world error value source replayed ->
  TraceIndependent name key world error value keyEq source ->
  TraceIndependent name key world error value keyEq replayed
traceIndependentAfterRelationalReplaySpike keyEq correspondence independent =
  MkTraceIndependent
    (\left, right, distinct, leftTransformation, rightTransformation =>
      replayPartialCommuteTransport
        (runTraceEffectTransformation
          (replayTransformationOrigin correspondence leftTransformation))
        (runTraceEffectTransformation leftTransformation)
        (runTraceEffectTransformation
          (replayTransformationOrigin correspondence rightTransformation))
        (runTraceEffectTransformation rightTransformation)
        (replayTransformationMapPreserved correspondence leftTransformation)
        (replayTransformationMapPreserved correspondence rightTransformation)
        (generatedMonoidsCommute independent left right distinct
          (replayTransformationOrigin correspondence leftTransformation)
          (replayTransformationOrigin correspondence rightTransformation)))
    (replayIteratorStable correspondence independent)

||| Replay correspondence composes structurally.  This checked helper is the
||| one-trace bridge from original→closing-free and closing-free→sorted replay;
||| it is kept transparent rather than assumed by an opaque schedule producer.
public export
composeRelationalReplayCorrespondence :
  {source : Transitions sourceFirst sourceFinal} ->
  {middle : Transitions middleFirst middleFinal} ->
  {target : Transitions targetFirst targetFinal} ->
  RelationalReplayCorrespondence name key world error value source middle ->
  RelationalReplayCorrespondence name key world error value middle target ->
  RelationalReplayCorrespondence name key world error value source target
composeRelationalReplayCorrespondence left right =
  MkRelationalReplayCorrespondence
    (\actor, generator => replayGeneratorOrigin left actor
      (replayGeneratorOrigin right actor generator))
    (\actor, generator, state => trans
      (replayGeneratorMapPreserved left actor
        (replayGeneratorOrigin right actor generator) state)
      (replayGeneratorMapPreserved right actor generator state))
    (\actor, stage => replayIteratorStageOrigin left actor
      (replayIteratorStageOrigin right actor stage))
    (\actor, stage, state => trans
      (replayIteratorOutcomePreserved right actor stage state)
      (replayIteratorOutcomePreserved left actor
        (replayIteratorStageOrigin right actor stage) state))

||| Registration generations need their own permutation when transitions are
||| swapped: the raw O-Insert action is preserved, but its global birth ordinal
||| may move.  This composition is deliberately local to operational replay so
||| it cannot be confused with the accepted left-to-right generation bijection.
public export
composeReplayGenerationBijection : RegistrationGenerationBijection name ->
  RegistrationGenerationBijection name -> RegistrationGenerationBijection name
composeReplayGenerationBijection left right =
  MkRegistrationGenerationBijection
    (generationForward right . generationForward left)
    (generationBackward left . generationBackward right)
    (\generation => trans
      (cong (generationBackward left)
        (generationLeftInverse right (generationForward left generation)))
      (generationLeftInverse left generation))
    (\generation => trans
      (cong (generationForward right)
        (generationRightInverse left (generationBackward right generation)))
      (generationRightInverse right generation))

||| Convert the specialized generated-registration occurrence to the exact
||| all-action occurrence used by the general replay map.  Both views retain the
||| same dependent prefix, transition, suffix, action, and decomposition.
public export
0 generatedRegistrationActionOccurrence :
  LocatedGeneratedRegistration child parent component trace ->
  LocatedActionOccurrence (OInsert child (ChildOf parent) component) trace
generatedRegistrationActionOccurrence occurrence =
  MkLocatedActionOccurrence
    (registrationBefore occurrence)
    (registrationAfter occurrence)
    (beforeRegistration occurrence)
    (registrationTransition occurrence)
    (afterRegistration occurrence)
    (registrationAction occurrence)
    (registrationDecomposition occurrence)

||| Exact transition-occurrence capital retained by operational permutation.
||| Generated registrations are not an independently replaceable second map:
||| their specialized origin must convert to exactly the all-action origin of
||| the same replayed O-Insert occurrence.
public export
record ActionRegistrationReplayCorrespondence
  (name, key, world, error : Type) (value : key -> Type)
  {sourceFirst, sourceFinal, replayedFirst, replayedFinal :
    SystemState name key value world error}
  (source : Transitions sourceFirst sourceFinal)
  (replayed : Transitions replayedFirst replayedFinal) where
  constructor MkActionRegistrationReplayCorrespondence
  replayGenerationRenaming : RegistrationGenerationBijection name
  replayActionOrigin : {action : Action name key value world error} ->
    LocatedActionOccurrence action replayed -> LocatedActionOccurrence action source
  0 replayActionTagPreserved :
    {action : Action name key value world error} ->
    (occurrence : LocatedActionOccurrence action replayed) ->
    transitionTag (locatedTransition (replayActionOrigin occurrence)) =
      transitionTag (locatedTransition occurrence)
  replayGeneratedRegistrationOrigin :
    {child, parent : name} ->
    {component : Component key value world error} ->
    LocatedGeneratedRegistration child parent component replayed ->
    LocatedGeneratedRegistration child parent component source
  0 replayGeneratedActionOriginCoherent :
    {child, parent : name} ->
    {component : Component key value world error} ->
    (occurrence : LocatedGeneratedRegistration child parent component replayed) ->
    generatedRegistrationActionOccurrence
      (replayGeneratedRegistrationOrigin occurrence) =
    replayActionOrigin (generatedRegistrationActionOccurrence occurrence)
  0 replayGeneratedOrdinalPreserved :
    {child, parent : name} ->
    {component : Component key value world error} ->
    (occurrence : LocatedGeneratedRegistration child parent component replayed) ->
    generationForward replayGenerationRenaming
      (registrationGeneration (replayGeneratedRegistrationOrigin occurrence)) =
        registrationGeneration occurrence

public export
identityActionRegistrationReplayCorrespondence :
  (trace : Transitions initial finalState) ->
  ActionRegistrationReplayCorrespondence name key world error value trace trace
identityActionRegistrationReplayCorrespondence trace =
  MkActionRegistrationReplayCorrespondence
    identityRegistrationGenerationBijection id (\occurrence => Refl) id
    (\occurrence => Refl) (\occurrence => Refl)

||| Occurrence capital composes in the same direction as trace replay.  The
||| ordinal equation explicitly uses the composed replay-generation bijection.
public export
composeActionRegistrationReplayCorrespondence :
  {source : Transitions sourceFirst sourceFinal} ->
  {middle : Transitions middleFirst middleFinal} ->
  {target : Transitions targetFirst targetFinal} ->
  ActionRegistrationReplayCorrespondence name key world error value source middle ->
  ActionRegistrationReplayCorrespondence name key world error value middle target ->
  ActionRegistrationReplayCorrespondence name key world error value source target
composeActionRegistrationReplayCorrespondence left right =
  MkActionRegistrationReplayCorrespondence
    (composeReplayGenerationBijection (replayGenerationRenaming left)
      (replayGenerationRenaming right))
    (\occurrence => replayActionOrigin left (replayActionOrigin right occurrence))
    (\occurrence => trans
      (replayActionTagPreserved left (replayActionOrigin right occurrence))
      (replayActionTagPreserved right occurrence))
    (\occurrence => replayGeneratedRegistrationOrigin left
      (replayGeneratedRegistrationOrigin right occurrence))
    (\occurrence => trans
      (replayGeneratedActionOriginCoherent left
        (replayGeneratedRegistrationOrigin right occurrence))
      (cong (replayActionOrigin left)
        (replayGeneratedActionOriginCoherent right occurrence)))
    (\occurrence => trans
      (cong (generationForward (replayGenerationRenaming right))
        (replayGeneratedOrdinalPreserved left
          (replayGeneratedRegistrationOrigin right occurrence)))
      (replayGeneratedOrdinalPreserved right occurrence))

||| Every premise consumed again by deletion selection, Lemmas 68/70, or the
||| next adjacent swap.  Using one shared record prevents the sorting and
||| deletion recursions from silently dropping capital at their boundaries.
public export
record ReplayInvariantBundle
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkReplayInvariantBundle
  0 replayAligned : AlignedTransitions name key world error value nameEq keyEq trace
  0 replayDiscipline : RegistrationDiscipline protocol nameEq trace
  0 replayInitialWellFormed :
    registryWellFormed @{nameEq} @{keyEq} initial = True
  0 replayInitialEmpty : bindings (registry initial) = []
  0 replayFinalWellFormed :
    registryWellFormed @{nameEq} @{keyEq} finalState = True
  0 replayQuiet : quiet @{nameEq} @{keyEq} finalState = True
  0 replayNoFailure : noFailedFibers finalState = True
  0 replayTotal : TraceComponentsTotal nameEq keyEq trace
  0 replayIndependent : TraceIndependent name key world error value keyEq trace
  0 replayProvenance : RegistrationProvenance protocol nameEq trace
  0 replayProtocolRanked : RegistryProtocolRanked protocol nameEq finalState
  0 replayParentRanksIncrease :
    RegistryParentRanksIncrease protocol nameEq finalState
  0 replayPrecedenceAcyclic : PrecedenceAcyclic nameEq finalState
  0 replaySupportWellFounded : SupportWellFounded nameEq finalState
  0 replaySupportMatchesActive : SupportMatchesActive nameEq keyEq finalState

||| The exact `ReachedFromEmpty` value consumed by Lemmas 68 and 70 is
||| definitionally reconstructed from each recursive bundle, rather than being
||| mentioned only in prose.
public export
0 replayReachedFromEmpty :
  {trace : Transitions initial finalState} ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq trace ->
  ReachedFromEmpty name key world error value nameEq keyEq finalState
replayReachedFromEmpty premises =
  MkReachedFromEmpty initial trace (replayAligned premises)
    (replayInitialEmpty premises) (replayInitialWellFormed premises)

||| Endpoint quotient carried by every suffix replay.  It is strong enough to
||| compose effects and ordered controls without demanding equality of
||| function-valued tables or accumulators.
public export
record RelationalReplayEndpoint
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (sourceFinal, replayedFinal : SystemState name key value world error) where
  constructor MkRelationalReplayEndpoint
  0 replayedEffects : EffectStateRelated keyEq
    (projectEffectState @{nameEq} sourceFinal)
    (projectEffectState @{nameEq} replayedFinal)
  0 replayedControls : OrderedRegistryControlsRelated name key world error value
    (bindings (registry sourceFinal)) (bindings (registry replayedFinal))
  0 replayedWellFormed :
    registryWellFormed @{nameEq} @{keyEq} replayedFinal = True

||| Quotient adequacy must compose through an arbitrary number of adjacent
||| swaps; endpoint relations are therefore explicit algebra rather than an
||| unstated appeal to equality.
public export
0 relationalReplayEndpointReflexiveSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} state = True ->
  RelationalReplayEndpoint name key world error value nameEq keyEq state state
relationalReplayEndpointReflexiveSpike nameEq keyEq state wellFormed =
  MkRelationalReplayEndpoint
    (effectStateReflexive keyEq (projectEffectState @{nameEq} state))
    (orderedControlsReflexive (bindings (registry state)))
    wellFormed

public export
0 relationalReplayEndpointTransitiveSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (left, middle, right : SystemState name key value world error) ->
  RelationalReplayEndpoint name key world error value nameEq keyEq left middle ->
  RelationalReplayEndpoint name key world error value nameEq keyEq middle right ->
  RelationalReplayEndpoint name key world error value nameEq keyEq left right
relationalReplayEndpointTransitiveSpike nameEq keyEq left middle right
  (MkRelationalReplayEndpoint firstEffects firstControls middleWellFormed)
  (MkRelationalReplayEndpoint secondEffects secondControls rightWellFormed) =
    MkRelationalReplayEndpoint
      (effectsTransitive firstEffects secondEffects)
      (controlsTransitive firstControls secondControls)
      rightWellFormed
  where
  0 effectsTransitive :
    EffectStateRelated keyEq leftEffect middleEffect ->
    EffectStateRelated keyEq middleEffect rightEffect ->
    EffectStateRelated keyEq leftEffect rightEffect
  effectsTransitive
    (MkEffectStateRelated firstAmbient firstTables)
    (MkEffectStateRelated secondAmbient secondTables) =
      MkEffectStateRelated (trans firstAmbient secondAmbient)
        (\actor => trans (firstTables actor) (secondTables actor))

  0 controlsTransitive :
    OrderedRegistryControlsRelated name key world error value leftEntries
      middleEntries ->
    OrderedRegistryControlsRelated name key world error value middleEntries
      rightEntries ->
    OrderedRegistryControlsRelated name key world error value leftEntries
      rightEntries
  controlsTransitive OrderedControlsNil OrderedControlsNil = OrderedControlsNil
  controlsTransitive
    (OrderedControlsCons actor first firstRest)
    (OrderedControlsCons actor second secondRest) =
      OrderedControlsCons actor (fiberControlTransitive first second)
        (controlsTransitive firstRest secondRest)

||| Relational local diamond suitable for splicing by replay.  Action and tag
||| equalities are both explicit: L-Iter and L-Finish share LAdvance, so action
||| equality alone cannot recover a located paper activation step.
public export
record LocalRelationalDiamond
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {first, middle, originalFinal : SystemState name key value world error}
  (left : Transition first middle)
  (right : Transition middle originalFinal) where
  constructor MkLocalRelationalDiamond
  swappedMiddle : SystemState name key value world error
  swappedFinal : SystemState name key value world error
  movedRight : Transition first swappedMiddle
  movedLeft : Transition swappedMiddle swappedFinal
  0 movedRightAction : transitionAction movedRight = transitionAction right
  0 movedRightTag : transitionTag movedRight = transitionTag right
  0 movedLeftAction : transitionAction movedLeft = transitionAction left
  0 movedLeftTag : transitionTag movedLeft = transitionTag left
  0 movedRightActivationBranch :
    PaperActivationStep right -> PaperActivationStep movedRight
  0 movedLeftActivationBranch :
    PaperActivationStep left -> PaperActivationStep movedLeft
  0 movedRightOrchestrationBranch :
    PaperOrchestrationStep right -> PaperOrchestrationStep movedRight
  0 movedLeftOrchestrationBranch :
    PaperOrchestrationStep left -> PaperOrchestrationStep movedLeft
  0 swappedEffects : EffectStateRelated keyEq
    (projectEffectState @{nameEq} originalFinal)
    (projectEffectState @{nameEq} swappedFinal)
  0 swappedControls : OrderedRegistryControlsRelated name key world error value
    (bindings (registry originalFinal)) (bindings (registry swappedFinal))
  0 swappedWellFormed : registryWellFormed @{nameEq} @{keyEq} swappedFinal = True

||| Source-sensitive evidence for swapping two orchestration rules.  The early
||| checked transition proves the moved rule's freshness/applicability at the
||| source.  Registration discipline plus the generation scan retain exact
||| birth ordinals/parent-local positions; the negative fields prevent two
||| yielded insertions from crossing their own licensing births.
public export
record OrchestrationSwapSafety
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {first, middle, originalFinal : SystemState name key value world error}
  (left : Transition first middle)
  (right : Transition middle originalFinal) where
  constructor MkOrchestrationSwapSafety
  earlyRightFinal : SystemState name key value world error
  earlyRight : Transition first earlyRightFinal
  0 earlyRightAction : transitionAction earlyRight = transitionAction right
  0 earlyRightTag : transitionTag earlyRight = transitionTag right
  0 sourceRegistrationDiscipline : RegistrationDiscipline protocol nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
  sourceStartOrdinal : Nat
  sourceStartLive : GenerationEnvironment name
  sourceEndOrdinal : Nat
  sourceEndLive : GenerationEnvironment name
  0 sourceGenerationScan : GenerationTraceScan nameEq sourceStartOrdinal
    sourceStartLive (MoreTransitions left (MoreTransitions right NoTransitions))
    sourceEndOrdinal sourceEndLive
  0 insertedChildrenDistinct :
    (leftChild, rightChild : name) ->
    (leftParent, rightParent : Parent name) ->
    (leftComponent, rightComponent : Component key value world error) ->
    transitionAction left = OInsert leftChild leftParent leftComponent ->
    transitionAction right = OInsert rightChild rightParent rightComponent ->
    Not (leftChild = rightChild)
  0 generatedLicensesDoNotCross :
    (leftChild, leftParent, rightChild, rightParent : name) ->
    (leftComponent, rightComponent : Component key value world error) ->
    transitionAction left = OInsert leftChild (ChildOf leftParent) leftComponent ->
    transitionAction right = OInsert rightChild (ChildOf rightParent) rightComponent ->
    (Not (leftChild = rightParent), Not (rightChild = leftParent))

||| Locate the first transition after an exact prefixTrace decomposition.  The
||| operational occurrence fold below uses this constructor for the moved-right
||| node rather than accepting a caller-selected occurrence.
public export
0 locatedFirstAfterPrefix :
  {initial, pairFirst, pairMiddle, finalState :
    SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (prefixTrace : Transitions initial pairFirst) ->
  (first : Transition pairFirst pairMiddle) ->
  (rest : Transitions pairMiddle finalState) ->
  appendTransitions prefixTrace (MoreTransitions first rest) = global ->
  LocatedActionOccurrence (transitionAction first) global
locatedFirstAfterPrefix global prefixTrace first rest decomposition =
  MkLocatedActionOccurrence _ _ prefixTrace first rest Refl decomposition

||| Locate the second transition after an exact prefixTrace decomposition.
public export
0 locatedSecondAfterPrefix :
  {initial, pairFirst, pairMiddle, pairFinal, finalState :
    SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (prefixTrace : Transitions initial pairFirst) ->
  (first : Transition pairFirst pairMiddle) ->
  (second : Transition pairMiddle pairFinal) ->
  (rest : Transitions pairFinal finalState) ->
  appendTransitions prefixTrace
    (MoreTransitions first (MoreTransitions second rest)) = global ->
  LocatedActionOccurrence (transitionAction second) global
locatedSecondAfterPrefix global prefixTrace first second rest decomposition =
  MkLocatedActionOccurrence _ _
    (appendTransitions prefixTrace (MoreTransitions first NoTransitions)) second rest
    Refl
    (trans (appendTransitionsAssociative prefixTrace
      (MoreTransitions first NoTransitions) (MoreTransitions second rest))
      decomposition)

||| Exhaustive ordinal semantics of one adjacent transposition.  Prefix and
||| suffix occurrences retain their absolute ordinal; moved-right and moved-left
||| exchange the two adjacent source ordinals.
public export
data AdjacentSwapOrdinalRelation :
  (prefixCount, targetOrdinal, sourceOrdinal : Nat) -> Type where
  AdjacentPrefixOrdinal : LT targetOrdinal prefixCount ->
    AdjacentSwapOrdinalRelation prefixCount targetOrdinal targetOrdinal
  AdjacentMovedRightOrdinal :
    AdjacentSwapOrdinalRelation prefixCount prefixCount (S prefixCount)
  AdjacentMovedLeftOrdinal :
    AdjacentSwapOrdinalRelation prefixCount (S prefixCount) prefixCount
  AdjacentSuffixOrdinal : LTE (S (S prefixCount)) targetOrdinal ->
    AdjacentSwapOrdinalRelation prefixCount targetOrdinal targetOrdinal

||| The four regions cover every target ordinal.  This executable classifier is
||| independent of occurrence actions/tags, so repeated identical Iter nodes do
||| not create an unclassified case.
public export
adjacentSwapOrdinalExhaustive : (prefixCount, targetOrdinal : Nat) ->
  (sourceOrdinal : Nat **
    AdjacentSwapOrdinalRelation prefixCount targetOrdinal sourceOrdinal)
adjacentSwapOrdinalExhaustive Z Z =
  (S Z ** AdjacentMovedRightOrdinal)
adjacentSwapOrdinalExhaustive Z (S Z) =
  (Z ** AdjacentMovedLeftOrdinal)
adjacentSwapOrdinalExhaustive Z (S (S later)) =
  (S (S later) ** AdjacentSuffixOrdinal (LTESucc (LTESucc LTEZero)))
adjacentSwapOrdinalExhaustive (S prefixCount) Z =
  (Z ** AdjacentPrefixOrdinal (LTESucc LTEZero))
adjacentSwapOrdinalExhaustive (S prefixCount) (S targetOrdinal) =
  case adjacentSwapOrdinalExhaustive prefixCount targetOrdinal of
    (_ ** AdjacentPrefixOrdinal before) =>
      (S targetOrdinal ** AdjacentPrefixOrdinal (LTESucc before))
    (_ ** AdjacentMovedRightOrdinal) =>
      (S (S prefixCount) ** AdjacentMovedRightOrdinal)
    (_ ** AdjacentMovedLeftOrdinal) =>
      (S prefixCount ** AdjacentMovedLeftOrdinal)
    (_ ** AdjacentSuffixOrdinal after) =>
      (S targetOrdinal ** AdjacentSuffixOrdinal (LTESucc after))

public export
0 adjacentTwoSuccNotLTE : LTE (S (S n)) n -> Void
adjacentTwoSuccNotLTE {n = Z} LTEZero impossible
adjacentTwoSuccNotLTE {n = S later} (LTESucc before) =
  adjacentTwoSuccNotLTE before

public export
0 adjacentSeparatedBoundsImpossible :
  LTE (S (S upper)) lower -> LTE (S lower) upper -> Void
adjacentSeparatedBoundsImpossible {upper = Z} after LTEZero impossible
adjacentSeparatedBoundsImpossible {upper = S upper} {lower = Z}
  LTEZero before impossible
adjacentSeparatedBoundsImpossible {upper = S upper} {lower = S lower}
  (LTESucc after) (LTESucc before) =
    adjacentSeparatedBoundsImpossible after before

||| Pairwise arithmetic disjointness of the four regions.
public export
0 adjacentPrefixNotMovedRight : LT prefixCount prefixCount -> Void
adjacentPrefixNotMovedRight = succNotLTEpred

public export
0 adjacentPrefixNotMovedLeft : LT (S prefixCount) prefixCount -> Void
adjacentPrefixNotMovedLeft = adjacentTwoSuccNotLTE

public export
0 adjacentPrefixNotSuffix :
  LT targetOrdinal prefixCount ->
  LTE (S (S prefixCount)) targetOrdinal -> Void
adjacentPrefixNotSuffix before after =
  adjacentSeparatedBoundsImpossible after before

public export
0 adjacentMovedRightNotSuffix : LTE (S (S prefixCount)) prefixCount -> Void
adjacentMovedRightNotSuffix = adjacentTwoSuccNotLTE

public export
0 adjacentMovedLeftNotSuffix : LTE (S (S prefixCount)) (S prefixCount) -> Void
adjacentMovedLeftNotSuffix = succNotLTEpred

||| First-source authenticity for one adjacent swap.  The occurrence map is
||| produced by one globally fixed suffix-replay fold, and every target
||| occurrence—prefix, moved pair, or suffix—must satisfy the exhaustive ordinal
||| relation above.
public export
record AdjacentSwapOperationalOccurrenceFold
  (name, key, world, error : Type) (value : key -> Type)
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal, swappedMiddle,
    swappedFinal, replayedFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (prefixTrace : Transitions initial pairFirst)
  (left : Transition pairFirst pairMiddle)
  (right : Transition pairMiddle pairFinal)
  (suffix : Transitions pairFinal originalFinal)
  (movedRight : Transition pairFirst swappedMiddle)
  (movedLeft : Transition swappedMiddle swappedFinal)
  (replayedSuffix : Transitions swappedFinal replayedFinal)
  (swappedTrace : Transitions initial replayedFinal) where
  constructor MkAdjacentSwapOperationalOccurrenceFold
  operationalOriginalDecomposition : appendTransitions prefixTrace
    (MoreTransitions left (MoreTransitions right suffix)) = original
  operationalSwappedDecomposition : appendTransitions prefixTrace
    (MoreTransitions movedRight (MoreTransitions movedLeft replayedSuffix)) =
      swappedTrace
  operationalOccurrenceCorrespondence : ActionRegistrationReplayCorrespondence
    name key world error value original swappedTrace
  0 operationalOrdinalRelation :
    {action : Action name key value world error} ->
    (occurrence : LocatedActionOccurrence action swappedTrace) ->
    AdjacentSwapOrdinalRelation (transitionCount prefixTrace)
      (locatedActionOrdinal occurrence)
      (locatedActionOrdinal
        (replayActionOrigin operationalOccurrenceCorrespondence occurrence))

||| O6's explicit suffix-replay fold signature.  The body is deliberately the
||| named proof obligation, but callers cannot substitute another coherent map:
||| `AdjacentSwapResult` projects only this globally fixed function applied to
||| its exact decompositions and moved transitions.
public export
0 adjacentSwapOperationalOccurrenceFoldSpike :
  (original : Transitions initial originalFinal) ->
  (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) ->
  (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  (replayedSuffix : Transitions (swappedFinal diamond) replayedFinal) ->
  (swappedTrace : Transitions initial replayedFinal) ->
  appendTransitions prefixTrace (MoreTransitions left (MoreTransitions right suffix)) =
    original ->
  appendTransitions prefixTrace
    (MoreTransitions (movedRight diamond)
      (MoreTransitions (movedLeft diamond) replayedSuffix)) = swappedTrace ->
  AdjacentSwapOperationalOccurrenceFold name key world error value original prefixTrace
    left right suffix (movedRight diamond) (movedLeft diamond) replayedSuffix
    swappedTrace
adjacentSwapOperationalOccurrenceFoldSpike =
  ?adjacentSwapOperationalOccurrenceFoldSpike_rhs

||| A complete adjacent transposition: the local pair is swapped, the untouched
||| suffix is replayed, and the next recursion receives the same full premise
||| bundle.  It also exposes exact same-external-input and generator/stage
||| correspondence rather than expecting endpoint relations to imply them.
public export
record AdjacentSwapResult
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
    SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (tracePrefix : Transitions initial pairFirst)
  (left : Transition pairFirst pairMiddle)
  (right : Transition pairMiddle pairFinal)
  (suffix : Transitions pairFinal originalFinal)
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) where
  constructor MkAdjacentSwapResult
  replayedFinal : SystemState name key value world error
  replayedSuffix : Transitions (swappedFinal diamond) replayedFinal
  swappedTrace : Transitions initial replayedFinal
  0 originalDecomposition : appendTransitions tracePrefix
    (MoreTransitions left (MoreTransitions right suffix)) = original
  0 swappedDecomposition : swappedTrace = appendTransitions tracePrefix
    (MoreTransitions (movedRight diamond)
      (MoreTransitions (movedLeft diamond) replayedSuffix))
  swappedSameExternalInputs :
    SameExternalOrchestration nameEq original swappedTrace
  swappedReplayCorrespondence : RelationalReplayCorrespondence name key world
    error value original swappedTrace
  swappedEndpoint : RelationalReplayEndpoint name key world error value nameEq
    keyEq originalFinal replayedFinal
  swappedPremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq swappedTrace

||| The first operational occurrence certificate is definitionally the global
||| suffix-replay fold applied to this result's exact decompositions.
public export
0 swappedOccurrenceFold :
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
    original tracePrefix left right suffix diamond) ->
  AdjacentSwapOperationalOccurrenceFold name key world error value original tracePrefix
    left right suffix (movedRight diamond) (movedLeft diamond)
    (replayedSuffix result) (swappedTrace result)
swappedOccurrenceFold {original} {tracePrefix} {left} {right} {suffix} {diamond}
  result =
    adjacentSwapOperationalOccurrenceFoldSpike original tracePrefix left right suffix
      diamond (replayedSuffix result) (swappedTrace result)
      (originalDecomposition result) (sym (swappedDecomposition result))

public export
0 swappedOccurrenceCorrespondence :
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
    original tracePrefix left right suffix diamond) ->
  ActionRegistrationReplayCorrespondence name key world error value original
    (swappedTrace result)
swappedOccurrenceCorrespondence result =
  operationalOccurrenceCorrespondence (swappedOccurrenceFold result)

||| The finite derivation records which one of the four source-sensitive local
||| diamonds justified every adjacent transition transposition.  Thus a block
||| producer cannot hide an unclassified pair behind endpoint assertions.
public export
data AdjacentSwapOrientationEvidence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, middle, afterState : SystemState name key value world error} ->
  Transition before middle -> Transition middle afterState -> Type where
  AdjacentActivationActivation :
    (left : Transition before middle) ->
    (right : Transition middle afterState) ->
    PaperActivationStep left -> PaperActivationStep right ->
    AdjacentSwapOrientationEvidence left right
  AdjacentActivationOrchestration :
    (left : Transition before middle) ->
    (right : Transition middle afterState) ->
    PaperActivationStep left -> PaperOrchestrationStep right ->
    AdjacentSwapOrientationEvidence left right
  AdjacentOrchestrationActivation :
    (left : Transition before middle) ->
    (right : Transition middle afterState) ->
    PaperOrchestrationStep left -> PaperActivationStep right ->
    AdjacentSwapOrientationEvidence left right
  AdjacentOrchestrationOrchestration :
    (left : Transition before middle) ->
    (right : Transition middle afterState) ->
    PaperOrchestrationStep left -> PaperOrchestrationStep right ->
    AdjacentSwapOrientationEvidence left right

||| A finite whole-block replay is not an assertion about its endpoint.  It is
||| an explicit list of source-sensitive adjacent transpositions, each carrying
||| the concrete A/A, A/O, O/A, or O/O `LocalRelationalDiamond` and the complete
||| `AdjacentSwapResult` returned by suffix replay.
public export
data FiniteAdjacentSwapDerivation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  Transitions initial sourceFinal -> Transitions initial targetFinal -> Type where
  FiniteAdjacentSwapDone :
    FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq
      trace trace
  FiniteAdjacentSwapStep :
    {initial, pairFirst, pairMiddle, pairFinal, originalFinal, targetFinal :
      SystemState name key value world error} ->
    (original : Transitions initial originalFinal) ->
    (prefixTrace : Transitions initial pairFirst) ->
    (left : Transition pairFirst pairMiddle) ->
    (right : Transition pairMiddle pairFinal) ->
    (suffix : Transitions pairFinal originalFinal) ->
    (orientation : AdjacentSwapOrientationEvidence left right) ->
    (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
      left right) ->
    (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
      original prefixTrace left right suffix diamond) ->
    (target : Transitions initial targetFinal) ->
    (rest : FiniteAdjacentSwapDerivation name key world error value protocol
      nameEq keyEq (swappedTrace result) target) ->
    FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq
      original target

||| A nontrivial actor-block transposition cannot use the zero-node terminator.
||| This family exposes its first concrete orientation/diamond/result and leaves
||| `FiniteAdjacentSwapDone` available only for the tail after all crossings.
public export
data NonEmptyFiniteAdjacentSwapDerivation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  Transitions initial sourceFinal -> Transitions initial targetFinal -> Type where
  NonEmptyAdjacentSwap :
    {initial, pairFirst, pairMiddle, pairFinal, originalFinal, targetFinal :
      SystemState name key value world error} ->
    (original : Transitions initial originalFinal) ->
    (prefixTrace : Transitions initial pairFirst) ->
    (left : Transition pairFirst pairMiddle) ->
    (right : Transition pairMiddle pairFinal) ->
    (suffix : Transitions pairFinal originalFinal) ->
    (orientation : AdjacentSwapOrientationEvidence left right) ->
    (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
      left right) ->
    (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
      original prefixTrace left right suffix diamond) ->
    (target : Transitions initial targetFinal) ->
    (rest : FiniteAdjacentSwapDerivation name key world error value protocol
      nameEq keyEq (swappedTrace result) target) ->
    NonEmptyFiniteAdjacentSwapDerivation name key world error value protocol
      nameEq keyEq original target

public export
nonEmptyToFiniteAdjacentSwapDerivation :
  NonEmptyFiniteAdjacentSwapDerivation name key world error value protocol nameEq
    keyEq source target ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq
    source target
nonEmptyToFiniteAdjacentSwapDerivation
  (NonEmptyAdjacentSwap original prefixTrace left right suffix orientation diamond
    result target rest) =
      FiniteAdjacentSwapStep original prefixTrace left right suffix orientation
        diamond result target rest

public export
finiteAdjacentSwapNodeCount :
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq
    source target -> Nat
finiteAdjacentSwapNodeCount FiniteAdjacentSwapDone = Z
finiteAdjacentSwapNodeCount
  (FiniteAdjacentSwapStep _ _ _ _ _ _ _ _ _ rest) =
    S (finiteAdjacentSwapNodeCount rest)

public export
nonEmptyAdjacentSwapNodeCount :
  NonEmptyFiniteAdjacentSwapDerivation name key world error value protocol nameEq
    keyEq source target -> Nat
nonEmptyAdjacentSwapNodeCount
  (NonEmptyAdjacentSwap _ _ _ _ _ _ _ _ _ rest) =
    S (finiteAdjacentSwapNodeCount rest)

public export
0 finiteDerivationReplayCorrespondence :
  (derivation : FiniteAdjacentSwapDerivation name key world error value protocol
    nameEq keyEq source target) ->
  RelationalReplayCorrespondence name key world error value source target
finiteDerivationReplayCorrespondence FiniteAdjacentSwapDone =
  MkRelationalReplayCorrespondence (\actor, generator => generator)
    (\actor, generator, state => Refl) (\actor, stage => stage)
    (\actor, stage, state => Refl)
finiteDerivationReplayCorrespondence
  (FiniteAdjacentSwapStep _ _ _ _ _ _ _ result _ rest) =
    composeRelationalReplayCorrespondence (swappedReplayCorrespondence result)
      (finiteDerivationReplayCorrespondence rest)

public export
0 finiteDerivationOccurrenceCorrespondence :
  (derivation : FiniteAdjacentSwapDerivation name key world error value protocol
    nameEq keyEq source target) ->
  ActionRegistrationReplayCorrespondence name key world error value source target
finiteDerivationOccurrenceCorrespondence {source}
  FiniteAdjacentSwapDone = identityActionRegistrationReplayCorrespondence source
finiteDerivationOccurrenceCorrespondence
  (FiniteAdjacentSwapStep _ _ _ _ _ _ _ result _ rest) =
    composeActionRegistrationReplayCorrespondence
      (swappedOccurrenceCorrespondence result)
      (finiteDerivationOccurrenceCorrespondence rest)

||| Candidate for paper Lemma 71(1).
public export
0 activationActivationDiamondSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, earlyRightFinal :
    SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (earlyRight : Transition first earlyRightFinal) ->
  transitionAction earlyRight = transitionAction right ->
  transitionTag earlyRight = transitionTag right ->
  PaperActivationStep left -> PaperActivationStep right ->
  Not (transitionActor left = transitionActor right) ->
  registryWellFormed @{nameEq} @{keyEq} first = True ->
  TraceIndependent name key world error value keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
activationActivationDiamondSpike = ?activationActivationDiamondSpike_rhs

||| Candidate for paper Lemma 71(2).
public export
0 activationOrchestrationDiamondSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal : SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  PaperActivationStep left -> PaperOrchestrationStep right ->
  Not (transitionActor left = transitionActor right) ->
  ((child, parent : name) ->
    (component : Component key value world error) ->
    transitionAction right = OInsert child (ChildOf parent) component ->
    Not (transitionActor left = parent)) ->
  registryWellFormed @{nameEq} @{keyEq} first = True ->
  TraceIndependent name key world error value keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
activationOrchestrationDiamondSpike = ?activationOrchestrationDiamondSpike_rhs

||| The reverse mixed orientation needed when a yielded O-Insert at the end of
||| one actor block crosses the following block's activation while bubbling that
||| block left.  `earlyRight` is the checked activation at the pre-orchestration
||| source; child/parent exclusions keep the activation independent of the
||| insertion generation and its licensing parent.
public export
0 orchestrationActivationDiamondSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, earlyRightFinal :
    SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (earlyRight : Transition first earlyRightFinal) ->
  transitionAction earlyRight = transitionAction right ->
  transitionTag earlyRight = transitionTag right ->
  PaperOrchestrationStep left -> PaperActivationStep right ->
  Not (transitionActor left = transitionActor right) ->
  ((child : name) -> (parent : Parent name) ->
    (component : Component key value world error) ->
    transitionAction left = OInsert child parent component ->
    Not (transitionActor right = child)) ->
  ((child, parent : name) ->
    (component : Component key value world error) ->
    transitionAction left = OInsert child (ChildOf parent) component ->
    Not (transitionActor right = parent)) ->
  registryWellFormed @{nameEq} @{keyEq} first = True ->
  TraceIndependent name key world error value keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
orchestrationActivationDiamondSpike =
  ?orchestrationActivationDiamondSpike_rhs

||| Missing Lemma-71 case exposed by yielded child registrations: two checked
||| orchestration rules, including O-Insert/O-Insert, must transpose under the
||| exact source freshness/generation/licensing package above.
public export
0 orchestrationOrchestrationDiamondSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {first, middle, originalFinal : SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  PaperOrchestrationStep left -> PaperOrchestrationStep right ->
  Not (transitionActor left = transitionActor right) ->
  OrchestrationSwapSafety name key world error value protocol nameEq keyEq
    left right ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
orchestrationOrchestrationDiamondSpike =
  ?orchestrationOrchestrationDiamondSpike_rhs

||| Checked suffix-splice interface consumed by sorting.  It is generic over the
||| local diamond case (A/A, A/O, O/A, or O/O) and returns all recursive capital.
public export
0 adjacentSwapSuffixSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
    SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (tracePrefix : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) ->
  (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) ->
  appendTransitions tracePrefix (MoreTransitions left (MoreTransitions right suffix)) =
    original ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq original ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  AdjacentSwapResult name key world error value protocol nameEq keyEq original
    tracePrefix left right suffix diamond
adjacentSwapSuffixSpike = ?adjacentSwapSuffixSpike_rhs

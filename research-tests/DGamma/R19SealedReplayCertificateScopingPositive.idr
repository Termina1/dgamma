module DGamma.R19SealedReplayCertificateScopingPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import Decidable.Equality

%default total

||| Historical revision-19 scoping probe.  The recursive spine remains accepted,
||| but the certificate's suffix-local `ReplayInvariantBundle` field was rejected
||| by the first cross-state checkpoint: that bundle is global-from-empty capital.
||| See `O6-R19-CROSS-STATE-BUNDLE-MISMATCH-AUDIT.md`.  The declarations stay as
||| a checked pin of the superseded candidate and are not the next boundary.

||| Candidate recursive spine for revision-19 scoping. `export` exposes the type
||| but not its constructors to importing modules. Each nonempty node owns exact
||| checked source/replayed transitions and the already sealed recursive tail;
||| no constructor quantifies a fresh arbitrary tail trace.
export
data ScopedReplaySpine :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {sourceFirst, sourceFinal, replayedFirst, replayedFinal :
    SystemState name key value world error} ->
  Transitions sourceFirst sourceFinal ->
  Transitions replayedFirst replayedFinal -> Type where
  ScopedReplayEnd : ScopedReplaySpine NoTransitions NoTransitions
  ScopedReplayStep :
    (sourceStep : Transition sourceFirst sourceMiddle) ->
    (replayedStep : Transition replayedFirst replayedMiddle) ->
    (sourceTail : Transitions sourceMiddle sourceFinal) ->
    (replayedTail : Transitions replayedMiddle replayedFinal) ->
    transitionAction replayedStep = transitionAction sourceStep ->
    transitionTag replayedStep = transitionTag sourceStep ->
    ScopedReplaySpine sourceTail replayedTail ->
    ScopedReplaySpine (MoreTransitions sourceStep sourceTail)
      (MoreTransitions replayedStep replayedTail)

0 identityRelationalReplayCorrespondenceR19 :
  (trace : Transitions initial finalState) ->
  RelationalReplayCorrespondence name key world error value trace trace
identityRelationalReplayCorrespondenceR19 trace =
  MkRelationalReplayCorrespondence (\actor, generator => generator)
    (\observedKeyEq, actor, generator =>
      replayTraceGeneratorMapRespects observedKeyEq generator)
    (\actor, stage => stage) (\actor, stage, state => Refl)

0 identityActionOrdinalR19 :
  (trace : Transitions initial finalState) ->
  {action : Action name key value world error} ->
  (occurrence : LocatedActionOccurrence action trace) ->
  locatedActionOrdinal
    (replayActionOrigin
      (identityActionRegistrationReplayCorrespondence trace) occurrence) =
    locatedActionOrdinal occurrence
identityActionOrdinalR19 trace occurrence = Refl

||| Superseded suffix-relative candidate.  `scopedNextBundle` is intentionally
||| retained as the checked historical mistake: the corrected recursive spine
||| omits it, while the opaque outer adjacent envelope owns the whole-trace
||| bundle.
export
record ScopedSealedSuffixReplayCertificate
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {sourceFirst, sourceFinal, replayedFirst, replayedFinal :
    SystemState name key value world error}
  (sourceSuffix : Transitions sourceFirst sourceFinal)
  (replayedSuffix : Transitions replayedFirst replayedFinal) where
  constructor MkScopedSealedSuffixReplayCertificate
  0 scopedReplaySpine : ScopedReplaySpine sourceSuffix replayedSuffix
  0 scopedRAR : RelationalReplayCorrespondence name key world error value
    sourceSuffix replayedSuffix
  0 scopedEndpoint : RelationalReplayEndpoint name key world error value nameEq
    keyEq sourceFinal replayedFinal
  0 scopedNextBundle : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq replayedSuffix
  0 scopedExternal : SameExternalOrchestration nameEq sourceSuffix
    replayedSuffix
  0 scopedOccurrences : ActionRegistrationReplayCorrespondence name key world
    error value sourceSuffix replayedSuffix
  0 scopedRelativeOrdinal :
    {action : Action name key value world error} ->
    (occurrence : LocatedActionOccurrence action replayedSuffix) ->
    locatedActionOrdinal
      (replayActionOrigin scopedOccurrences occurrence) =
      locatedActionOrdinal occurrence

||| Historical empty-state producer for the superseded candidate.  It works only
||| because the suffix state is itself globally empty and is not evidence that a
||| normal post-swap empty suffix can carry `ReplayInvariantBundle`.
export
0 scopedSuffixFreeCertificateProducer :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {state : SystemState name key value world error} ->
  (bundle : ReplayInvariantBundle name key world error value protocol nameEq
    keyEq (the (Transitions state state) NoTransitions)) ->
  ScopedSealedSuffixReplayCertificate name key world error value protocol
    nameEq keyEq (the (Transitions state state) NoTransitions)
      (the (Transitions state state) NoTransitions)
scopedSuffixFreeCertificateProducer nameEq keyEq protocol bundle =
  MkScopedSealedSuffixReplayCertificate ScopedReplayEnd
       (identityRelationalReplayCorrespondenceR19 NoTransitions)
       (relationalReplayEndpointReflexiveSpike nameEq keyEq state
         (replayFinalWellFormed bundle))
       bundle
       (sameExternalOrchestrationReflexiveSpike nameEq NoTransitions)
       (identityActionRegistrationReplayCorrespondence NoTransitions)
       (identityActionOrdinalR19 NoTransitions)

||| Historical checked identity one-step shape.  It still validates constructor
||| sealing, but its caller-supplied whole bundle cannot become suffix-local
||| recursive capital.  The checked cross-state retire probe derives the actual
||| replacement head without this premise.
export
0 scopedOneStepCertificateProducer :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {first, finalState : SystemState name key value world error} ->
  (step : Transition first finalState) ->
  (bundle : ReplayInvariantBundle name key world error value protocol nameEq
    keyEq (MoreTransitions step NoTransitions)) ->
  ScopedSealedSuffixReplayCertificate name key world error value protocol
    nameEq keyEq (MoreTransitions step NoTransitions)
      (MoreTransitions step NoTransitions)
scopedOneStepCertificateProducer nameEq keyEq protocol step bundle =
  MkScopedSealedSuffixReplayCertificate
       (ScopedReplayStep step step NoTransitions NoTransitions Refl Refl
         ScopedReplayEnd)
       (identityRelationalReplayCorrespondenceR19
         (MoreTransitions step NoTransitions))
       (relationalReplayEndpointReflexiveSpike nameEq keyEq finalState
         (replayFinalWellFormed bundle))
       bundle
       (sameExternalOrchestrationReflexiveSpike nameEq
         (MoreTransitions step NoTransitions))
       (identityActionRegistrationReplayCorrespondence
         (MoreTransitions step NoTransitions))
       (identityActionOrdinalR19 (MoreTransitions step NoTransitions))

||| Projection probe: downstream recursion sees only producer-owned outputs.
export
0 scopedCertificateOccurrenceProjection :
  (certificate : ScopedSealedSuffixReplayCertificate name key world error value
    protocol nameEq keyEq sourceSuffix replayedSuffix) ->
  ActionRegistrationReplayCorrespondence name key world error value sourceSuffix
    replayedSuffix
scopedCertificateOccurrenceProjection certificate = scopedOccurrences certificate

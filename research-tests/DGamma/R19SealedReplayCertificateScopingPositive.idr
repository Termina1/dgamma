module DGamma.R19SealedReplayCertificateScopingPositive

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import Decidable.Equality

%default total

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
    (\actor, generator, state => Refl) (\actor, stage => stage)
    (\actor, stage, state => Refl)

0 identityActionOrdinalR19 :
  (trace : Transitions initial finalState) ->
  {action : Action name key value world error} ->
  (occurrence : LocatedActionOccurrence action trace) ->
  locatedActionOrdinal
    (replayActionOrigin
      (identityActionRegistrationReplayCorrespondence trace) occurrence) =
    locatedActionOrdinal occurrence
identityActionOrdinalR19 trace occurrence = Refl

||| Suffix-relative candidate owned by the future simultaneous producer. It
||| carries every recursively composable observation rather than accepting them
||| later at the occurrence-fold projection boundary.
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

||| Suffix-free base producer. All capital is derived from the exact empty trace
||| bundle; no replayed trace, endpoint, occurrence map, or ordinal function is
||| accepted from its caller.
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

||| Genuine checked one-step shape. The transition already owns its evaluator
||| equation. The producer chooses the replayed trace definitionally, builds the
||| sealed nonempty spine from that checked transition plus the sealed base, and
||| derives every certificate field by identity. This validates the recursive
||| ownership boundary; the future cross-state producer must replace only the
||| identity head with its checked replayed head while retaining the same sealed
||| tail discipline.
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

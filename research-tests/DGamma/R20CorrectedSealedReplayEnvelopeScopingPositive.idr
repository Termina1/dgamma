module DGamma.R20CorrectedSealedReplayEnvelopeScopingPositive

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

||| Corrected revision-20 recursive replay spine.  A node owns only capital whose
||| indices are local to the exact source/replayed suffix head.  In particular it
||| has no `ReplayInvariantBundle`: that package starts at the globally empty
||| state and belongs only to the outer whole-trace envelope.
export
data SealedSuffixReplaySpine :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {sourceFirst, sourceFinal, replayedFirst, replayedFinal :
    SystemState name key value world error} ->
  Transitions sourceFirst sourceFinal ->
  Transitions replayedFirst replayedFinal -> Type where
  SealedSuffixReplayEnd :
    SealedSuffixReplaySpine name key world error value nameEq keyEq
      NoTransitions NoTransitions
  SealedSuffixReplayStep :
    (sourceStep : Transition sourceFirst sourceMiddle) ->
    (replayedStep : Transition replayedFirst replayedMiddle) ->
    (sourceTail : Transitions sourceMiddle sourceFinal) ->
    (replayedTail : Transitions replayedMiddle replayedFinal) ->
    (0 sameAction : transitionAction replayedStep =
      transitionAction sourceStep) ->
    (0 sameTag : transitionTag replayedStep = transitionTag sourceStep) ->
    (0 headRAR : RelationalReplayCorrespondence name key world error value
      (MoreTransitions sourceStep NoTransitions)
      (MoreTransitions replayedStep NoTransitions)) ->
    (0 headEndpoint : RelationalReplayEndpoint name key world error value nameEq
      keyEq sourceMiddle replayedMiddle) ->
    (0 headOccurrences : ActionRegistrationReplayCorrespondence name key world
      error value (MoreTransitions sourceStep NoTransitions)
      (MoreTransitions replayedStep NoTransitions)) ->
    (0 headRelativeOrdinal :
      {action : Action name key value world error} ->
      (occurrence : LocatedActionOccurrence action
        (MoreTransitions replayedStep NoTransitions)) ->
      locatedActionOrdinal occurrence = locatedActionOrdinal
        (replayActionOrigin headOccurrences occurrence)) ->
    SealedSuffixReplaySpine name key world error value nameEq keyEq sourceTail
      replayedTail ->
    SealedSuffixReplaySpine name key world error value nameEq keyEq
      (MoreTransitions sourceStep sourceTail)
      (MoreTransitions replayedStep replayedTail)

||| Test-local corrected outer envelope.  Its constructor is not exported.  It
||| mirrors the nine live `AdjacentSwapResult` fields and adds only the two
||| producer-owned seals proposed for the eventual boundary.  The whole bundle
||| is indexed by `wholeSwappedTrace`, which starts at the original globally
||| empty state; no recursive spine node contains such a bundle.
export
record CorrectedAdjacentReplayEnvelope
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
  constructor MkCorrectedAdjacentReplayEnvelope
  wholeReplayedFinal : SystemState name key value world error
  wholeReplayedSuffix : Transitions (swappedFinal diamond) wholeReplayedFinal
  wholeSwappedTrace : Transitions initial wholeReplayedFinal
  0 wholeOriginalDecomposition : appendTransitions tracePrefix
    (MoreTransitions left (MoreTransitions right suffix)) = original
  0 wholeSwappedDecomposition : wholeSwappedTrace = appendTransitions tracePrefix
    (MoreTransitions (movedRight diamond)
      (MoreTransitions (movedLeft diamond) wholeReplayedSuffix))
  wholeExternal : SameExternalOrchestration nameEq original wholeSwappedTrace
  wholeRAR : RelationalReplayCorrespondence name key world error value original
    wholeSwappedTrace
  wholeEndpoint : RelationalReplayEndpoint name key world error value nameEq keyEq
    originalFinal wholeReplayedFinal
  wholePremises : ReplayInvariantBundle name key world error value protocol nameEq
    keyEq wholeSwappedTrace
  0 sealedSuffixReplay : SealedSuffixReplaySpine name key world error value nameEq
    keyEq suffix wholeReplayedSuffix
  0 sealedOccurrenceFold : AdjacentSwapOperationalOccurrenceFold name key world
    error value original tracePrefix left right suffix (movedRight diamond)
    (movedLeft diamond) wholeReplayedSuffix wholeSwappedTrace

||| Consumer projection: the complete action/generated occurrence map is owned
||| by the sealed fold rather than accepted independently.
export
0 correctedEnvelopeOccurrences :
  (envelope : CorrectedAdjacentReplayEnvelope name key world error value protocol
    nameEq keyEq original tracePrefix left right suffix diamond) ->
  ActionRegistrationReplayCorrespondence name key world error value original
    (wholeSwappedTrace envelope)
correctedEnvelopeOccurrences envelope = operationalOccurrenceCorrespondence
  (sealedOccurrenceFold envelope)

||| Consumer projection: the absolute adjacent ordinal law is likewise sealed in
||| the exact fold selected by this envelope.
export
0 correctedEnvelopeAbsoluteOrdinal :
  (envelope : CorrectedAdjacentReplayEnvelope name key world error value protocol
    nameEq keyEq original tracePrefix left right suffix diamond) ->
  {action : Action name key value world error} ->
  (occurrence : LocatedActionOccurrence action (wholeSwappedTrace envelope)) ->
  AdjacentSwapOrdinalRelation (transitionCount tracePrefix)
    (locatedActionOrdinal occurrence)
    (locatedActionOrdinal
      (replayActionOrigin (correctedEnvelopeOccurrences envelope) occurrence))
correctedEnvelopeAbsoluteOrdinal envelope = operationalOrdinalRelation
  (sealedOccurrenceFold envelope)

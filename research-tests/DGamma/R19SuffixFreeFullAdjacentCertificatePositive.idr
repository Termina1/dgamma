module DGamma.R19SuffixFreeFullAdjacentCertificatePositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Metatheory
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import Data.Nat
import Decidable.Equality

%default total

0 advanceIsNotOrchestration :
  transitionAction transition = LAdvance actor ->
  PaperOrchestrationStep transition -> Void
advanceIsNotOrchestration advance (PaperInsertStep insert) =
  case trans (sym advance) insert of Refl impossible
advanceIsNotOrchestration advance (PaperRetireStep retire) =
  case trans (sym advance) retire of Refl impossible
advanceIsNotOrchestration advance (PaperRemoveStep remove) =
  case trans (sym advance) remove of Refl impossible

0 twoSuccCountInjective : S (S count) = S (S Z) -> count = Z
twoSuccCountInjective Refl = Refl

0 appendedTraceCountNonZero :
  (tracePrefix : Transitions first point) ->
  (step : Transition point afterStep) ->
  (suffix : Transitions afterStep finalState) ->
  transitionCount (appendTransitions tracePrefix
    (MoreTransitions step suffix)) = Z -> Void
appendedTraceCountNonZero NoTransitions step suffix Refl impossible
appendedTraceCountNonZero (MoreTransitions head rest) step suffix Refl impossible

0 twoNodePrefixTooLong :
  (prefixFirst : Transition first second) ->
  (prefixSecond : Transition second point) ->
  (prefixRest : Transitions point beforeLocated) ->
  (located : Transition beforeLocated afterLocated) ->
  (suffix : Transitions afterLocated finalState) ->
  (left : Transition first middle) ->
  (right : Transition middle finalState) ->
  appendTransitions
    (MoreTransitions prefixFirst (MoreTransitions prefixSecond prefixRest))
    (MoreTransitions located suffix) =
      MoreTransitions left (MoreTransitions right NoTransitions) -> Void
twoNodePrefixTooLong prefixFirst prefixSecond prefixRest located suffix left right
  decomposition = appendedTraceCountNonZero prefixRest located suffix
    (twoSuccCountInjective (cong transitionCount decomposition))

||| Historical note: the former zero-consumer `repeatedIterIdentityDiamond`
||| helper was retired in revision 21.  It accepted arbitrary dictionary-storing
||| transitions without source alignment.  The live full-certificate producer
||| below retains the genuine identity-pair construction because it consumes an
||| authenticated `ReplayInvariantBundle` and can project `replayAligned`.

public export
record TwoAdvanceOccurrenceCertificate
  {name, key, world, error : Type} {value : key -> Type}
  {first, middle, finalState : SystemState name key value world error}
  {left : Transition first middle}
  {right : Transition middle finalState}
  {action : Action name key value world error}
  (occurrence : LocatedActionOccurrence action
    (MoreTransitions left (MoreTransitions right NoTransitions))) where
  constructor MkTwoAdvanceOccurrenceCertificate
  0 swappedSourceOccurrence : LocatedActionOccurrence action
    (MoreTransitions left (MoreTransitions right NoTransitions))
  0 swappedSourceTagPreserved :
    transitionTag (locatedTransition swappedSourceOccurrence) =
      transitionTag (locatedTransition occurrence)
  0 swappedSourceOrdinal : AdjacentSwapOrdinalRelation Z
    (locatedActionOrdinal occurrence)
    (locatedActionOrdinal swappedSourceOccurrence)

0 twoAdvanceOccurrenceCertificate :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {left : Transition first middle} ->
  {right : Transition middle finalState} ->
  {actor : name} ->
  (leftAdvance : transitionAction left = LAdvance actor) ->
  (leftIter : transitionTag left = LIterTag) ->
  (rightAdvance : transitionAction right = LAdvance actor) ->
  (rightIter : transitionTag right = LIterTag) ->
  {action : Action name key value world error} ->
  (occurrence : LocatedActionOccurrence action
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  TwoAdvanceOccurrenceCertificate occurrence
twoAdvanceOccurrenceCertificate leftAdvance leftIter rightAdvance rightIter
  occurrence@(MkLocatedActionOccurrence before after NoTransitions left
    (MoreTransitions right NoTransitions) same Refl) =
      MkTwoAdvanceOccurrenceCertificate
        (MkLocatedActionOccurrence _ _ (MoreTransitions left NoTransitions) right
          NoTransitions (trans rightAdvance (trans (sym leftAdvance) same)) Refl)
        (trans rightIter (sym leftIter)) AdjacentMovedRightOrdinal
twoAdvanceOccurrenceCertificate leftAdvance leftIter rightAdvance rightIter
  occurrence@(MkLocatedActionOccurrence before after
    (MoreTransitions left NoTransitions) right NoTransitions same Refl) =
      MkTwoAdvanceOccurrenceCertificate
        (MkLocatedActionOccurrence _ _ NoTransitions left
          (MoreTransitions right NoTransitions)
          (trans leftAdvance (trans (sym rightAdvance) same)) Refl)
        (trans leftIter (sym rightIter)) AdjacentMovedLeftOrdinal
twoAdvanceOccurrenceCertificate leftAdvance leftIter rightAdvance rightIter
  (MkLocatedActionOccurrence before after
    (MoreTransitions prefixStep (MoreTransitions secondPrefix prefixRest))
    located suffix same decomposition) =
      void (twoNodePrefixTooLong prefixStep secondPrefix prefixRest located suffix
        left right decomposition)

0 twoAdvanceOccurrenceAction :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {left : Transition first middle} ->
  {right : Transition middle finalState} ->
  {actor : name} ->
  (leftAdvance : transitionAction left = LAdvance actor) ->
  (rightAdvance : transitionAction right = LAdvance actor) ->
  {action : Action name key value world error} ->
  (occurrence : LocatedActionOccurrence action
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  action = LAdvance actor
twoAdvanceOccurrenceAction leftAdvance rightAdvance
  (MkLocatedActionOccurrence before after NoTransitions left
    (MoreTransitions right NoTransitions) same Refl) =
      trans (sym same) leftAdvance
twoAdvanceOccurrenceAction leftAdvance rightAdvance
  (MkLocatedActionOccurrence before after
    (MoreTransitions left NoTransitions) right NoTransitions same Refl) =
      trans (sym same) rightAdvance
twoAdvanceOccurrenceAction leftAdvance rightAdvance
  (MkLocatedActionOccurrence before after
    (MoreTransitions prefixStep (MoreTransitions secondPrefix prefixRest))
    located suffix same decomposition) =
      void (twoNodePrefixTooLong prefixStep secondPrefix prefixRest located suffix
        left right decomposition)

0 twoAdvanceHasNoGeneratedRegistration :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {left : Transition first middle} ->
  {right : Transition middle finalState} ->
  {actor : name} ->
  (leftAdvance : transitionAction left = LAdvance actor) ->
  (rightAdvance : transitionAction right = LAdvance actor) ->
  {child, parent : name} ->
  {component : Component key value world error} ->
  (generated : LocatedGeneratedRegistration child parent component
    (MoreTransitions left (MoreTransitions right NoTransitions))) -> Void
twoAdvanceHasNoGeneratedRegistration leftAdvance rightAdvance generated =
  case twoAdvanceOccurrenceAction leftAdvance rightAdvance
    (generatedRegistrationActionOccurrence generated) of Refl impossible

0 swapTwoAdvanceActionOrigin :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {left : Transition first middle} -> {right : Transition middle finalState} ->
  {actor : name} -> {action : Action name key value world error} ->
  (leftAdvance : transitionAction left = LAdvance actor) ->
  (leftIter : transitionTag left = LIterTag) ->
  (rightAdvance : transitionAction right = LAdvance actor) ->
  (rightIter : transitionTag right = LIterTag) ->
  (occurrence : LocatedActionOccurrence action
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  LocatedActionOccurrence action
    (MoreTransitions left (MoreTransitions right NoTransitions))
swapTwoAdvanceActionOrigin leftAdvance leftIter rightAdvance rightIter occurrence =
  swappedSourceOccurrence
    (twoAdvanceOccurrenceCertificate leftAdvance leftIter rightAdvance rightIter
      occurrence)

0 swapTwoAdvanceTagPreserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {left : Transition first middle} -> {right : Transition middle finalState} ->
  {actor : name} -> {action : Action name key value world error} ->
  (leftAdvance : transitionAction left = LAdvance actor) ->
  (leftIter : transitionTag left = LIterTag) ->
  (rightAdvance : transitionAction right = LAdvance actor) ->
  (rightIter : transitionTag right = LIterTag) ->
  (occurrence : LocatedActionOccurrence action
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  transitionTag (locatedTransition
    (swapTwoAdvanceActionOrigin leftAdvance leftIter rightAdvance rightIter
      occurrence)) = transitionTag (locatedTransition occurrence)
swapTwoAdvanceTagPreserved leftAdvance leftIter rightAdvance rightIter occurrence =
  swappedSourceTagPreserved
    (twoAdvanceOccurrenceCertificate leftAdvance leftIter rightAdvance rightIter
      occurrence)

0 swapTwoAdvanceOrdinal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {left : Transition first middle} -> {right : Transition middle finalState} ->
  {actor : name} -> {action : Action name key value world error} ->
  (leftAdvance : transitionAction left = LAdvance actor) ->
  (leftIter : transitionTag left = LIterTag) ->
  (rightAdvance : transitionAction right = LAdvance actor) ->
  (rightIter : transitionTag right = LIterTag) ->
  (occurrence : LocatedActionOccurrence action
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  AdjacentSwapOrdinalRelation Z (locatedActionOrdinal occurrence)
    (locatedActionOrdinal
      (swapTwoAdvanceActionOrigin leftAdvance leftIter rightAdvance rightIter
        occurrence))
swapTwoAdvanceOrdinal leftAdvance leftIter rightAdvance rightIter occurrence =
  swappedSourceOrdinal
    (twoAdvanceOccurrenceCertificate leftAdvance leftIter rightAdvance rightIter
      occurrence)

0 swapTwoAdvanceOccurrenceCorrespondence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {left : Transition first middle} ->
  {right : Transition middle finalState} ->
  {actor : name} ->
  (leftAdvance : transitionAction left = LAdvance actor) ->
  (leftIter : transitionTag left = LIterTag) ->
  (rightAdvance : transitionAction right = LAdvance actor) ->
  (rightIter : transitionTag right = LIterTag) ->
  ActionRegistrationReplayCorrespondence name key world error value
    (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions left (MoreTransitions right NoTransitions))
swapTwoAdvanceOccurrenceCorrespondence leftAdvance leftIter rightAdvance
  rightIter =
    MkActionRegistrationReplayCorrespondence
      identityRegistrationGenerationBijection
      (swapTwoAdvanceActionOrigin leftAdvance leftIter rightAdvance rightIter)
      (swapTwoAdvanceTagPreserved leftAdvance leftIter rightAdvance rightIter)
      (\generated => void
        (twoAdvanceHasNoGeneratedRegistration leftAdvance rightAdvance generated))
      (\generated => void
        (twoAdvanceHasNoGeneratedRegistration leftAdvance rightAdvance generated))
      (\generated => void
        (twoAdvanceHasNoGeneratedRegistration leftAdvance rightAdvance generated))

||| Test-local sealed suffix spine.  The suffix-free producer is the sole
||| constructor client; callers receive the spine only through the full result.
export
data FullAdjacentSuffixSpine :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  FullAdjacentSuffixEnd : FullAdjacentSuffixSpine NoTransitions

||| Candidate complete adjacent certificate at the suffix-free boundary.  It
||| deliberately contains every future `AdjacentSwapResult` output plus the
||| sealed fold and suffix spine, but is test-local and changes no frozen record.
public export
record ScopedFullSuffixFreeAdjacentCertificate
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {first, middle, finalState : SystemState name key value world error}
  (left : Transition first middle)
  (right : Transition middle finalState)
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) where
  constructor MkScopedFullSuffixFreeAdjacentCertificate
  fullReplayedFinal : SystemState name key value world error
  fullReplayedSuffix : Transitions (swappedFinal diamond) fullReplayedFinal
  fullSwappedTrace : Transitions first fullReplayedFinal
  0 fullOriginalDecomposition : appendTransitions NoTransitions
    (MoreTransitions left (MoreTransitions right NoTransitions)) =
      MoreTransitions left (MoreTransitions right NoTransitions)
  0 fullSwappedDecomposition : fullSwappedTrace = appendTransitions NoTransitions
    (MoreTransitions (movedRight diamond)
      (MoreTransitions (movedLeft diamond) fullReplayedSuffix))
  fullSameExternalInputs : SameExternalOrchestration nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions)) fullSwappedTrace
  fullReplayCorrespondence : RelationalReplayCorrespondence name key world error
    value (MoreTransitions left (MoreTransitions right NoTransitions))
    fullSwappedTrace
  fullEndpoint : RelationalReplayEndpoint name key world error value nameEq keyEq
    finalState fullReplayedFinal
  fullPremises : ReplayInvariantBundle name key world error value protocol nameEq
    keyEq fullSwappedTrace
  0 fullOccurrenceFold : AdjacentSwapOperationalOccurrenceFold name key world
    error value (MoreTransitions left (MoreTransitions right NoTransitions))
    NoTransitions left right NoTransitions (movedRight diamond)
    (movedLeft diamond) fullReplayedSuffix fullSwappedTrace
  0 fullSealedSuffix : FullAdjacentSuffixSpine fullReplayedSuffix

||| Full suffix-free producer.  Its only semantic premise is the checked source
||| bundle; every target field is derived because the repeated checked Iter pair
||| is a trace-preserving semantic transposition.  No endpoint, RAR, target
||| bundle, occurrence map, or ordinal law is accepted as an input.
public export
0 scopedFullSuffixFreeAdjacentCertificateProducer :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (actor : name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle finalState) ->
  (leftAdvance : transitionAction left = LAdvance actor) ->
  (leftIter : transitionTag left = LIterTag) ->
  (rightAdvance : transitionAction right = LAdvance actor) ->
  (rightIter : transitionTag right = LIterTag) ->
  (source : ReplayInvariantBundle name key world error value protocol nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
      left right **
    ScopedFullSuffixFreeAdjacentCertificate name key world error value protocol
      nameEq keyEq left right diamond)
scopedFullSuffixFreeAdjacentCertificateProducer nameEq keyEq protocol actor left
  right leftAdvance leftIter rightAdvance rightIter source =
    case relationalReplayEndpointReflexiveSpike nameEq keyEq finalState
      (replayFinalWellFormed source) of
      endpoint@(MkRelationalReplayEndpoint effects controls wellFormed) =>
        let diamond : LocalRelationalDiamond name key world error value nameEq
              keyEq left right
            diamond = MkLocalRelationalDiamond middle finalState left right
              (replayAligned source)
              (trans leftAdvance (sym rightAdvance))
              (trans leftIter (sym rightIter))
              (trans rightAdvance (sym leftAdvance))
              (trans rightIter (sym leftIter))
              (\paper => PaperIterStep leftAdvance leftIter)
              (\paper => PaperIterStep rightAdvance rightIter)
              (\paper => void (advanceIsNotOrchestration rightAdvance paper))
              (\paper => void (advanceIsNotOrchestration leftAdvance paper))
              (CandidateActivationActivation
                (PaperIterStep leftAdvance leftIter)
                (PaperIterStep rightAdvance rightIter))
              effects controls wellFormed
            trace = MoreTransitions left (MoreTransitions right NoTransitions)
            0 occurrence : ActionRegistrationReplayCorrespondence name key world
              error value (MoreTransitions left (MoreTransitions right NoTransitions))
              (MoreTransitions left (MoreTransitions right NoTransitions))
            occurrence = swapTwoAdvanceOccurrenceCorrespondence leftAdvance
              leftIter rightAdvance rightIter
            0 fold : AdjacentSwapOperationalOccurrenceFold name key world error
              value (MoreTransitions left (MoreTransitions right NoTransitions))
              NoTransitions left right NoTransitions left right NoTransitions
              (MoreTransitions left (MoreTransitions right NoTransitions))
            fold = MkAdjacentSwapOperationalOccurrenceFold Refl Refl occurrence
              (swapTwoAdvanceOrdinal leftAdvance leftIter rightAdvance rightIter)
        in (diamond ** MkScopedFullSuffixFreeAdjacentCertificate finalState
          NoTransitions trace Refl Refl
          (sameExternalOrchestrationReflexiveSpike nameEq trace)
          (MkRelationalReplayCorrespondence (\selected, generator => generator)
            (\observedKeyEq, selected, generator =>
              replayTraceGeneratorMapRespects observedKeyEq generator)
            (\selected, stage => stage) (\selected, stage, state => Refl))
          endpoint source fold FullAdjacentSuffixEnd)

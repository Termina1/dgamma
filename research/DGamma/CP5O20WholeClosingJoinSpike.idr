module DGamma.CP5O20WholeClosingJoinSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O20DeletionRetainedUnloadSpike
import DGamma.CP5O20DeletionRetainedBirthSpike
import DGamma.CP5O20NativeInsertEnvironmentSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5O20RetainedClosingIndexSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Control.Relation
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Both coordinates of a successful native subsequence lookup are inside
||| their OWN physical segment. These bounds separate the three segments.
export
0 o20SubsequenceOrdinalBounds :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {deletable : Nat -> GenerationEnvironment name -> Action name key value world error -> Type} ->
  {ordinal : Nat} -> {live : GenerationEnvironment name} ->
  {first, finalState, otherFirst, otherFinal : SystemState name key value world error} ->
  {trace : Transitions first finalState} -> {survivor : Transitions otherFirst otherFinal} ->
  (kept : GenerationActionSubsequence nameEq deletable ordinal live trace survivor) ->
  (targetIndex, sourceIndex : Nat) ->
  (generationSubsequenceSourceOrdinal kept targetIndex = Just sourceIndex) ->
  (LT targetIndex (transitionCount survivor), LT sourceIndex (transitionCount trace))
o20SubsequenceOrdinalBounds GenerationActionSubsequenceEnd targetIndex sourceIndex exact = absurd exact
o20SubsequenceOrdinalBounds (KeepGenerationAction step rest target later outside same tail) Z sourceIndex exact =
  (LTESucc LTEZero,
   replace {p = \source => LT source (S (transitionCount rest))}
     (justInjective exact) (LTESucc LTEZero))
o20SubsequenceOrdinalBounds (KeepGenerationAction step rest target later outside same tail) (S targetIndex) sourceIndex exact =
  case o20MappedSuccessorPredecessor (generationSubsequenceSourceOrdinal tail targetIndex) sourceIndex exact of
    (earlier ** (shift, origin)) =>
      case o20SubsequenceOrdinalBounds tail targetIndex earlier origin of
        (targetBound, sourceBound) =>
          (LTESucc targetBound,
           replace {p = \source => LT source (S (transitionCount rest))} (sym shift) (LTESucc sourceBound))
o20SubsequenceOrdinalBounds (DeleteGenerationAction step rest deleted tail) targetIndex sourceIndex exact =
  case o20MappedSuccessorPredecessor (generationSubsequenceSourceOrdinal tail targetIndex) sourceIndex exact of
    (earlier ** (shift, origin)) =>
      case o20SubsequenceOrdinalBounds tail targetIndex earlier origin of
        (targetBound, sourceBound) =>
          (targetBound,
           replace {p = \source => LT source (S (transitionCount rest))} (sym shift) (LTESucc sourceBound))

||| Exact cancellation and preservation of a common physical segment offset.
export
0 o20OffsetStrictOrder :
  (offset, left, right : Nat) ->
  (LT left right -> LT (offset + left) (offset + right),
   LT (offset + left) (offset + right) -> LT left right)
o20OffsetStrictOrder Z left right = (\ordered => ordered, \ordered => ordered)
o20OffsetStrictOrder (S offset) left right =
  case o20OffsetStrictOrder offset left right of
    (forward, backward) =>
      (\ordered => LTESucc (forward ordered), \ordered => backward (fromLteSucc ordered))

||| Reflect source order across ALL nine before/center/after combinations.
||| Both embeddings are the result's exact native subsequence equations.
||| Cross-segment target order follows from native segment bounds, never
||| from equal-action identification or an independently chosen target order.
export
0 o20WholeEmbeddingReflectsSourceOrder :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, finalState : SystemState name key value world error} ->
  {trace : Transitions initial finalState} -> {selected : name} ->
  {episode : LocatedClosedEpisode name key world error value nameEq keyEq selected trace} ->
  {registered : List (RegistrationGeneration name)} -> {startOrdinal : Nat} ->
  {startLive : GenerationEnvironment name} ->
  (result : DeletionResult name key world error value nameEq keyEq trace selected episode registered startOrdinal startLive) ->
  (leftTarget, rightTarget, leftSource, rightSource : Nat) ->
  DeletionSurvivingOrdinalEmbedding result leftTarget leftSource ->
  DeletionSurvivingOrdinalEmbedding result rightTarget rightSource ->
  LT leftSource rightSource -> LT leftTarget rightTarget
o20WholeEmbeddingReflectsSourceOrder result _ _ _ _
  (DeletionBeforeEmbedding {survivingOrdinal = lt} {originalOrdinal = ls} leftExact)
  (DeletionBeforeEmbedding {survivingOrdinal = rt} {originalOrdinal = rs} rightExact) ordered =
    o20SubsequenceReflectsSourceOrder (beforeDeletion result) lt rt ls rs leftExact rightExact ordered
o20WholeEmbeddingReflectsSourceOrder result _ _ _ _
  (DeletionBeforeEmbedding {survivingOrdinal = lt} {originalOrdinal = ls} leftExact)
  (DeletionEpisodeEmbedding {survivingOrdinal = rt} {originalOrdinal = rs} rightExact) ordered =
    transitive (fst (o20SubsequenceOrdinalBounds (beforeDeletion result) lt ls leftExact))
      (lteAddRight (deletionSurvivingBeforeCount result))
o20WholeEmbeddingReflectsSourceOrder result _ _ _ _
  (DeletionBeforeEmbedding {survivingOrdinal = lt} {originalOrdinal = ls} leftExact)
  (DeletionAfterEmbedding {survivingOrdinal = rt} {originalOrdinal = rs} rightExact) ordered =
    transitive (fst (o20SubsequenceOrdinalBounds (beforeDeletion result) lt ls leftExact))
      (transitive (lteAddRight (deletionSurvivingBeforeCount result))
        (lteAddRight (deletionSurvivingBeforeCount result + deletionSurvivingEpisodeCount result)))
o20WholeEmbeddingReflectsSourceOrder result _ _ _ _
  (DeletionEpisodeEmbedding {survivingOrdinal = lt} {originalOrdinal = ls} leftExact)
  (DeletionBeforeEmbedding {survivingOrdinal = rt} {originalOrdinal = rs} rightExact) ordered =
    void (succNotLTEpred (transitive
      (transitive ordered (lteSuccLeft (snd (o20SubsequenceOrdinalBounds (beforeDeletion result) rt rs rightExact))))
      (lteAddRight (deletionOriginalBeforeCount result))))
o20WholeEmbeddingReflectsSourceOrder result _ _ _ _
  (DeletionEpisodeEmbedding {survivingOrdinal = lt} {originalOrdinal = ls} leftExact)
  (DeletionEpisodeEmbedding {survivingOrdinal = rt} {originalOrdinal = rs} rightExact) ordered =
    fst (o20OffsetStrictOrder (deletionSurvivingBeforeCount result) lt rt)
      (o20SubsequenceReflectsSourceOrder (episodeDeletion result) lt rt ls rs leftExact rightExact
        (snd (o20OffsetStrictOrder (deletionOriginalBeforeCount result) ls rs) ordered))
o20WholeEmbeddingReflectsSourceOrder result _ _ _ _
  (DeletionEpisodeEmbedding {survivingOrdinal = lt} {originalOrdinal = ls} leftExact)
  (DeletionAfterEmbedding {survivingOrdinal = rt} {originalOrdinal = rs} rightExact) ordered =
    transitive (fst (o20OffsetStrictOrder (deletionSurvivingBeforeCount result) lt (deletionSurvivingEpisodeCount result))
      (fst (o20SubsequenceOrdinalBounds (episodeDeletion result) lt ls leftExact)))
      (lteAddRight (deletionSurvivingBeforeCount result + deletionSurvivingEpisodeCount result))
o20WholeEmbeddingReflectsSourceOrder result _ _ _ _
  (DeletionAfterEmbedding {survivingOrdinal = lt} {originalOrdinal = ls} leftExact)
  (DeletionBeforeEmbedding {survivingOrdinal = rt} {originalOrdinal = rs} rightExact) ordered =
    void (succNotLTEpred (transitive
      (transitive ordered (lteSuccLeft (snd (o20SubsequenceOrdinalBounds (beforeDeletion result) rt rs rightExact))))
      (transitive (lteAddRight (deletionOriginalBeforeCount result))
        (lteAddRight (deletionOriginalBeforeCount result + deletionOriginalEpisodeCount result)))))
o20WholeEmbeddingReflectsSourceOrder result _ _ _ _
  (DeletionAfterEmbedding {survivingOrdinal = lt} {originalOrdinal = ls} leftExact)
  (DeletionEpisodeEmbedding {survivingOrdinal = rt} {originalOrdinal = rs} rightExact) ordered =
    void (succNotLTEpred (transitive
      (transitive ordered (lteSuccLeft
        (fst (o20OffsetStrictOrder (deletionOriginalBeforeCount result) rs (deletionOriginalEpisodeCount result))
          (snd (o20SubsequenceOrdinalBounds (episodeDeletion result) rt rs rightExact)))))
      (lteAddRight (deletionOriginalBeforeCount result + deletionOriginalEpisodeCount result))))
o20WholeEmbeddingReflectsSourceOrder result _ _ _ _
  (DeletionAfterEmbedding {survivingOrdinal = lt} {originalOrdinal = ls} leftExact)
  (DeletionAfterEmbedding {survivingOrdinal = rt} {originalOrdinal = rs} rightExact) ordered =
    fst (o20OffsetStrictOrder ((deletionSurvivingBeforeCount result + deletionSurvivingEpisodeCount result)) lt rt)
      (o20SubsequenceReflectsSourceOrder (afterDeletion result) lt rt ls rs leftExact rightExact
        (snd (o20OffsetStrictOrder ((deletionOriginalBeforeCount result + deletionOriginalEpisodeCount result)) ls rs) ordered))

||| A real Unload inside the left segment keeps its physical index when a
||| later segment is appended. An out-of-range index cannot satisfy the input.
export
0 o20ClosingActionAtAppendLeft :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (earlier : Transitions first middle) -> (later : Transitions middle finalState) ->
  (ordinal : Nat) -> (actor : name) ->
  (rawClosingActionAt name key world error value ordinal earlier = Just (LUnload actor)) ->
  (rawClosingActionAt name key world error value ordinal (appendTransitions earlier later) = Just (LUnload actor))
o20ClosingActionAtAppendLeft name key world error value NoTransitions later ordinal actor exact = absurd exact
o20ClosingActionAtAppendLeft name key world error value
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest) later Z actor exact = exact
o20ClosingActionAtAppendLeft name key world error value (MoreTransitions step rest) later (S ordinal) actor exact =
  o20ClosingActionAtAppendLeft name key world error value rest later ordinal actor exact

||| Split a WHOLE indexed Unload into a left occurrence or a right occurrence
||| with its exact physical offset. The right index is computed structurally.
export
0 o20SplitClosingActionAtAppend :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (earlier : Transitions first middle) -> (later : Transitions middle finalState) ->
  (ordinal : Nat) -> (actor : name) ->
  (rawClosingActionAt name key world error value ordinal (appendTransitions earlier later) = Just (LUnload actor)) ->
  Either (rawClosingActionAt name key world error value ordinal earlier = Just (LUnload actor))
    (laterIndex : Nat ** (ordinal = transitionCount earlier + laterIndex,
      rawClosingActionAt name key world error value laterIndex later = Just (LUnload actor)))
o20SplitClosingActionAtAppend name key world error value NoTransitions later ordinal actor exact =
  Right (ordinal ** (Refl, exact))
o20SplitClosingActionAtAppend name key world error value
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest) later Z actor exact = Left exact
o20SplitClosingActionAtAppend name key world error value (MoreTransitions step rest) later (S ordinal) actor exact =
  case o20SplitClosingActionAtAppend name key world error value rest later ordinal actor exact of
    Left earlier => Left earlier
    Right (laterIndex ** (offset, found)) => Right (laterIndex ** (cong S offset, found))

||| Produce the three Unload-exclusion certificates from the actual candidate
||| and the result's OWN generation scans. No segment exclusion is assumed.
export
0 o20DeletionUnloadFreeSegments :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol nameEq keyEq trace) ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq trace) ->
  (result : DeletionResult name key world error value nameEq keyEq trace
    (selectedActor candidate) (selectedEpisode candidate) (selectedRegistrations candidate)
    (selectedStartOrdinal candidate) (selectedStartLive candidate)) ->
  (O20RegisteredUnloadFree name key world error value nameEq (selectedRegistrations candidate) Z []
     (traceBeforeOpening (selectedEpisode candidate)),
   O20RegisteredUnloadFree name key world error value nameEq (selectedRegistrations candidate)
     (selectedStartOrdinal candidate) (selectedStartLive candidate)
     (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate))))
       (closedTransitions (locatedEpisode (selectedEpisode candidate)))),
   O20RegisteredUnloadFree name key world error value nameEq (selectedRegistrations candidate)
     (episodeEndOrdinal result) (episodeEndLive result) (traceAfterClosing (selectedEpisode candidate)))
o20DeletionUnloadFreeSegments name key world error value protocol nameEq keyEq trace premises candidate result =
  case o20RegisteredUnloadSplit nameEq (selectedRegistrations candidate) Z []
    (traceBeforeOpening (selectedEpisode candidate))
    (appendTransitions
      (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate))))
        (closedTransitions (locatedEpisode (selectedEpisode candidate))))
      (traceAfterClosing (selectedEpisode candidate)))
    (selectedStartOrdinal candidate) (selectedStartLive candidate) (beforeGenerationScan result)
    (replace {p = O20RegisteredUnloadFree name key world error value nameEq (selectedRegistrations candidate) Z []}
      (sym (locatedDecomposition (selectedEpisode candidate)))
      (o20DeletionRegisteredUnloadFree name key world error value protocol nameEq keyEq trace premises candidate)) of
    (beforeFree, laterFree) =>
      case o20RegisteredUnloadSplit nameEq (selectedRegistrations candidate)
        (selectedStartOrdinal candidate) (selectedStartLive candidate)
        (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate))))
          (closedTransitions (locatedEpisode (selectedEpisode candidate))))
        (traceAfterClosing (selectedEpisode candidate)) (episodeEndOrdinal result) (episodeEndLive result)
        (episodeGenerationScan result) laterFree of
          (centerFree, afterFree) => (beforeFree, centerFree, afterFree)

||| WHOLE three-segment closing transport. The only unretained alternative
||| identifies the selected parent's center Unload with an EXACT source index.
||| In every other case the target close and its whole native embedding are
||| outputs, including birth/close uses that cross segment boundaries.
export
0 o20WholeClosingIndexRetainedOrSelectedCenter :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol nameEq keyEq trace) ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq trace) ->
  (result : DeletionResult name key world error value nameEq keyEq trace
    (selectedActor candidate) (selectedEpisode candidate) (selectedRegistrations candidate)
    (selectedStartOrdinal candidate) (selectedStartLive candidate)) ->
  (actor : name) -> (sourceIndex : Nat) ->
  (rawClosingActionAt name key world error value sourceIndex trace = Just (LUnload actor)) ->
  Either
    (actor = selectedActor candidate,
     (centerIndex : Nat ** (sourceIndex = deletionOriginalBeforeCount result + centerIndex,
       rawClosingActionAt name key world error value centerIndex
         (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate))))
           (closedTransitions (locatedEpisode (selectedEpisode candidate)))) = Just (LUnload actor))))
    (targetIndex : Nat **
      (rawClosingActionAt name key world error value targetIndex (survivingTrace result) = Just (LUnload actor),
       DeletionSurvivingOrdinalEmbedding result targetIndex sourceIndex))
o20WholeClosingIndexRetainedOrSelectedCenter name key world error value protocol nameEq keyEq trace premises candidate result actor sourceIndex exact =
  case o20DeletionUnloadFreeSegments name key world error value protocol nameEq keyEq trace premises candidate result of
    (beforeFree, centerFree, afterFree) =>
      case o20SplitClosingActionAtAppend name key world error value
        (traceBeforeOpening (selectedEpisode candidate))
        (appendTransitions
          (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate))))
            (closedTransitions (locatedEpisode (selectedEpisode candidate))))
          (traceAfterClosing (selectedEpisode candidate))) sourceIndex actor
        (trans (cong (rawClosingActionAt name key world error value sourceIndex)
          (locatedDecomposition (selectedEpisode candidate))) exact) of
        Left beforeExact =>
          case o20RegisteredSubsequenceUnloadIndex name key world error value nameEq (selectedRegistrations candidate)
            Z [] (beforeDeletion result) beforeFree actor sourceIndex beforeExact of
            (targetIndex ** (targetExact, originExact)) =>
              Right (targetIndex **
                (o20ClosingActionAtAppendLeft name key world error value (survivingBefore result)
                  (appendTransitions (survivingEpisode result) (survivingAfter result)) targetIndex actor targetExact,
                 DeletionBeforeEmbedding originExact))
        Right (laterSource ** (sourceOffset, laterExact)) =>
          case o20SplitClosingActionAtAppend name key world error value
            (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate))))
              (closedTransitions (locatedEpisode (selectedEpisode candidate))))
            (traceAfterClosing (selectedEpisode candidate)) laterSource actor laterExact of
            Left centerExact =>
              case decEq @{nameEq} actor (selectedActor candidate) of
                Yes selected => Left (selected, (laterSource ** (sourceOffset, centerExact)))
                No foreignActor =>
                  case o20ForeignSubsequenceUnloadIndex name key world error value nameEq (selectedActor candidate)
                    (selectedRegistrations candidate) (selectedStartOrdinal candidate) (selectedStartLive candidate)
                    (episodeDeletion result) centerFree actor foreignActor laterSource centerExact of
                    (targetCenter ** (targetExact, originExact)) =>
                      Right (deletionSurvivingBeforeCount result + targetCenter **
                        (trans (o20ClosingActionAtAppend name key world error value (survivingBefore result)
                          (appendTransitions (survivingEpisode result) (survivingAfter result)) targetCenter)
                          (o20ClosingActionAtAppendLeft name key world error value (survivingEpisode result)
                            (survivingAfter result) targetCenter actor targetExact),
                         replace {p = DeletionSurvivingOrdinalEmbedding result (deletionSurvivingBeforeCount result + targetCenter)}
                           (sym sourceOffset) (DeletionEpisodeEmbedding originExact)))
            Right (afterSource ** (afterOffset, afterExact)) =>
              case o20RegisteredSubsequenceUnloadIndex name key world error value nameEq (selectedRegistrations candidate)
                (episodeEndOrdinal result) (episodeEndLive result) (afterDeletion result) afterFree actor afterSource afterExact of
                (targetAfter ** (targetExact, originExact)) =>
                  Right ((deletionSurvivingBeforeCount result + deletionSurvivingEpisodeCount result) + targetAfter **
                    (trans (cong (\index => rawClosingActionAt name key world error value index (survivingTrace result))
                      (sym (plusAssociative (deletionSurvivingBeforeCount result) (deletionSurvivingEpisodeCount result) targetAfter)))
                      (trans (o20ClosingActionAtAppend name key world error value (survivingBefore result)
                        (appendTransitions (survivingEpisode result) (survivingAfter result))
                        (deletionSurvivingEpisodeCount result + targetAfter))
                        (trans (o20ClosingActionAtAppend name key world error value (survivingEpisode result)
                          (survivingAfter result) targetAfter) targetExact)),
                     replace {p = DeletionSurvivingOrdinalEmbedding result
                       ((deletionSurvivingBeforeCount result + deletionSurvivingEpisodeCount result) + targetAfter)}
                       (sym (trans sourceOffset (trans (cong ((deletionOriginalBeforeCount result) +) afterOffset)
                         (plusAssociative (deletionOriginalBeforeCount result) (deletionOriginalEpisodeCount result) afterSource))))
                       (DeletionAfterEmbedding originExact)))

||| Rebase the accounting producer's ACTUAL retained birth to its source
||| generation ordinal, using operational occurrence embedding and the exact
||| generated/action coherence law. No segment assignment is a premise.
export
0 o20DeletionRetainedBirthEmbedding :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol nameEq keyEq trace) ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq trace) ->
  (step : DeletionChainStep name key world error value protocol nameEq keyEq trace premises candidate) ->
  {child, parent : name} -> {component : Component key value world error} ->
  (birth : LocatedGeneratedRegistration child parent component (survivingTrace (deletionResult step))) ->
  (generation : RegistrationGeneration name) ->
  (registrationGeneration (canonicalToOriginal (deletionRegistrationAccounting step) birth) = generation) ->
  DeletionSurvivingOrdinalEmbedding (deletionResult step) (registrationOrdinal birth) (generationBirthOrdinal generation)
o20DeletionRetainedBirthEmbedding {protocol} {nameEq} {keyEq} trace premises candidate step birth generation exact =
  replace {p = DeletionSurvivingOrdinalEmbedding (deletionResult step) (registrationOrdinal birth)}
    (trans (sym (cong locatedActionOrdinal
      (replayGeneratedActionOriginCoherent (deletionOccurrenceCorrespondence step) birth)))
      (cong generationBirthOrdinal
        (trans (sym (cong registrationGeneration (deletionRegistrationOriginExact step birth))) exact)))
    (replace {p = \correspondence => DeletionSurvivingOrdinalEmbedding (deletionResult step)
      (registrationOrdinal birth)
      (locatedActionOrdinal (replayActionOrigin correspondence (generatedRegistrationActionOccurrence birth)))}
      (sym (deletionOccurrenceCorrespondenceExact step))
      (everySurvivingOccurrenceEmbedded
        (deletionStepOperationalOccurrenceFoldSpike nameEq keyEq protocol trace premises candidate
          (deletionResult step) (deletionProducerCapital step))
        (generatedRegistrationActionOccurrence birth)))

||| The actual deletion step produces a retained birth AND its own suffix
||| close across all three segments, except for the explicitly returned
||| selected-parent center close. Its exact source index/order are retained.
export
0 o20DeletionRetainedClosingBirthOrSelectedParent :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol nameEq keyEq trace) ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq trace) ->
  (step : DeletionChainStep name key world error value protocol nameEq keyEq trace premises candidate) ->
  (generation : RegistrationGeneration name) ->
  (classified : DeletedGenerationClassification name key world error value nameEq trace generation) ->
  Not (Elem generation (selectedRegistrations candidate)) ->
  Either
    (sourceClose : Nat **
      (LT (registrationOrdinal (deletedOccurrence classified)) sourceClose,
       deletedParent classified = selectedActor candidate,
       (centerIndex : Nat **
         (sourceClose = deletionOriginalBeforeCount (deletionResult step) + centerIndex,
          rawClosingActionAt name key world error value centerIndex
            (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate))))
              (closedTransitions (locatedEpisode (selectedEpisode candidate)))) = Just (LUnload (deletedParent classified))))))
    (birth : LocatedGeneratedRegistration (generationName generation) (deletedParent classified)
      (deletedComponent classified) (survivingTrace (deletionResult step)) **
      (generationForward (deletionProducerGenerationRenaming (deletionProducerCapital step)) generation = registrationGeneration birth,
       ActionOccurs (LUnload (deletedParent classified)) (afterRegistration birth)))
o20DeletionRetainedClosingBirthOrSelectedParent name key world error value protocol nameEq keyEq trace premises candidate step generation classified outside =
  case originalRegistrationAccounted (deletionRegistrationAccounting step) (deletedOccurrence classified) of
    Left selected => void (outside
      (replace {p = Elem generation} (deletionWithdrawnGenerationsExact step)
        (replace {p = \stamp => Elem stamp (endpointWithdrawnGenerations (deletionEndpoint step))}
          (deletedOccurrenceGeneration classified) selected)))
    Right (birth ** originalExact) =>
      case o20DeletedBirthClosingIndex name key world error value nameEq trace generation classified of
        (sourceClose ** (sourceOrder, sourceExact)) =>
          case o20WholeClosingIndexRetainedOrSelectedCenter name key world error value protocol nameEq keyEq
            trace premises candidate (deletionResult step) (deletedParent classified) sourceClose sourceExact of
            Left (selected, (centerIndex ** (centerOffset, centerExact))) =>
              Left (sourceClose ** (sourceOrder, selected, (centerIndex ** (centerOffset, centerExact))))
            Right (targetClose ** (targetExact, closeEmbedding)) =>
              Right (birth **
                (o20DeletionRetainedBirthGeneration trace premises candidate step birth generation
                  (trans originalExact (deletedOccurrenceGeneration classified)),
                 o20UnloadBeyondBirthCut name key world error value (beforeRegistration birth)
                   (registrationTransition birth) (afterRegistration birth) targetClose (deletedParent classified)
                   (o20WholeEmbeddingReflectsSourceOrder (deletionResult step)
                     (registrationOrdinal birth) targetClose (registrationOrdinal (deletedOccurrence classified)) sourceClose
                     (o20DeletionRetainedBirthEmbedding trace premises candidate step birth
                       (registrationGeneration (deletedOccurrence classified)) originalExact)
                     closeEmbedding sourceOrder)
                   (trans (cong (rawClosingActionAt name key world error value targetClose)
                     (registrationDecomposition birth)) targetExact)))

||| Reassociating an exact trace or rewriting an action equality does not
||| change a located occurrence's physical ordinal. Both transports are named.
export
0 o20LocatedOrdinalTransport :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (source, target : Transitions first finalState) ->
  (sourceAction, targetAction : Action name key value world error) ->
  (traceExact : source = target) -> (actionExact : sourceAction = targetAction) ->
  (occurrence : LocatedActionOccurrence sourceAction source) ->
  (locatedActionOrdinal
    (replace {p = \action => LocatedActionOccurrence action target} actionExact
      (replace {p = LocatedActionOccurrence sourceAction} traceExact occurrence)) =
    locatedActionOrdinal occurrence)
o20LocatedOrdinalTransport source _ sourceAction _ Refl Refl occurrence = Refl

||| A successful physical action observation is strictly inside its trace.
||| Used to rule out an after-segment birth preceding a center-segment close.
export
0 o20ClosingIndexInsideTrace :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> (ordinal : Nat) ->
  (action : Action name key value world error) ->
  (rawClosingActionAt name key world error value ordinal trace = Just action) ->
  LT ordinal (transitionCount trace)
o20ClosingIndexInsideTrace name key world error value NoTransitions ordinal action exact = absurd exact
o20ClosingIndexInsideTrace name key world error value (MoreTransitions step rest) Z action exact = LTESucc LTEZero
o20ClosingIndexInsideTrace name key world error value (MoreTransitions step rest) (S ordinal) action exact =
  LTESucc (o20ClosingIndexInsideTrace name key world error value rest ordinal action exact)

||| The removed-center exception LOCATES the nonselected birth in BEFORE.
||| Center is impossible by registered-during completeness (R202 B2); after
||| is impossible by the actual center closing bound. No location is assumed.
export
0 o20SelectedCenterCloseBirthBefore :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq trace) ->
  (generation : RegistrationGeneration name) ->
  (classified : DeletedGenerationClassification name key world error value nameEq trace generation) ->
  Not (Elem generation (selectedRegistrations candidate)) ->
  (deletedParent classified = selectedActor candidate) ->
  (centerIndex : Nat) ->
  LT (registrationOrdinal (deletedOccurrence classified)) (transitionCount (traceBeforeOpening (selectedEpisode candidate)) + centerIndex) ->
  (rawClosingActionAt name key world error value centerIndex (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate)))) (closedTransitions (locatedEpisode (selectedEpisode candidate)))) = Just (LUnload (deletedParent classified))) ->
  (localBirth : LocatedActionOccurrence (OInsert (generationName generation) (ChildOf (deletedParent classified)) (deletedComponent classified)) (traceBeforeOpening (selectedEpisode candidate)) **
    (registrationOrdinal (deletedOccurrence classified) = locatedActionOrdinal localBirth))
o20SelectedCenterCloseBirthBefore name key world error value nameEq keyEq trace candidate generation classified outside parentExact centerIndex ordered centerExact =
  case deletionWholeTraceOccurrenceClassification (traceBeforeOpening (selectedEpisode candidate)) (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate)))) (closedTransitions (locatedEpisode (selectedEpisode candidate)))) (traceAfterClosing (selectedEpisode candidate))
    (replace {p = LocatedActionOccurrence (OInsert (generationName generation) (ChildOf (deletedParent classified)) (deletedComponent classified))} (sym (locatedDecomposition (selectedEpisode candidate))) (generatedRegistrationActionOccurrence (deletedOccurrence classified))) of
    DeletionWholeBefore localBirth exactOrdinal =>
      (localBirth ** trans (sym (o20LocatedOrdinalTransport trace (appendTransitions (traceBeforeOpening (selectedEpisode candidate)) (appendTransitions (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate)))) (closedTransitions (locatedEpisode (selectedEpisode candidate)))) (traceAfterClosing (selectedEpisode candidate)))) (OInsert (generationName generation) (ChildOf (deletedParent classified)) (deletedComponent classified)) (OInsert (generationName generation) (ChildOf (deletedParent classified)) (deletedComponent classified)) (sym (locatedDecomposition (selectedEpisode candidate))) Refl (generatedRegistrationActionOccurrence (deletedOccurrence classified)))) exactOrdinal)
    DeletionWholeEpisode localBirth exactOrdinal =>
      void (o20SelectedCenterBirthContradictsNonselection trace candidate generation classified outside
        (replace {p = \action => LocatedActionOccurrence action (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate)))) (closedTransitions (locatedEpisode (selectedEpisode candidate))))} (cong (\parent => OInsert (generationName generation) (ChildOf parent) (deletedComponent classified)) parentExact) localBirth)
        (cong (MkRegistrationGeneration (generationName generation))
          (trans (sym (o20LocatedOrdinalTransport trace (appendTransitions (traceBeforeOpening (selectedEpisode candidate)) (appendTransitions (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate)))) (closedTransitions (locatedEpisode (selectedEpisode candidate)))) (traceAfterClosing (selectedEpisode candidate)))) (OInsert (generationName generation) (ChildOf (deletedParent classified)) (deletedComponent classified)) (OInsert (generationName generation) (ChildOf (deletedParent classified)) (deletedComponent classified)) (sym (locatedDecomposition (selectedEpisode candidate))) Refl (generatedRegistrationActionOccurrence (deletedOccurrence classified))))
            (trans exactOrdinal
              (trans (cong (\count => count + locatedActionOrdinal localBirth)
                (sym (o20NativeScanCount (selectedBeforeScan candidate))))
                (cong ((selectedStartOrdinal candidate) +) (sym (o20LocatedOrdinalTransport (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate)))) (closedTransitions (locatedEpisode (selectedEpisode candidate)))) (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate)))) (closedTransitions (locatedEpisode (selectedEpisode candidate)))) (OInsert (generationName generation) (ChildOf (deletedParent classified)) (deletedComponent classified)) (OInsert (generationName generation) (ChildOf (selectedActor candidate)) (deletedComponent classified)) Refl (cong (\parent => OInsert (generationName generation) (ChildOf parent) (deletedComponent classified)) parentExact) localBirth))))))))
    DeletionWholeAfter localBirth exactOrdinal =>
      void (succNotLTEpred (transitive
        (transitive
          (replace {p = \index => LT index (transitionCount (traceBeforeOpening (selectedEpisode candidate)) + centerIndex)}
            (trans (sym (o20LocatedOrdinalTransport trace (appendTransitions (traceBeforeOpening (selectedEpisode candidate)) (appendTransitions (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate)))) (closedTransitions (locatedEpisode (selectedEpisode candidate)))) (traceAfterClosing (selectedEpisode candidate)))) (OInsert (generationName generation) (ChildOf (deletedParent classified)) (deletedComponent classified)) (OInsert (generationName generation) (ChildOf (deletedParent classified)) (deletedComponent classified)) (sym (locatedDecomposition (selectedEpisode candidate))) Refl (generatedRegistrationActionOccurrence (deletedOccurrence classified)))) exactOrdinal) ordered)
          (lteSuccLeft (fst (o20OffsetStrictOrder (transitionCount (traceBeforeOpening (selectedEpisode candidate))) centerIndex (transitionCount (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate)))) (closedTransitions (locatedEpisode (selectedEpisode candidate))))))
            (o20ClosingIndexInsideTrace name key world error value (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate)))) (closedTransitions (locatedEpisode (selectedEpisode candidate)))) centerIndex (LUnload (deletedParent classified)) centerExact))))
        (lteAddRight (transitionCount (traceBeforeOpening (selectedEpisode candidate)) + transitionCount (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate)))) (closedTransitions (locatedEpisode (selectedEpisode candidate))))))))

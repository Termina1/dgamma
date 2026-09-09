module DGamma.CP5O20OwnCutSafetySpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O19BodyMetadataSpike
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5O20BlockResolverFrameSpike
import DGamma.CP5O20BeginObservationSpike
import DGamma.CP5O20RightOpeningTransportSpike
import DGamma.CP5O20SupportedReferenceSpike
import DGamma.CP5O20InversionChildSafetySpike
import DGamma.CP5O20ReferenceDescentSpike
import DGamma.CP5O20SafeBlockSelectionSpike
import DGamma.CP5O20SelectionCompletenessSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Attach any actual replay cut's present component to the ORIGINAL fixed
||| endpoint. Compose the two authentic occurrence origins; raw uniqueness and
||| the native birth invariant supply metadata, not an endpoint equation input.
export
0 o20ReplayCutReferenceComponent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal, reachedFinal, current : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (replayed : Transitions initial reachedFinal) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq replayed ->
  ActionRegistrationReplayCorrespondence name key world error value (canonicalTrace (canonicalSchedule capital)) replayed ->
  (earlier : Transitions initial current) -> (later : Transitions current reachedFinal) ->
  (appendTransitions earlier later = replayed) ->
  (actor : name) -> (referenceFiber, currentFiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry originalFinal) = Just referenceFiber) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry current) = Just currentFiber) ->
  (fiberComponent currentFiber = fiberComponent referenceFiber)
o20ReplayCutReferenceComponent {name} {key} {world} {error} {value} nameEq keyEq protocol original capital unique replayed premises occurrences
  earlier later exact actor referenceFiber currentFiber referenceFound currentFound =
    sym (cong snd (o19ReplayedCutMetadata nameEq keyEq protocol original replayed
      original NoTransitions (currentBirthTraceAppendEmpty name key world error value original)
      earlier later exact (chainReplayCapital (capitalPremises capital)) premises unique
      (composeActionRegistrationReplayCorrespondence (canonicalOccurrenceCorrespondence capital) occurrences)
      actor referenceFiber currentFiber referenceFound currentFound))

||| First missing E60 attachment: the ACTUAL block-end fiber's component is
||| the original reference component. The block owns its exact physical cut
||| decomposition; no per-cut metadata equality is assumed.
export
0 o20BlockEndReferenceComponent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal, reachedFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (replayed : Transitions initial reachedFinal) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq replayed ->
  ActionRegistrationReplayCorrespondence name key world error value (canonicalTrace (canonicalSchedule capital)) replayed ->
  (actor : name) ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq actor replayed) ->
  (referenceFiber, lastFiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry originalFinal) = Just referenceFiber) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry (blockEnd block)) = Just lastFiber) ->
  (fiberComponent lastFiber = fiberComponent referenceFiber)
o20BlockEndReferenceComponent nameEq keyEq protocol original capital unique replayed premises occurrences actor block
  referenceFiber lastFiber referenceFound lastFound =
    o20ReplayCutReferenceComponent nameEq keyEq protocol original capital unique replayed premises occurrences
      (prefixThroughBlock block) (traceAfterBlock block)
      (trans (appendTransitionsAssociative (prefixToBlockOpening block) (blockBody block) (traceAfterBlock block))
        (trans (appendTransitionsAssociative (traceBeforeBlock block) (MoreTransitions (beginTransition (blockOpening block)) NoTransitions)
          (appendTransitions (blockBody block) (traceAfterBlock block))) (blockDecomposition block)))
      actor referenceFiber lastFiber referenceFound lastFound

||| Second missing E60 attachment: the actual right opening observation has
||| the original reference component. Its primitive source lookup and the
||| block's exact preceding trace own the proof; no resolver frame is input.
export
0 o20BlockOpeningReferenceComponent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal, reachedFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (replayed : Transitions initial reachedFinal) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq replayed ->
  ActionRegistrationReplayCorrespondence name key world error value (canonicalTrace (canonicalSchedule capital)) replayed ->
  (actor : name) ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq actor replayed) ->
  (referenceFiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry originalFinal) = Just referenceFiber) ->
  (observed : O20BeginObservation name key world error value nameEq keyEq actor (blockPreStart block) (blockStart block)) ->
  (beginObservedComponent observed = fiberComponent referenceFiber)
o20BlockOpeningReferenceComponent nameEq keyEq protocol original capital unique replayed premises occurrences actor block
  referenceFiber referenceFound observed =
    o20ReplayCutReferenceComponent nameEq keyEq protocol original capital unique replayed premises occurrences
      (traceBeforeBlock block)
      (MoreTransitions (beginTransition (blockOpening block)) (appendTransitions (blockBody block) (traceAfterBlock block)))
      (blockDecomposition block) actor referenceFiber
      (MkFiber (beginObservedComponent observed) (beginObservedParent observed) False (beginObservedTable observed) (Inactive Nothing))
      referenceFound (beginObservedFound observed)

||| InstalledTrace includes the ACTUAL endpoint, including an empty body.
||| Expose that endpoint clause by structural induction, not presence guessing.
export
0 o20InstalledTraceEnd :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {actor : name} ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  InstalledTrace name key world error value nameEq keyEq actor trace ->
  (installedAt {name} {key} {value} {world} {error} @{nameEq} actor finalState = True)
o20InstalledTraceEnd NoTransitions (InstalledEnd installed) = installed
o20InstalledTraceEnd _ (InstalledStep action tag checked rest installed tailInstalled) =
  o20InstalledTraceEnd rest tailInstalled

||| One primitive present-fiber observation, with its fiber erased because
||| only erased safety proofs consume it. It stores no component attachment,
||| target guard or resolver preservation conclusion.
public export
record O20PresentLookup
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (actor : name) (state : SystemState name key value world error) where
  constructor MkO20PresentLookup
  0 presentFiber : Fiber name key value world error
  0 presentFound : (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry state) = Just presentFiber)

||| Decode one explicitly observed primitive lookup. The absent branch is
||| refuted by the supplied native nonabsence proof; no computed existential
||| is locally eliminated or reconstructed.
export
0 o20PresentLookupObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) -> (state : SystemState name key value world error) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry state) = observed) ->
  Not (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry state) = Nothing) ->
  O20PresentLookup name key world error value nameEq actor state
o20PresentLookupObserved nameEq actor state Nothing found notAbsent = void (notAbsent found)
o20PresentLookupObserved nameEq actor state (Just fiber) found notAbsent = MkO20PresentLookup fiber found

||| An ACTUAL installed segment produces its endpoint lookup observation.
||| End installedness and the primitive lookup rule out absence internally.
export
0 o20InstalledEndPresentLookup :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  InstalledTrace name key world error value nameEq keyEq actor trace ->
  O20PresentLookup name key world error value nameEq actor finalState
o20InstalledEndPresentLookup {name} {key} {world} {error} {value} {finalState} nameEq keyEq actor trace installed =
  o20PresentLookupObserved nameEq actor finalState
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry finalState)) Refl
    (\absent => absurd (trans (sym (the (installedAt {name} {key} {value} {world} {error} @{nameEq} actor finalState = False)
      (rewrite absent in Refl))) (o20InstalledTraceEnd trace installed)))

||| Original supportedness produces the fixed-reference lookup by the accepted
||| support/Active theorem. No original fiber or presence premise is supplied.
export
0 o20OriginalSupportedLookup :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  (actor : name) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} actor originalFinal = True) ->
  O20PresentLookup name key world error value nameEq actor originalFinal
o20OriginalSupportedLookup {name} {key} {world} {error} {value} {originalFinal} nameEq keyEq protocol original capital actor supported =
  o20PresentLookupObserved nameEq actor originalFinal
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry originalFinal)) Refl
    (\absent => absurd (trans (sym (the (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} actor originalFinal = False)
      (rewrite absent in Refl)))
      (trans (sym (replaySupportMatchesActive (chainReplayCapital (capitalPremises capital)) actor)) supported)))

||| Actual earlier right Begin with BOTH former endpoint attachments produced.
||| The three lookup packets are explicit observations at this helper boundary;
||| B7/B8 produce them. Zero gap and child exclusion remain physical inputs.
export
0 o20ReferenceEarlierBeginObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal, reachedFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (replayed : Transitions initial reachedFinal) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq replayed) ->
  (occurrences : ActionRegistrationReplayCorrespondence name key world error value (canonicalTrace (canonicalSchedule capital)) replayed) ->
  (left, right : name) -> Not (right = left) ->
  (leftBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq left replayed) ->
  (rightBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq right replayed) ->
  (ordered : BlockBefore name key world error value nameEq keyEq replayed left right leftBlock rightBlock) ->
  NoGeneratedChild right (blockBody leftBlock) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} left originalFinal = True) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} right originalFinal = True) ->
  Not (O20SupportedPath name key world error value nameEq keyEq originalFinal left right) ->
  ZeroGapPending (betweenBlocks ordered) ->
  (leftSeen : O20PresentLookup name key world error value nameEq left originalFinal) ->
  (rightSeen : O20PresentLookup name key world error value nameEq right originalFinal) ->
  (lastSeen : O20PresentLookup name key world error value nameEq left (blockEnd leftBlock)) ->
  CheckedEarlyApplication name key world error value nameEq keyEq (blockPreStart leftBlock) (LBegin right) LBeginTag
o20ReferenceEarlierBeginObserved {name} {key} {world} {error} {value} {originalFinal} nameEq keyEq protocol original capital unique replayed premises occurrences
  left right distinct leftBlock rightBlock ordered excluded leftSupported rightSupported noPath empty leftSeen rightSeen lastSeen =
    o20IncomparableInstalledEarlierBegin nameEq keyEq left right distinct originalFinal (presentFiber leftSeen) (presentFiber rightSeen)
      (blockPreStart leftBlock) (blockStart leftBlock) (blockEnd leftBlock) (blockPreStart rightBlock) (blockStart rightBlock)
      (blockOpening leftBlock) (blockOpening rightBlock) (blockBody leftBlock) (blockBodyInstalled leftBlock) (blockActorOnly leftBlock)
      excluded (betweenBlocks ordered) empty
      (alignedTraceWellFormedEnd nameEq keyEq (traceBeforeBlock leftBlock)
        (fst (alignedAppendSplit (traceBeforeBlock leftBlock)
          (MoreTransitions (beginTransition (blockOpening leftBlock)) (appendTransitions (blockBody leftBlock) (traceAfterBlock leftBlock)))
          (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym (blockDecomposition leftBlock)) (replayAligned premises))))
        (replayInitialWellFormed premises))
      (presentFiber lastSeen) (presentFound lastSeen)
      (o20BlockEndReferenceComponent nameEq keyEq protocol original capital unique replayed premises occurrences left leftBlock
        (presentFiber leftSeen) (presentFiber lastSeen) (presentFound leftSeen) (presentFound lastSeen))
      (o20BlockOpeningReferenceComponent nameEq keyEq protocol original capital unique replayed premises occurrences right rightBlock
        (presentFiber rightSeen) (presentFound rightSeen)
        (o20ObserveActualBegin nameEq keyEq right (blockPreStart rightBlock) (blockStart rightBlock) (blockOpening rightBlock)))
      (presentFound leftSeen) (presentFound rightSeen) leftSupported rightSupported noPath

||| The selected inversion's right Begin is safe at its OWN native left slot.
||| Accepted reference/operational capital produces child exclusion, support,
||| source well-formedness, all three lookups and both component attachments.
||| The ONLY remaining physical safety hypothesis is literal ZeroGapPending.
export
0 o20ReachedInversionEarlierBegin :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal, reachedFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  {reachedOrder, goalOrder, swappedOrder : List name} ->
  (originalReference : O20SupportedReferenceOrders name key world error value nameEq keyEq originalFinal (supportOrder (canonicalSchedule capital)) goalOrder) ->
  (reachedReference : O20SupportedReferenceOrders name key world error value nameEq keyEq originalFinal reachedOrder goalOrder) ->
  (replayed : Transitions initial reachedFinal) ->
  {certificate : CertifiedActorPermutation name (supportOrder (canonicalSchedule capital)) reachedOrder} ->
  (operational : OperationalActorPermutation name key world error value protocol nameEq keyEq certificate
    (canonicalTrace (canonicalSchedule capital)) (canonicalActorBlockDecomposition capital) (canonicalReplayPremises capital) replayed) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq reachedOrder replayed) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq replayed) ->
  (swap : AdjacentActorOrderSwap name reachedOrder swappedOrder) ->
  BeforeIn (actorRight swap) (actorLeft swap) goalOrder ->
  ZeroGapPending (betweenBlocks (decomposedBlocksFollowOrder blocks (actorLeft swap) (actorRight swap)
    (fst (o20ChosenActorFacts swap)) (fst (snd (o20ChosenActorFacts swap))) (snd (snd (o20ChosenActorFacts swap))))) ->
  CheckedEarlyApplication name key world error value nameEq keyEq
    (blockPreStart (decomposedBlock blocks (actorLeft swap) (fst (o20ChosenActorFacts swap)))) (LBegin (actorRight swap)) LBeginTag
o20ReachedInversionEarlierBegin nameEq keyEq protocol original capital unique originalReference reachedReference replayed operational blocks premises swap reverseGoal empty =
  o20ReferenceEarlierBeginObserved nameEq keyEq protocol original capital unique replayed premises
    (operationalPermutationOccurrenceCorrespondence operational) (actorLeft swap) (actorRight swap) (\same => actorDistinct swap (sym same))
    (decomposedBlock blocks (actorLeft swap) (fst (o20ChosenActorFacts swap)))
    (decomposedBlock blocks (actorRight swap) (fst (snd (o20ChosenActorFacts swap))))
    (decomposedBlocksFollowOrder blocks (actorLeft swap) (actorRight swap)
      (fst (o20ChosenActorFacts swap)) (fst (snd (o20ChosenActorFacts swap))) (snd (snd (o20ChosenActorFacts swap))))
    (fst (o20ReachedInversionChildSafety nameEq keyEq protocol original capital unique originalReference reachedReference replayed operational blocks swap reverseGoal))
    (o20ReachedReferenceSupport capital originalReference reachedReference (actorLeft swap) (fst (o20ChosenActorFacts swap)))
    (o20ReachedReferenceSupport capital originalReference reachedReference (actorRight swap) (fst (snd (o20ChosenActorFacts swap))))
    (fst (o20ReferenceIncomparable swap reachedReference reverseGoal)) empty
    (o20OriginalSupportedLookup nameEq keyEq protocol original capital (actorLeft swap)
      (o20ReachedReferenceSupport capital originalReference reachedReference (actorLeft swap) (fst (o20ChosenActorFacts swap))))
    (o20OriginalSupportedLookup nameEq keyEq protocol original capital (actorRight swap)
      (o20ReachedReferenceSupport capital originalReference reachedReference (actorRight swap) (fst (snd (o20ChosenActorFacts swap)))))
    (o20InstalledEndPresentLookup nameEq keyEq (actorLeft swap)
      (blockBody (decomposedBlock blocks (actorLeft swap) (fst (o20ChosenActorFacts swap))))
      (blockBodyInstalled (decomposedBlock blocks (actorLeft swap) (fst (o20ChosenActorFacts swap)))))

||| Full native OWN-CUT safety test for an actual selected reached inversion.
||| All semantic clauses are produced; only literal ZeroGapPending remains.
||| This proves the native check succeeds, without fabricating a chosen payload.
export
0 o20ReachedInversionOwnCutSafe :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal, reachedFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  {reachedOrder, goalOrder, swappedOrder : List name} ->
  O20SupportedReferenceOrders name key world error value nameEq keyEq originalFinal (supportOrder (canonicalSchedule capital)) goalOrder ->
  O20SupportedReferenceOrders name key world error value nameEq keyEq originalFinal reachedOrder goalOrder ->
  (replayed : Transitions initial reachedFinal) ->
  {certificate : CertifiedActorPermutation name (supportOrder (canonicalSchedule capital)) reachedOrder} ->
  (operational : OperationalActorPermutation name key world error value protocol nameEq keyEq certificate
    (canonicalTrace (canonicalSchedule capital)) (canonicalActorBlockDecomposition capital) (canonicalReplayPremises capital) replayed) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq reachedOrder replayed) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq replayed) ->
  (replayedUnique : UniqueRawNameInsertions name key world error value nameEq keyEq replayed) ->
  (swap : AdjacentActorOrderSwap name reachedOrder swappedOrder) ->
  BeforeIn (actorRight swap) (actorLeft swap) goalOrder ->
  ZeroGapPending (betweenBlocks (decomposedBlocksFollowOrder blocks (actorLeft swap) (actorRight swap)
    (fst (o20ChosenActorFacts swap)) (fst (snd (o20ChosenActorFacts swap))) (snd (snd (o20ChosenActorFacts swap))))) ->
  (isJust (o20CheckCandidate nameEq keyEq protocol reachedOrder replayed blocks premises replayedUnique (swappedOrder ** swap)) = True)
o20ReachedInversionOwnCutSafe {reachedOrder} {swappedOrder} nameEq keyEq protocol original capital unique originalReference reachedReference
  replayed operational blocks premises replayedUnique swap reverseGoal empty =
    o20CandidateCompleteAtOwnSlots nameEq keyEq protocol reachedOrder swappedOrder swap replayed blocks premises replayedUnique
      (fst (o20ReachedInversionChildSafety nameEq keyEq protocol original capital unique originalReference reachedReference replayed operational blocks swap reverseGoal))
      (snd (o20ReachedInversionChildSafety nameEq keyEq protocol original capital unique originalReference reachedReference replayed operational blocks swap reverseGoal))
      (o20ReachedInversionEarlierBegin nameEq keyEq protocol original capital unique originalReference reachedReference replayed operational blocks premises swap reverseGoal empty)
      empty

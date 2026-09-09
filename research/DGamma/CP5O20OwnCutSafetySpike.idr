module DGamma.CP5O20OwnCutSafetySpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
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

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

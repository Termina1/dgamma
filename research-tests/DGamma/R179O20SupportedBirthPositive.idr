module DGamma.R179O20SupportedBirthPositive

import DGamma.Calculus
import DGamma.CP5O20SupportedBirthBridgeSpike
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5AllSupportedMetadataSpike
import DGamma.CP5AcceptedSupportTruthSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O21EndpointIdentitySpike
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Positive conditional consumer: producer-owned supported replay birth clause
||| AND canonical right-stamp uniqueness, with the same fixed child/parent.
export
0 r179SupportedReplayedBirthUnique :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal, replayedFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq left) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq right) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  GeneratedOrchestrationMatched name key world error value nameEq left right (generatedGenerationBijection sameInputs) ->
  (replayed : Transitions initial replayedFinal) ->
  (occurrences : ActionRegistrationReplayCorrespondence name key world error value
    (canonicalTrace (canonicalSchedule leftCapital)) replayed) ->
  (selected, parent : name) -> (component : Component key value world error) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} @{keyEq} selected leftFinal = True) ->
  (replayedBirth : LocatedGeneratedRegistration selected parent component replayed) ->
  (sourceOccurrence : LocatedGeneratedRegistration selected parent component (canonicalTrace (canonicalSchedule leftCapital)) **
    (sourceOccurrence = replayGeneratedRegistrationOrigin occurrences replayedBirth,
     (rightBirth : LocatedGeneratedRegistration (renameForward (expectedBridgeBijection sameInputs) selected)
       (renameForward (expectedBridgeBijection sameInputs) parent) component (canonicalTrace (canonicalSchedule rightCapital)) **
       ((generationForward (generatedGenerationBijection sameInputs)
         (registrationGeneration (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence leftCapital) sourceOccurrence)) =
         registrationGeneration (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence rightCapital) rightBirth)),
        ((candidate : LocatedGeneratedRegistration (renameForward (expectedBridgeBijection sameInputs) selected)
          (renameForward (expectedBridgeBijection sameInputs) parent) component (canonicalTrace (canonicalSchedule rightCapital))) ->
          registrationGeneration rightBirth = registrationGeneration candidate)))))
r179SupportedReplayedBirthUnique name key world error value nameEq keyEq protocol left right sameInputs leftCapital rightCapital
  leftUnique rightUnique matched replayed occurrences selected parent component supported replayedBirth =
    case supportedReplayedBirthBridge name key world error value nameEq keyEq protocol left right sameInputs leftCapital rightCapital
      leftUnique rightUnique matched replayed occurrences selected parent component supported replayedBirth of
      (sourceOccurrence ** (sourceExact, (rightBirth ** triangle))) =>
        (sourceOccurrence ** (sourceExact, (rightBirth ** (triangle,
          canonicalGeneratedBirthStampUnique name key world error value nameEq keyEq protocol right rightCapital rightUnique
            (renameForward (expectedBridgeBijection sameInputs) selected) (renameForward (expectedBridgeBijection sameInputs) parent) component rightBirth))))

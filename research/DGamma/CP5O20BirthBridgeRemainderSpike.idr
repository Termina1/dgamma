module DGamma.CP5O20BirthBridgeRemainderSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20SupportedBirthBridgeSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| Honest fourth-clause result indexed by the ACTUAL original child support.
||| The matched payload is the exact canonical/replay origin packet, unchanged.
||| False carries an explicit unresolved branch, NOT an invented opposite birth,
||| not proof of impossibility, and not a fallback claimed to close O20.
public export
data O20BirthBridgeAttempt : Bool -> Type -> Type where
  O20UnsupportedBirth : {matched : Type} -> O20BirthBridgeAttempt False matched
  O20MatchedBirth : {matched : Type} -> (0 evidence : matched) -> O20BirthBridgeAttempt True matched

||| Observe only the ACTUAL support Bool. True uses the authentic supported
||| replay bridge wholesale; False keeps the unsupported-child remainder exact.
||| No computed dependent packet is eliminated or reconstructed here.
export
0 o20BirthBridgeObserved :
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
  (observedSupport : Bool) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} selected leftFinal = observedSupport) ->
  (replayedBirth : LocatedGeneratedRegistration selected parent component replayed) ->
  O20BirthBridgeAttempt (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} selected leftFinal)
    ((sourceOccurrence : LocatedGeneratedRegistration selected parent component (canonicalTrace (canonicalSchedule leftCapital)) **
    (sourceOccurrence = replayGeneratedRegistrationOrigin occurrences replayedBirth,
     (rightBirth : LocatedGeneratedRegistration (renameForward (expectedBridgeBijection sameInputs) selected)
       (renameForward (expectedBridgeBijection sameInputs) parent) component (canonicalTrace (canonicalSchedule rightCapital)) **
       generationForward (generatedGenerationBijection sameInputs)
         (registrationGeneration (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence leftCapital) sourceOccurrence)) =
       registrationGeneration (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence rightCapital) rightBirth)))))
o20BirthBridgeObserved name key world error value nameEq keyEq protocol left right sameInputs leftCapital rightCapital
  leftUnique rightUnique matched replayed occurrences selected parent component False observed replayedBirth =
    rewrite observed in O20UnsupportedBirth
o20BirthBridgeObserved name key world error value nameEq keyEq protocol left right sameInputs leftCapital rightCapital
  leftUnique rightUnique matched replayed occurrences selected parent component True observed replayedBirth =
    rewrite observed in O20MatchedBirth
      (supportedReplayedBirthBridge name key world error value nameEq keyEq protocol left right sameInputs leftCapital rightCapital
        leftUnique rightUnique matched replayed occurrences selected parent component observed replayedBirth)

||| Accept ANY actual replayed generated birth. Compute original child support
||| here; no support oracle is an input. This produces the existing full fourth
||| clause precisely when supported, and explicitly reports the remaining case.
export
0 o20ClassifyReplayedBirth :
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
  (replayedBirth : LocatedGeneratedRegistration selected parent component replayed) ->
  O20BirthBridgeAttempt (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} selected leftFinal)
    ((sourceOccurrence : LocatedGeneratedRegistration selected parent component (canonicalTrace (canonicalSchedule leftCapital)) **
    (sourceOccurrence = replayGeneratedRegistrationOrigin occurrences replayedBirth,
     (rightBirth : LocatedGeneratedRegistration (renameForward (expectedBridgeBijection sameInputs) selected)
       (renameForward (expectedBridgeBijection sameInputs) parent) component (canonicalTrace (canonicalSchedule rightCapital)) **
       generationForward (generatedGenerationBijection sameInputs)
         (registrationGeneration (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence leftCapital) sourceOccurrence)) =
       registrationGeneration (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence rightCapital) rightBirth)))))
o20ClassifyReplayedBirth name key world error value nameEq keyEq protocol {leftFinal} left right sameInputs leftCapital rightCapital
  leftUnique rightUnique matched replayed occurrences selected parent component replayedBirth =
    o20BirthBridgeObserved name key world error value nameEq keyEq protocol left right sameInputs leftCapital rightCapital
      leftUnique rightUnique matched replayed occurrences selected parent component
      (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} selected leftFinal) Refl replayedBirth

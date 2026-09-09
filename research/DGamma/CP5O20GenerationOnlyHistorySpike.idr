module DGamma.CP5O20GenerationOnlyHistorySpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5SupportedBirthCoverageSpike
import DGamma.CP5O20CanonicalBirthDispositionSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5UniqueRawNameInsertions
import Data.List
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Original-history birth disposition with no current-name or opposite-
||| canonical occurrence claim. Closing keeps its actual scanner birth and
||| deletion evidence; matching keeps BOTH original births and the exact
||| generation equation. All constructor witnesses are erased.
public export
data O20GenerationOnlyDisposition :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (mapping : RegistrationGenerationBijection name) ->
  (left : Transitions leftFirst leftFinal) ->
  (right : Transitions rightFirst rightFinal) ->
  (stamp : RegistrationGeneration name) -> Type where
  O20OriginalClosingBirth :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
    {mapping : RegistrationGenerationBijection name} ->
    {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
    {stamp : RegistrationGeneration name} ->
    (0 event : RegistrationEvent name key world error value) ->
    (0 birth : ScannedRegistrationBirth name key world error value Z left event) ->
    (0 exact : (eventChildGeneration event = stamp)) ->
    (0 closing : DeletedClosingRegistration event (afterActionOccurrence (scannedLocatedBirth birth))) ->
    O20GenerationOnlyDisposition name key world error value mapping left right stamp
  O20OriginalMatchedBirth :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
    {mapping : RegistrationGenerationBijection name} ->
    {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
    {stamp : RegistrationGeneration name} ->
    (0 event, opposite : RegistrationEvent name key world error value) ->
    (0 leftBirth : ScannedRegistrationBirth name key world error value Z left event) ->
    (0 rightBirth : ScannedRegistrationBirth name key world error value Z right opposite) ->
    (0 exact : (eventChildGeneration event = stamp)) ->
    (0 matched : RegistrationEventMatch mapping event opposite) ->
    (0 stampMatched : (generationForward mapping stamp = eventChildGeneration opposite)) ->
    O20GenerationOnlyDisposition name key world error value mapping left right stamp

||| Eliminate the one authentic opposite ORIGINAL birth packet, retaining
||| its very same event and scanned occurrence in the matched constructor.
export
0 o20MatchedDispositionPacket :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  (mapping : RegistrationGenerationBijection name) ->
  (stamp : RegistrationGeneration name) ->
  (event : RegistrationEvent name key world error value) ->
  (birth : ScannedRegistrationBirth name key world error value Z left event) ->
  (eventChildGeneration event = stamp) ->
  (opposite : RegistrationEvent name key world error value **
    (RegistrationEventMatch mapping event opposite,
     ScannedRegistrationBirth name key world error value Z right opposite,
     (generationForward mapping stamp = eventChildGeneration opposite))) ->
  O20GenerationOnlyDisposition name key world error value mapping left right stamp
o20MatchedDispositionPacket mapping stamp event birth exact (opposite ** (matched, rightBirth, stampMatched)) =
  O20OriginalMatchedBirth event opposite birth rightBirth exact matched stampMatched

||| Eliminate E8's observed closing-or-original-match choice without losing
||| its closing branch. No right retained occurrence or raw-name equation
||| is manufactured by either constructor.
export
0 o20DispositionChoice :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  (mapping : RegistrationGenerationBijection name) ->
  (stamp : RegistrationGeneration name) ->
  (event : RegistrationEvent name key world error value) ->
  (birth : ScannedRegistrationBirth name key world error value Z left event) ->
  (eventChildGeneration event = stamp) ->
  Either
    (DeletedClosingRegistration event (afterActionOccurrence (scannedLocatedBirth birth)))
    (opposite : RegistrationEvent name key world error value **
      (RegistrationEventMatch mapping event opposite,
       ScannedRegistrationBirth name key world error value Z right opposite,
       (generationForward mapping stamp = eventChildGeneration opposite))) ->
  O20GenerationOnlyDisposition name key world error value mapping left right stamp
o20DispositionChoice mapping stamp event birth exact (Left closing) =
  O20OriginalClosingBirth event birth exact closing
o20DispositionChoice mapping stamp event birth exact (Right matched) =
  o20MatchedDispositionPacket mapping stamp event birth exact matched

||| Eliminate a single existing E8 classification packet. The output is a
||| flat indexed disposition, not another nested existential producer.
export
0 o20DispositionPacket :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  (mapping : RegistrationGenerationBijection name) ->
  (events : List (RegistrationEvent name key world error value)) ->
  (selected : name) -> (stamp : RegistrationGeneration name) ->
  (coverage : ClassifiedGeneratedBirth name key world error value Z left events selected **
    ((eventChildGeneration (coveredEvent coverage) = stamp),
     Either
       (DeletedClosingRegistration (coveredEvent coverage) (afterActionOccurrence (scannedLocatedBirth (coveredBirth coverage))))
       (opposite : RegistrationEvent name key world error value **
         (RegistrationEventMatch mapping (coveredEvent coverage) opposite,
          ScannedRegistrationBirth name key world error value Z right opposite,
          (generationForward mapping stamp = eventChildGeneration opposite))))) ->
  O20GenerationOnlyDisposition name key world error value mapping left right stamp
o20DispositionPacket mapping events selected stamp (coverage ** (exact, choice)) =
  o20DispositionChoice mapping stamp (coveredEvent coverage) (coveredBirth coverage) exact choice

||| Accepted canonical birth capital yields a generation-only ORIGINAL
||| disposition through E8. Unsupported and closing histories are retained;
||| the output does not assert a right canonical birth or physical stage.
export
0 o20CanonicalGenerationDisposition :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (inputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq left) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  (selected, parent : name) -> (component : Component key value world error) ->
  (birth : LocatedGeneratedRegistration selected parent component (canonicalTrace (canonicalSchedule capital))) ->
  O20GenerationOnlyDisposition name key world error value (generatedGenerationBijection inputs) left right
    (registrationGeneration (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence capital) birth))
o20CanonicalGenerationDisposition {name} {key} {world} {error} {value} nameEq keyEq protocol
  left right inputs capital unique selected parent component birth =
    o20DispositionPacket (generatedGenerationBijection inputs)
      (leftScannedEvents (acceptedAuthenticatedRegistrationMatching name key world error value nameEq
        left right (generatedGenerationBijection inputs) (generatedRegistrationTree inputs))) selected
      (registrationGeneration (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence capital) birth))
      (o20CanonicalOriginMatchOrClosing nameEq keyEq protocol left right inputs capital unique selected parent component birth)

||| An authentic original birth and its scanner coverage determine the flat
||| generation-only disposition. Raw uniqueness owns the exact stamp; the
||| accepted matching, not current endpoint names, owns the opposite branch.
export
0 o20CoveredGenerationDisposition :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (matching : AuthenticatedRegistrationMatching name key world error value mapping left right) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  (selected, parent : name) -> (component : Component key value world error) ->
  (birth : LocatedGeneratedRegistration selected parent component left) ->
  (coverage : ClassifiedGeneratedBirth name key world error value Z left (leftScannedEvents matching) selected) ->
  O20GenerationOnlyDisposition name key world error value mapping left right (registrationGeneration birth)
o20CoveredGenerationDisposition {nameEq} {keyEq} left right mapping matching unique selected parent component birth coverage =
  o20DispositionChoice mapping (registrationGeneration birth) (coveredEvent coverage) (coveredBirth coverage)
    (o20CoveredOriginStamp {nameEq} {keyEq} left unique (leftScannedEvents matching) selected parent component birth coverage)
    (o20MatchClassifiedOrigin mapping matching selected (registrationGeneration birth) coverage
      (o20CoveredOriginStamp {nameEq} {keyEq} left unique (leftScannedEvents matching) selected parent component birth coverage))

||| EVERY actual original generated birth receives its authenticated E8
||| disposition. No original support/presence or right canonical-retention
||| premise is required; raw uniqueness identifies this birth's exact stamp.
export
0 o20OriginalGenerationDisposition :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  (selected, parent : name) -> (component : Component key value world error) ->
  (birth : LocatedGeneratedRegistration selected parent component left) ->
  O20GenerationOnlyDisposition name key world error value mapping left right (registrationGeneration birth)
o20OriginalGenerationDisposition {name} {key} {world} {error} {value} nameEq keyEq left right mapping registrations unique
  selected parent component birth =
    o20CoveredGenerationDisposition {nameEq} {keyEq} left right mapping
      (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right mapping registrations)
      unique selected parent component birth
      (acceptedLeftBirthCoverage name key world error value nameEq left right mapping registrations selected parent component
        (generatedRegistrationActionOccurrence birth))

||| Complete immutable ORIGINAL birth history, quantified over actual located
||| occurrences. The closing branch is retained at every replay stage by
||| transporting occurrence origins, not by imposing current raw-name matches.
||| This record contains no paired stage sequence or runtime cut.
public export
record O20GenerationOnlyHistory
  (name, key, world, error : Type) (value : key -> Type)
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error}
  (mapping : RegistrationGenerationBijection name)
  (left : Transitions leftFirst leftFinal) (right : Transitions rightFirst rightFinal) where
  constructor MkO20GenerationOnlyHistory
  0 originalBirthDisposition :
    (selected, parent : name) -> (component : Component key value world error) ->
    (birth : LocatedGeneratedRegistration selected parent component left) ->
    O20GenerationOnlyDisposition name key world error value mapping left right (registrationGeneration birth)

||| The accepted original scanners produce the WHOLE immutable birth history.
||| This is occurrence coverage, not alignment of the two canonical words.
export
0 o20WholeOriginalGenerationHistory :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  O20GenerationOnlyHistory name key world error value mapping left right
o20WholeOriginalGenerationHistory nameEq keyEq left right mapping registrations unique =
  MkO20GenerationOnlyHistory
    (o20OriginalGenerationDisposition nameEq keyEq left right mapping registrations unique)

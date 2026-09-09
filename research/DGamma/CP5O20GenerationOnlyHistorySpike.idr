module DGamma.CP5O20GenerationOnlyHistorySpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5SupportedBirthCoverageSpike
import DGamma.CP5O20CanonicalBirthDispositionSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
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

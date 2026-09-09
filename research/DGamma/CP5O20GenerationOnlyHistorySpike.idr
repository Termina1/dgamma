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

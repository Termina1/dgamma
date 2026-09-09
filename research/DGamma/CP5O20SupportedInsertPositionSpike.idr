module DGamma.CP5O20SupportedInsertPositionSpike

import DGamma.Coeffects
import DGamma.CP5RetirementHistorySpike
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5ConfluenceDeletionChainSpike
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

||| Supported canonical birth's paired ORIGINAL scanner Insert positions.
||| Both original occurrences and the exact mapped stamp are retained. These
||| are per-parent-activation positions, NOT canonical physical trace ordinals.
public export
record O20SupportedInsertPositionPair
  (name, key, world, error : Type) (value : key -> Type)
  {0 leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error}
  (0 mapping : RegistrationGenerationBijection name)
  (0 left : Transitions leftFirst leftFinal) (0 right : Transitions rightFirst rightFinal)
  (0 stamp : RegistrationGeneration name) where
  constructor MkO20SupportedInsertPositionPair
  0 positionLeftEvent : RegistrationEvent name key world error value
  0 positionRightEvent : RegistrationEvent name key world error value
  0 positionLeftBirth : ScannedRegistrationBirth name key world error value Z left positionLeftEvent
  0 positionRightBirth : ScannedRegistrationBirth name key world error value Z right positionRightEvent
  0 positionOriginalStamp : (eventChildGeneration positionLeftEvent = stamp)
  0 positionEventMatch : RegistrationEventMatch mapping positionLeftEvent positionRightEvent
  0 positionMappedStamp : (generationForward mapping stamp = eventChildGeneration positionRightEvent)
  0 positionEqual : (eventChildPosition positionLeftEvent = eventChildPosition positionRightEvent)

||| Consume the authentic matcher's opposite event once. Its retained domain
||| supplies that very event's native birth; its match supplies position and
||| generation equations at the same original source stamp.
export
0 o20InsertPositionAtMatchedPacket :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  (mapping : RegistrationGenerationBijection name) ->
  (matching : AuthenticatedRegistrationMatching name key world error value mapping left right) ->
  (stamp : RegistrationGeneration name) -> (event : RegistrationEvent name key world error value) ->
  ScannedRegistrationBirth name key world error value Z left event ->
  (eventChildGeneration event = stamp) ->
  (opposite : RegistrationEvent name key world error value **
    (Elem opposite (rightScannedEvents matching), RegistrationEventMatch mapping event opposite)) ->
  O20SupportedInsertPositionPair name key world error value mapping left right stamp
o20InsertPositionAtMatchedPacket mapping matching stamp event birth exact (opposite ** (retained, matched)) =
  MkO20SupportedInsertPositionPair event opposite birth (rightScannedBirths matching opposite retained) exact matched
    (trans (cong (generationForward mapping) (sym exact)) (matchedChildGeneration matched))
    (matchedPerActivationPosition matched)

||| Native support rejects the authentic closing alternative; the retained
||| branch pairs original positions using the actual authenticated matching.
||| The source stamp is reconciled to the supplied birth by raw uniqueness.
export
0 o20SupportedClassifiedInsertPositions :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (matching : AuthenticatedRegistrationMatching name key world error value mapping left right) ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  RegistrationDiscipline protocol nameEq left -> (bindings (registry leftFirst) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  (selected, parent : name) -> (component : Component key value world error) ->
  (birth : LocatedGeneratedRegistration selected parent component left) ->
  (finalFiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry leftFinal) = Just finalFiber) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} selected leftFinal = True) ->
  ClassifiedGeneratedBirth name key world error value Z left (leftScannedEvents matching) selected ->
  O20SupportedInsertPositionPair name key world error value mapping left right (registrationGeneration birth)
o20SupportedClassifiedInsertPositions {name} {key} {value} {world} {error}
  nameEq keyEq protocol left right mapping matching aligned discipline empty unique selected parent component birth finalFiber found supported
  (MkClassifiedGeneratedBirth event childExact scanned (Left retained)) =
    o20InsertPositionAtMatchedPacket mapping matching (registrationGeneration birth) event scanned
      (o20CoveredOriginStamp {nameEq} {keyEq} left unique (leftScannedEvents matching) selected parent component birth
        (MkClassifiedGeneratedBirth event childExact scanned (Left retained)))
      (matchedEventForward matching event retained)
o20SupportedClassifiedInsertPositions {name} {key} {value} {world} {error} {leftFinal}
  nameEq keyEq protocol left right mapping matching aligned discipline empty unique selected parent component birth finalFiber found supported
  (MkClassifiedGeneratedBirth event childExact scanned (Right closing)) =
    void (nonretiredEndpointRejectsRetirement name key world error value nameEq keyEq left aligned empty unique selected finalFiber found
      (computedSupportNotRetired name key world error value nameEq keyEq leftFinal selected finalFiber found supported)
      (replace {p = \action => LocatedActionOccurrence action left} (cong ORetire childExact)
        (locatedClosingBirthHasRetirement name key world error value nameEq keyEq protocol left aligned discipline
          (eventChild event) (eventParent event) (eventComponent event) (scannedLocatedBirth scanned) (deletedParentEpisodeCloses closing))))

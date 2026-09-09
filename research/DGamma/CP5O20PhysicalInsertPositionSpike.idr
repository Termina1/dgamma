module DGamma.CP5O20PhysicalInsertPositionSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5O20CanonicalOrdinalAttachmentSpike
import DGamma.CP5O20SupportedInsertPositionSpike
import DGamma.CP5O20OwnCutSafetySpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Two actual replayed Inserts, their conjugated physical stamp equation,
||| and the original scanners' per-activation positions at those SAME origins.
||| This record does not assert preservation of canonical per-activation counts.
public export
record O20PhysicalInsertOriginPositions
  (name, key, world, error : Type) (value : key -> Type)
  {leftFirst, leftFinal, rightFirst, rightFinal, leftNowFirst, leftNowFinal, rightNowFirst, rightNowFinal : SystemState name key value world error}
  {left : Transitions leftFirst leftFinal} {right : Transitions rightFirst rightFinal}
  {leftNow : Transitions leftNowFirst leftNowFinal} {rightNow : Transitions rightNowFirst rightNowFinal}
  (leftReplay : ActionRegistrationReplayCorrespondence name key world error value left leftNow)
  (rightReplay : ActionRegistrationReplayCorrespondence name key world error value right rightNow)
  (mapping : RegistrationGenerationBijection name) (renaming : NameBijection name)
  (child, parent : name) (component : Component key value world error)
  (leftBirth : LocatedGeneratedRegistration child parent component leftNow) where
  constructor MkO20PhysicalInsertOriginPositions
  0 physicalBirths : O20AttachedGeneratedBirth name key world error value leftReplay rightReplay mapping renaming
    child parent component leftBirth
  0 physicalOriginalPositions : O20SupportedInsertPositionPair name key world error value mapping left right
    (registrationGeneration (replayGeneratedRegistrationOrigin leftReplay leftBirth))
  0 physicalRightOriginExact :
    (eventChildGeneration (positionRightEvent physicalOriginalPositions) =
      registrationGeneration (replayGeneratedRegistrationOrigin rightReplay (attachedRightBirth physicalBirths)))

||| Reconcile the position matcher's right ORIGINAL stamp with the SAME
||| opposite physical birth owned by the actual replay attachment.
export
0 o20PhysicalInsertOriginsFromPackets :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {leftFirst, leftFinal, rightFirst, rightFinal, leftNowFirst, leftNowFinal, rightNowFirst, rightNowFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  {leftNow : Transitions leftNowFirst leftNowFinal} -> {rightNow : Transitions rightNowFirst rightNowFinal} ->
  (leftReplay : ActionRegistrationReplayCorrespondence name key world error value left leftNow) ->
  (rightReplay : ActionRegistrationReplayCorrespondence name key world error value right rightNow) ->
  (mapping : RegistrationGenerationBijection name) -> (renaming : NameBijection name) ->
  (child, parent : name) -> (component : Component key value world error) ->
  (leftBirth : LocatedGeneratedRegistration child parent component leftNow) ->
  O20AttachedGeneratedBirth name key world error value leftReplay rightReplay mapping renaming child parent component leftBirth ->
  O20SupportedInsertPositionPair name key world error value mapping left right
    (registrationGeneration (replayGeneratedRegistrationOrigin leftReplay leftBirth)) ->
  O20PhysicalInsertOriginPositions name key world error value leftReplay rightReplay mapping renaming child parent component leftBirth
o20PhysicalInsertOriginsFromPackets leftReplay rightReplay mapping renaming child parent component leftBirth attached positions =
  MkO20PhysicalInsertOriginPositions attached positions
    (trans (sym (positionMappedStamp positions)) (attachedOriginalEquation attached))

||| With the original endpoint lookup explicitly observed, attach original
||| scanner positions to the ACTUAL replayed left Insert and its paired
||| canonical right Insert. Both origins come from the existing producer maps.
export
0 o20ReplayedInsertPositionsAtLookup :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal, replayedFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (inputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq left) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq right) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  GeneratedOrchestrationMatched name key world error value nameEq left right (generatedGenerationBijection inputs) ->
  (replayed : Transitions initial replayedFinal) ->
  (occurrences : ActionRegistrationReplayCorrespondence name key world error value
    (canonicalTrace (canonicalSchedule leftCapital)) replayed) ->
  (child, parent : name) -> (component : Component key value world error) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} child leftFinal = True) ->
  (leftBirth : LocatedGeneratedRegistration child parent component replayed) ->
  O20PresentLookup name key world error value nameEq child leftFinal ->
  O20PhysicalInsertOriginPositions name key world error value
    (composeActionRegistrationReplayCorrespondence (canonicalOccurrenceCorrespondence leftCapital) occurrences)
    (canonicalOccurrenceCorrespondence rightCapital) (generatedGenerationBijection inputs)
    (expectedBridgeBijection inputs) child parent component leftBirth
o20ReplayedInsertPositionsAtLookup name key world error value nameEq keyEq protocol left right inputs
  leftCapital rightCapital leftUnique rightUnique matched replayed occurrences child parent component supported leftBirth
  (MkO20PresentLookup fiber found) =
    o20PhysicalInsertOriginsFromPackets
      (composeActionRegistrationReplayCorrespondence (canonicalOccurrenceCorrespondence leftCapital) occurrences)
      (canonicalOccurrenceCorrespondence rightCapital) (generatedGenerationBijection inputs)
      (expectedBridgeBijection inputs) child parent component leftBirth
      (o20SupportedReplayedOrdinalAttachment name key world error value nameEq keyEq protocol left right inputs
        leftCapital rightCapital leftUnique rightUnique matched replayed occurrences child parent component supported leftBirth)
      (o20SupportedCanonicalInsertPositions nameEq keyEq protocol left right inputs leftCapital leftUnique child parent component
        (replayGeneratedRegistrationOrigin occurrences leftBirth) fiber found supported)

||| Accepted support produces the original presence observation internally.
||| The output joins authentic ORIGINAL per-activation positions to the real
||| exchanged physical Insert pair; canonical per-activation transport remains open.
export
0 o20SupportedReplayedInsertOrigins :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal, replayedFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (inputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq left) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq right) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  GeneratedOrchestrationMatched name key world error value nameEq left right (generatedGenerationBijection inputs) ->
  (replayed : Transitions initial replayedFinal) ->
  (occurrences : ActionRegistrationReplayCorrespondence name key world error value
    (canonicalTrace (canonicalSchedule leftCapital)) replayed) ->
  (child, parent : name) -> (component : Component key value world error) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} child leftFinal = True) ->
  (leftBirth : LocatedGeneratedRegistration child parent component replayed) ->
  O20PhysicalInsertOriginPositions name key world error value
    (composeActionRegistrationReplayCorrespondence (canonicalOccurrenceCorrespondence leftCapital) occurrences)
    (canonicalOccurrenceCorrespondence rightCapital) (generatedGenerationBijection inputs)
    (expectedBridgeBijection inputs) child parent component leftBirth
o20SupportedReplayedInsertOrigins name key world error value nameEq keyEq protocol left right inputs
  leftCapital rightCapital leftUnique rightUnique matched replayed occurrences child parent component supported leftBirth =
    o20ReplayedInsertPositionsAtLookup name key world error value nameEq keyEq protocol left right inputs
      leftCapital rightCapital leftUnique rightUnique matched replayed occurrences child parent component supported leftBirth
      (o20OriginalSupportedLookup nameEq keyEq protocol left leftCapital child supported)

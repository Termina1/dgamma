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

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

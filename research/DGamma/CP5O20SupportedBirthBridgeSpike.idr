module DGamma.CP5O20SupportedBirthBridgeSpike

import DGamma.Calculus
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

||| An actual canonical child birth has the actual ORIGINAL endpoint metadata.
||| Exact original origin comes from this capital's deletion/sorting producer.
export
0 canonicalGeneratedOriginMetadata :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (original : Transitions initial finalState) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (selected, parent : name) -> (component : Component key value world error) ->
  LocatedGeneratedRegistration selected parent component (canonicalTrace (canonicalSchedule capital)) ->
  (observed : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry finalState) = Just observed) ->
  ((ChildOf parent, component) = (fiberParent observed, fiberComponent observed))
canonicalGeneratedOriginMetadata name key world error value nameEq keyEq protocol original capital unique
  selected parent component occurrence observed found =
    uniqueRawBirthMetadata name key world error value nameEq keyEq original unique selected
      (ChildOf parent) (fiberParent observed) component (fiberComponent observed)
      (generatedRegistrationActionOccurrence (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence capital) occurrence))
      (rawMetadataBirthAtPrefix name key world error value nameEq keyEq original original NoTransitions
        (currentBirthTraceAppendEmpty name key world error value original)
        (replayAligned (chainReplayCapital (capitalPremises capital)))
        (replayInitialEmpty (chainReplayCapital (capitalPremises capital))) selected observed found)

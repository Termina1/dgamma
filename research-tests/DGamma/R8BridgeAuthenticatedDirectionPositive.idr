module DGamma.R8BridgeAuthenticatedDirectionPositive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Decidable.Equality

%default total

||| Positive constructor in the authenticated direction: operational replay ->
||| canonical-left source -> deletion/sorting source occurrence -> accepted
||| forward generation -> right deletion/sorting source occurrence.
public export
0 rebuildAuthenticatedBridge :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal, replayedLeftFinal :
    SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace} ->
  {replayed : Transitions initial replayedLeftFinal} ->
  {occurrences : ActionRegistrationReplayCorrespondence name key world error value
    (canonicalTrace (canonicalSchedule leftCapital)) replayed} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace} ->
  (bridge : ReplayedCanonicalEndpointBridge name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs leftCapital replayed occurrences
      rightCapital) ->
  ({child, parent : name} -> {component : Component key value world error} ->
    (replayedOccurrence : LocatedGeneratedRegistration child parent component replayed) ->
    (rightOccurrence : LocatedGeneratedRegistration
      (renameForward (replayBridgeBijection bridge) child)
      (renameForward (replayBridgeBijection bridge) parent) component
      (canonicalTrace (canonicalSchedule rightCapital)) **
      generationForward (generatedGenerationBijection sameInputs)
        (registrationGeneration
          (replayGeneratedRegistrationOrigin
            (canonicalOccurrenceCorrespondence leftCapital)
            (replayGeneratedRegistrationOrigin occurrences replayedOccurrence))) =
      registrationGeneration
        (replayGeneratedRegistrationOrigin
          (canonicalOccurrenceCorrespondence rightCapital) rightOccurrence))) ->
  ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital replayed occurrences rightCapital
rebuildAuthenticatedBridge {occurrences} bridge match =
  MkReplayedCanonicalEndpointBridge
    (replayBridgeAmbient bridge)
    (replayBridgeTables bridge)
    (replayBridgeControls bridge)
    (\replayedOccurrence =>
      (replayGeneratedRegistrationOrigin occurrences replayedOccurrence **
        (Refl, match replayedOccurrence)))

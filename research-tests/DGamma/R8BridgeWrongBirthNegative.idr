module DGamma.R8BridgeWrongBirthNegative

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Decidable.Equality

%default total

||| Exact round-6 Probe 24 attack at the revision-7 bridge: retain the exact
||| replay origin and endpoint fields, but pick an arbitrary same-action right
||| occurrence without proving accepted original-generation correspondence.
public export
0 replaceBridgeRightOccurrenceWithoutGenerationEquation :
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
    LocatedGeneratedRegistration child parent component replayed ->
    LocatedGeneratedRegistration
      (renameForward (replayBridgeBijection bridge) child)
      (renameForward (replayBridgeBijection bridge) parent) component
      (canonicalTrace (canonicalSchedule rightCapital))) ->
  ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital replayed occurrences rightCapital
replaceBridgeRightOccurrenceWithoutGenerationEquation {occurrences} bridge alternate =
  MkReplayedCanonicalEndpointBridge
    (replayBridgeBijection bridge)
    (replayBridgeBijectionFixed bridge)
    (replayBridgeAmbient bridge)
    (replayBridgeTables bridge)
    (replayBridgeControls bridge)
    (\replayedOccurrence =>
      (replayGeneratedRegistrationOrigin occurrences replayedOccurrence **
        (Refl, (alternate replayedOccurrence ** ()))))

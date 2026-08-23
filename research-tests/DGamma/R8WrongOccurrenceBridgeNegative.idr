module DGamma.R8WrongOccurrenceBridgeNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Decidable.Equality

%default total

0 detachBridgeOccurrenceRelation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal, replayedFinal :
    SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace} ->
  {replayed : Transitions initial replayedFinal} ->
  (first, second : ActionRegistrationReplayCorrespondence name key world error
    value (canonicalTrace (canonicalSchedule leftCapital)) replayed) ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace} ->
  ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital replayed first rightCapital ->
  ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital replayed second rightCapital
detachBridgeOccurrenceRelation first second bridge = bridge

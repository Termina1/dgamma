module DGamma.R8PublicScheduleCannotReachBridgeNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Decidable.Equality

%default total

||| Probe 27 boundary: even a complete public schedule containing a synthetic
||| no-withdrawal canonical map is not accepted where the bridge requires an
||| authenticated enriched capital. Rejection occurs before any birth equation.
public export
0 publicScheduleCannotEnterAuthenticatedBridge :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal, replayedFinal :
    SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace} ->
  (syntheticSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq leftTrace) ->
  {replayed : Transitions initial replayedFinal} ->
  (occurrences : ActionRegistrationReplayCorrespondence name key world error value
    (canonicalTrace syntheticSchedule) replayed) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs syntheticSchedule replayed occurrences
      rightCapital
publicScheduleCannotEnterAuthenticatedBridge syntheticSchedule occurrences
  rightCapital = rightCapital

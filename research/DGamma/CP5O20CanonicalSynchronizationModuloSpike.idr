module DGamma.CP5O20CanonicalSynchronizationModuloSpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5O20CanonicalOrdinalAttachmentSpike
import DGamma.CP5O20HistoryNameTransportSpike
import DGamma.CP5O20OccurrenceStampedHistorySpike
import Decidable.Equality

%default total
%unbound_implicits off

||| Owner-approved NEW accepted-input synchronization GOAL at the EXACT
||| conjugated actual replay maps. It is a Type, not an inhabitant or oracle.
||| A8's o20SynchronizationForwardOrdinalFixed shows why the unchanged old
||| lockstep goal is a superseded candidate. Genuine occurrence labels now
||| allow mapped births at different physical ordinals. Native paths and both
||| supplied-word scanners are still obligations, not supplied endpoint cuts.
||| whole-word / per-actor ordering and coverage producer remains to prove; arbitrary skips are NOT asserted to be zero native edges
public export
0 o20CanonicalSynchronizationGoalModulo :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace} ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  {operational : CertifiedOperationalCanonicalPermutation name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital matching} ->
  (execution : PermutedCanonicalExecution name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital operational) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  (0 generatedMatched : GeneratedOrchestrationMatched name key world error value nameEq
    leftTrace rightTrace (generatedGenerationBijection sameInputs)) -> Type
o20CanonicalSynchronizationGoalModulo {name} {key} {world} {error} {value} {nameEq} {keyEq}
  {sameInputs} {leftCapital} {rightCapital} {operational} execution leftUnique rightUnique generatedMatched =
  O20HistorySynchronizationModulo name key world error value nameEq keyEq
    (o20ReplayOrdinalBijection
      (replayGenerationRenaming (composeActionRegistrationReplayCorrespondence
        (canonicalOccurrenceCorrespondence leftCapital) (permutationOccurrenceCorrespondence execution)))
      (generatedGenerationBijection sameInputs)
      (replayGenerationRenaming (canonicalOccurrenceCorrespondence rightCapital)))
    (operationalTargetTrace operational) (canonicalTrace (canonicalSchedule rightCapital))

||| Accepted-capital sufficiency consumer for the NEW synchronization target.
||| The initial empty proof comes from the actual canonical replay premises;
||| the endpoint history cut is produced at the EXACT conjugated maps. A8
||| motivates this target. The synchronization remains INPUT, not a produced
||| universal pair, and current-name ALL-name rebasing remains separate B debt.
||| whole-word / per-actor ordering and coverage producer remains to prove; arbitrary skips are NOT asserted to be zero native edges
public export
0 o20CanonicalModuloHistoryCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace} ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  {operational : CertifiedOperationalCanonicalPermutation name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital matching} ->
  (execution : PermutedCanonicalExecution name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital operational) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  (0 generatedMatched : GeneratedOrchestrationMatched name key world error value nameEq
    leftTrace rightTrace (generatedGenerationBijection sameInputs)) ->
  (synchronization : o20CanonicalSynchronizationGoalModulo
    {name} {key} {world} {error} {value} {protocol} {nameEq} {keyEq}
    {initial} {leftFinal} {rightFinal} {leftTrace} {rightTrace} {sameInputs}
    {leftCapital} {rightCapital} {matching} {operational}
    execution leftUnique rightUnique generatedMatched) ->
  O20HistoryCut name key world error value nameEq
    (o20ReplayOrdinalBijection
      (replayGenerationRenaming (composeActionRegistrationReplayCorrespondence
        (canonicalOccurrenceCorrespondence leftCapital) (permutationOccurrenceCorrespondence execution)))
      (generatedGenerationBijection sameInputs)
      (replayGenerationRenaming (canonicalOccurrenceCorrespondence rightCapital)))
    (moduloLeftLive synchronization) (moduloRightLive synchronization)
    (operationalTargetFinal operational) (canonicalFinal (canonicalSchedule rightCapital))
o20CanonicalModuloHistoryCut {sameInputs} {leftCapital} {rightCapital} {operational}
  execution leftUnique rightUnique generatedMatched synchronization =
    o20ModuloSynchronizationHistoryCut
      (o20ReplayOrdinalBijection
      (replayGenerationRenaming (composeActionRegistrationReplayCorrespondence
        (canonicalOccurrenceCorrespondence leftCapital) (permutationOccurrenceCorrespondence execution)))
      (generatedGenerationBijection sameInputs)
      (replayGenerationRenaming (canonicalOccurrenceCorrespondence rightCapital)))
      synchronization (replayInitialEmpty (canonicalReplayPremises leftCapital))

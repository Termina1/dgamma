module DGamma.CP5O20CanonicalSynchronizationGoalSpike

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
import DGamma.CP5O20StampedHistoryFoldSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| The exact missing accepted-input synchronization GOAL as a total type
||| function, NOT an inhabitant or a postulate. It asks for an endpoint/scanner
||| synchronized native path at the conjugated replay map. Literal equality
||| of that path to both supplied words would be a stronger separate result.
public export
0 o20CanonicalSynchronizationGoal :
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
o20CanonicalSynchronizationGoal {name} {key} {world} {error} {value} {nameEq} {keyEq}
  {sameInputs} {leftCapital} {rightCapital} {operational} execution leftUnique rightUnique generatedMatched =
  O20HistorySynchronization name key world error value nameEq keyEq
    (o20ReplayOrdinalBijection
      (replayGenerationRenaming (composeActionRegistrationReplayCorrespondence
        (canonicalOccurrenceCorrespondence leftCapital) (permutationOccurrenceCorrespondence execution)))
      (generatedGenerationBijection sameInputs)
      (replayGenerationRenaming (canonicalOccurrenceCorrespondence rightCapital)))
    (operationalTargetTrace operational) (canonicalTrace (canonicalSchedule rightCapital))

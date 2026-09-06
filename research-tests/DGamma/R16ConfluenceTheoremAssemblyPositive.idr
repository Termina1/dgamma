module DGamma.R16ConfluenceTheoremAssemblyPositive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Metatheory
import DGamma.CP4Support
import DGamma.CP4SupportSolution
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorEndpoint
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.R8FullPipeline
import DGamma.CP5UniqueRawNameInsertions
import Decidable.Equality

%default total

0 canonicalPremisesFromTheoremInputs :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (aligned : AlignedTransitions name key world error value nameEq keyEq trace) ->
  (discipline : RegistrationDiscipline protocol nameEq trace) ->
  (initialWellFormed : registryWellFormed @{nameEq} @{keyEq} initial = True) ->
  (initialEmpty : bindings (registry initial) = []) ->
  (quietFinal : quiet @{nameEq} @{keyEq} finalState = True) ->
  (noFailures : noFailedFibers finalState = True) ->
  (totality : TraceComponentsTotal nameEq keyEq trace) ->
  (independent : TraceIndependent name key world error value keyEq trace) ->
  CanonicalizationPremises name key world error value protocol nameEq keyEq trace
canonicalPremisesFromTheoremInputs {name} {key} {world} {error} {value}
  nameEq keyEq protocol {initial} {finalState} trace aligned discipline
  initialWellFormed initialEmpty quietFinal noFailures totality independent =
    let reached : ReachedFromEmpty name key world error value nameEq keyEq
          finalState
        reached = MkReachedFromEmpty initial trace aligned initialEmpty
          initialWellFormed
        0 provenance : RegistrationProvenance protocol nameEq trace
        provenance = registrationDisciplineProvenance protocol nameEq trace
          discipline
        0 finalWellFormed : registryWellFormed @{nameEq} @{keyEq} finalState =
          True
        finalWellFormed = alignedTraceWellFormedEnd nameEq keyEq trace aligned
          initialWellFormed
        0 ranked : RegistryProtocolRanked protocol nameEq finalState
        ranked = reachedRegistryProtocolRanked protocol nameEq keyEq reached
          provenance
        0 parentRanks : RegistryParentRanksIncrease protocol nameEq finalState
        parentRanks = reachedRegistryParentRanksIncrease protocol nameEq keyEq
          reached provenance
        0 acyclic : PrecedenceAcyclic nameEq finalState
        acyclic = disciplinedEndpointPrecedenceAcyclic protocol nameEq keyEq
          finalState reached discipline
        0 supportWellFounded : SupportWellFounded nameEq finalState
        supportWellFounded = supportCombinedWellFounded protocol nameEq
          finalState ranked parentRanks
        0 supportMatches : SupportMatchesActive nameEq keyEq finalState
        supportMatches = deletionPremisesGiveSupportMatchesActive protocol nameEq
          keyEq initial finalState trace aligned discipline initialWellFormed
          initialEmpty quietFinal noFailures totality
        bundle : ReplayInvariantBundle name key world error value protocol nameEq
          keyEq trace
        bundle = MkReplayInvariantBundle aligned discipline initialWellFormed
          initialEmpty finalWellFormed quietFinal noFailures totality independent
          provenance ranked parentRanks acyclic supportWellFounded supportMatches
    in MkCanonicalizationPremises bundle

||| CONDITIONAL research assembly, not the immutable CP3 theorem type.
||| Assumes aligned left/right executions and registration disciplines; empty,
||| well-formed initial registry; quiet, failure-free endpoints; component
||| totality and trace independence on both sides; accepted common inputs;
||| both R143 late-capital records (shared original/reduced order, composed
||| endpoint, exact withdrawals, exact replay accounting); and strong global
||| raw insertion uniqueness for EACH original trace. Late-capital producers
||| and the remaining research holes are not discharged by this fixture.
public export
0 r16ConfluenceTheoremAssembly :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (initial, leftFinal, rightFinal : SystemState name key value world error) ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  AlignedTransitions name key world error value nameEq keyEq leftTrace ->
  AlignedTransitions name key world error value nameEq keyEq rightTrace ->
  RegistrationDiscipline protocol nameEq leftTrace ->
  RegistrationDiscipline protocol nameEq rightTrace ->
  (registryWellFormed @{nameEq} @{keyEq} initial = True) ->
  (bindings (registry initial) = []) ->
  (quiet @{nameEq} @{keyEq} leftFinal = True) ->
  (quiet @{nameEq} @{keyEq} rightFinal = True) ->
  (noFailedFibers leftFinal = True) ->
  (noFailedFibers rightFinal = True) ->
  TraceComponentsTotal nameEq keyEq leftTrace ->
  TraceComponentsTotal nameEq keyEq rightTrace ->
  TraceIndependent name key world error value keyEq leftTrace ->
  TraceIndependent name key world error value keyEq rightTrace ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace) ->
  (leftLate : FullPipelineLateCanonicalPremises name key world error value protocol nameEq keyEq leftTrace) ->
  (rightLate : FullPipelineLateCanonicalPremises name key world error value protocol nameEq keyEq rightTrace) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  ConfluenceResult name key world error value protocol nameEq keyEq leftTrace
    rightTrace (generatedGenerationBijection sameInputs)
    (currentNameBijection (endpointRenaming sameInputs))
r16ConfluenceTheoremAssembly nameEq keyEq protocol initial leftFinal rightFinal
  leftTrace rightTrace leftAligned rightAligned leftDiscipline rightDiscipline
  initialWellFormed initialEmpty leftQuiet rightQuiet leftNoFailures
  rightNoFailures leftTotal rightTotal leftIndependent rightIndependent
  sameInputs leftLate rightLate leftUnique rightUnique =
    let leftPremises = canonicalPremisesFromTheoremInputs nameEq keyEq protocol
          leftTrace leftAligned leftDiscipline initialWellFormed initialEmpty
          leftQuiet leftNoFailures leftTotal leftIndependent
        rightPremises = canonicalPremisesFromTheoremInputs nameEq keyEq protocol
          rightTrace rightAligned rightDiscipline initialWellFormed initialEmpty
          rightQuiet rightNoFailures rightTotal rightIndependent
    in fullPipelineFromBundles nameEq keyEq protocol leftTrace rightTrace
      leftPremises rightPremises sameInputs leftLate rightLate leftUnique rightUnique

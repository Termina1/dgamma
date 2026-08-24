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

||| Mandatory revision-16 full-coverage probe: the body has the immutable CP3
||| `confluenceTheorem` type exactly and assembles the complete research pipeline
||| without adding premises or using a hole/escape hatch.
public export
0 r16ConfluenceTheoremAssembly :
  confluenceTheorem name key value world error
r16ConfluenceTheoremAssembly nameEq keyEq protocol initial leftFinal rightFinal
  leftTrace rightTrace leftAligned rightAligned leftDiscipline rightDiscipline
  initialWellFormed initialEmpty leftQuiet rightQuiet leftNoFailures
  rightNoFailures leftTotal rightTotal leftIndependent rightIndependent
  sameInputs =
    let leftPremises = canonicalPremisesFromTheoremInputs nameEq keyEq protocol
          leftTrace leftAligned leftDiscipline initialWellFormed initialEmpty
          leftQuiet leftNoFailures leftTotal leftIndependent
        rightPremises = canonicalPremisesFromTheoremInputs nameEq keyEq protocol
          rightTrace rightAligned rightDiscipline initialWellFormed initialEmpty
          rightQuiet rightNoFailures rightTotal rightIndependent
    in fullPipelineFromBundles nameEq keyEq protocol leftTrace rightTrace
      leftPremises rightPremises sameInputs

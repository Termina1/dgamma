module DGamma.R8FullPipeline

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import Decidable.Equality

%default total

public export
0 fullPipelineFromBundles :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (leftPremises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightPremises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq rightTrace) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace) ->
  ConfluenceResult name key world error value protocol nameEq keyEq leftTrace
    rightTrace (generatedGenerationBijection sameInputs)
    (currentNameBijection (endpointRenaming sameInputs))
fullPipelineFromBundles nameEq keyEq protocol leftTrace rightTrace leftPremises
  rightPremises sameInputs =
  let leftReduction = deleteAllClosingEpisodesSpike nameEq keyEq protocol
        leftTrace leftPremises
      leftShape = closingFreeTraceShapeSpike nameEq keyEq protocol
        (reducedTrace leftReduction) (reducedClosingFree leftReduction)
        (chainReplayCapital (reducedPremises leftReduction))
      leftOrdering = supportOrderingSpike nameEq keyEq protocol
        (reducedTrace leftReduction)
        (chainReplayCapital (reducedPremises leftReduction))
      leftSorted = sortClosingFreeTraceSpike nameEq keyEq protocol
        (reducedTrace leftReduction)
        (chainReplayCapital (reducedPremises leftReduction)) leftShape leftOrdering
      leftTransport = canonicalSupportTransportSpike nameEq keyEq leftTrace
        (reducedTrace leftReduction) (cumulativeEndpoint leftReduction)
        (cumulativeRegistrationAccounting leftReduction)
      leftAccounting = deletionSortingOrchestrationAccountingSpike nameEq keyEq
        protocol leftTrace leftReduction leftOrdering leftSorted
      leftCapital = independentCanonicalScheduleSpike nameEq keyEq protocol
        leftTrace leftPremises leftReduction leftOrdering leftSorted leftTransport
        leftAccounting
      rightReduction = deleteAllClosingEpisodesSpike nameEq keyEq protocol
        rightTrace rightPremises
      rightShape = closingFreeTraceShapeSpike nameEq keyEq protocol
        (reducedTrace rightReduction) (reducedClosingFree rightReduction)
        (chainReplayCapital (reducedPremises rightReduction))
      rightOrdering = supportOrderingSpike nameEq keyEq protocol
        (reducedTrace rightReduction)
        (chainReplayCapital (reducedPremises rightReduction))
      rightSorted = sortClosingFreeTraceSpike nameEq keyEq protocol
        (reducedTrace rightReduction)
        (chainReplayCapital (reducedPremises rightReduction)) rightShape rightOrdering
      rightTransport = canonicalSupportTransportSpike nameEq keyEq rightTrace
        (reducedTrace rightReduction) (cumulativeEndpoint rightReduction)
        (cumulativeRegistrationAccounting rightReduction)
      rightAccounting = deletionSortingOrchestrationAccountingSpike nameEq keyEq
        protocol rightTrace rightReduction rightOrdering rightSorted
      rightCapital = independentCanonicalScheduleSpike nameEq keyEq protocol
        rightTrace rightPremises rightReduction rightOrdering rightSorted
        rightTransport rightAccounting
      matching = canonicalSupportOrdersMatchSpike nameEq keyEq protocol leftTrace
        rightTrace sameInputs leftCapital rightCapital
      operational = selectOperationalCanonicalPermutationSpike nameEq keyEq
        protocol leftTrace rightTrace sameInputs leftCapital rightCapital matching
      convergence = canonicalSchedulesConvergeSpike nameEq keyEq protocol leftTrace
        rightTrace sameInputs leftCapital rightCapital operational
      equivalent = originalEndpointsConvergeSpike nameEq keyEq protocol leftTrace
        rightTrace sameInputs leftCapital rightCapital convergence in
    confluenceResultFromCanonicalCapital nameEq keyEq protocol leftTrace rightTrace
      sameInputs (canonicalSchedule leftCapital)
      (canonicalSchedule rightCapital) equivalent

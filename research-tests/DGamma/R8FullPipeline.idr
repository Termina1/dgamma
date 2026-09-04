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

||| Explicit downstream provider for the corrected O15/O16 boundaries.  These
||| fields are exactly the obligations that cannot be recovered from the
||| uncorrelated stored registration trees.
public export
record FullPipelineLateCanonicalPremises
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal) where
  constructor MkFullPipelineLateCanonicalPremises
  sideOriginalLinearization :
    (reduction : ClosingFreeReduction name key world error value protocol nameEq
      keyEq original) ->
    (ordering : SupportOrderingCapital name key world error value nameEq keyEq
      (reducedFinal reduction)) ->
    LinearizesSupport name key world error value nameEq keyEq originalFinal
      (orderedSupportNames ordering)
  sideAccountingEndpoint :
    (reduction : ClosingFreeReduction name key world error value protocol nameEq
      keyEq original) ->
    (ordering : SupportOrderingCapital name key world error value nameEq keyEq
      (reducedFinal reduction)) ->
    (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
      keyEq (reducedTrace reduction) ordering) ->
    CanonicalEndpointRelation name key world error value nameEq keyEq
      originalFinal (sortedFinal sorted)
  sideAccountingWithdrawalsExact :
    (reduction : ClosingFreeReduction name key world error value protocol nameEq
      keyEq original) ->
    (ordering : SupportOrderingCapital name key world error value nameEq keyEq
      (reducedFinal reduction)) ->
    (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
      keyEq (reducedTrace reduction) ordering) ->
    endpointWithdrawnGenerations
      (sideAccountingEndpoint reduction ordering sorted) =
    endpointWithdrawnGenerations (cumulativeEndpoint reduction)
  sideReplayAccountingLaws :
    (reduction : ClosingFreeReduction name key world error value protocol nameEq
      keyEq original) ->
    (ordering : SupportOrderingCapital name key world error value nameEq keyEq
      (reducedFinal reduction)) ->
    (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
      keyEq (reducedTrace reduction) ordering) ->
    CanonicalReplayAccountingLaws name key world error value original
      (sortedTrace sorted)
      (endpointWithdrawnGenerations
        (sideAccountingEndpoint reduction ordering sorted))
      (deletionSortingOccurrenceCorrespondence reduction sorted)

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
  (leftLate : FullPipelineLateCanonicalPremises name key world error value
    protocol nameEq keyEq leftTrace) ->
  (rightLate : FullPipelineLateCanonicalPremises name key world error value
    protocol nameEq keyEq rightTrace) ->
  ConfluenceResult name key world error value protocol nameEq keyEq leftTrace
    rightTrace (generatedGenerationBijection sameInputs)
    (currentNameBijection (endpointRenaming sameInputs))
fullPipelineFromBundles nameEq keyEq protocol leftTrace rightTrace leftPremises
  rightPremises sameInputs leftLate rightLate =
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
        (orderedSupportNames leftOrdering)
        (orderedSupportLinearization leftOrdering)
        (sideOriginalLinearization leftLate leftReduction leftOrdering)
      leftAccounting = deletionSortingOrchestrationAccountingSpike nameEq keyEq
        protocol leftTrace leftReduction leftOrdering leftSorted
        (sideAccountingEndpoint leftLate leftReduction leftOrdering leftSorted)
        (sideAccountingWithdrawalsExact leftLate leftReduction leftOrdering
          leftSorted)
        (sideReplayAccountingLaws leftLate leftReduction leftOrdering leftSorted)
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
        (orderedSupportNames rightOrdering)
        (orderedSupportLinearization rightOrdering)
        (sideOriginalLinearization rightLate rightReduction rightOrdering)
      rightAccounting = deletionSortingOrchestrationAccountingSpike nameEq keyEq
        protocol rightTrace rightReduction rightOrdering rightSorted
        (sideAccountingEndpoint rightLate rightReduction rightOrdering rightSorted)
        (sideAccountingWithdrawalsExact rightLate rightReduction rightOrdering
          rightSorted)
        (sideReplayAccountingLaws rightLate rightReduction rightOrdering rightSorted)
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

module DGamma.R4VestigialSimultaneous

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import Data.List.Elem
import Decidable.Equality

%default total

||| Same complete simultaneous assembly, under an explicit accepted
||| original-present/reduced-absent vestigial endpoint case.
0 assembleWithPermittedVestigialChild :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq original) ->
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)) ->
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) ->
  (supportTransport : CanonicalSupportTransport name key world error value
    nameEq keyEq originalFinal (reducedFinal reduction)
      (cumulativeEndpoint reduction)) ->
  (accounting : OneTraceOrchestrationAccounting name key world error value
    protocol nameEq keyEq original reduction ordering sorted) ->
  ((generation : RegistrationGeneration name) ->
    Elem generation (endpointWithdrawnGenerations
      (accountedEndpoint accounting)) ->
    DeletedGenerationClassification name key world error value nameEq original
      generation) ->
  (child : name) ->
  Elem child (endpointWithdrawnNames (cumulativeEndpoint reduction)) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} child (registry originalFinal) = Just fiber ->
  retired fiber = True ->
  installed (fiberLifecycle fiber) = False ->
  bindings (ownedValues (fiberTable fiber)) = [] ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} child (registry (reducedFinal reduction)) = Nothing ->
  IndependentCanonicalSchedule name key world error value protocol nameEq keyEq
    original
assembleWithPermittedVestigialChild nameEq keyEq protocol original premises reduction
  ordering sorted supportTransport accounting classified child withdrawn fiber
  present retiredProof inactiveProof emptyProof absent =
    DGamma.CP5ConfluenceCanonicalSortSpike.assembleIndependentCanonicalSchedule
      nameEq keyEq protocol original premises reduction ordering sorted
      supportTransport accounting classified

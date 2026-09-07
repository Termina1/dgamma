module DGamma.CP5GeneratedRetirementTransportSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5RetirementHistorySpike
import Decidable.Equality

%default total
%unbound_implicits off

||| Construct the exact scan of any checked trace, without deleting TTC seeds
||| or importing any frozen deletion theorem/certificate.
export
0 generatedCompletePrefixScan :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  {first, finalState : SystemState name key value world error} ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) -> (trace : Transitions first finalState) ->
  (finalOrdinal : Nat ** finalLive : GenerationEnvironment name ** GenerationTraceScan nameEq ordinal live trace finalOrdinal finalLive)
generatedCompletePrefixScan name key world error value nameEq ordinal live NoTransitions =
  (ordinal ** live ** GenerationTraceScanEnd)
generatedCompletePrefixScan name key world error value nameEq ordinal live (MoreTransitions step rest) =
  case generatedCompletePrefixScan name key world error value nameEq (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal (transitionAction step) live) rest of
    (finalOrdinal ** finalLive ** later) => (finalOrdinal ** finalLive ** GenerationTraceScanStep step rest later)

0 generatedRetirementFromScan :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> (selected, parent : name) ->
  (occurrence : LocatedActionOccurrence (ORetire selected) trace) ->
  (sourceFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry (actionBeforeState occurrence)) = Just sourceFiber) -> (fiberParent sourceFiber = ChildOf parent) ->
  AlignedTransitions name key world error value nameEq keyEq (beforeActionOccurrence occurrence) -> (bindings (registry first) = []) ->
  (finalOrdinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationTraceScan nameEq Z [] (beforeActionOccurrence occurrence) finalOrdinal live ->
  (packet : LocatedGeneratedOrchestration name key world error value nameEq trace **
    (generatedActor packet = selected, generatedRemoval packet = False))
generatedRetirementFromScan name key world error value nameEq keyEq trace selected parent occurrence sourceFiber sourceFound parentExact aligned empty finalOrdinal live scan =
  case currentDomainFromEmptyScan name key world error value nameEq keyEq (beforeActionOccurrence occurrence) finalOrdinal live scan aligned empty
    selected sourceFiber sourceFound of
    (generation ** current) =>
      (MkLocatedGeneratedOrchestration selected False occurrence sourceFiber parent sourceFound parentExact finalOrdinal live scan generation current ** (Refl, Refl))

||| Any actual retirement of a present generated endpoint name inhabits A9's
||| domain. Its source parent and current generation are DERIVED, not supplied.
export
0 generatedEndpointRetirementPacket :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> AlignedTransitions name key world error value nameEq keyEq trace ->
  (bindings (registry first) = []) -> UniqueRawNameInsertions name key world error value nameEq keyEq trace ->
  (selected, parent : name) -> (finalFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} selected (registry finalState) = Just finalFiber) ->
  (fiberParent finalFiber = ChildOf parent) -> LocatedActionOccurrence (ORetire selected) trace ->
  (packet : LocatedGeneratedOrchestration name key world error value nameEq trace **
    (generatedActor packet = selected, generatedRemoval packet = False))
generatedEndpointRetirementPacket name key world error value nameEq keyEq trace aligned empty unique selected parent finalFiber finalFound parentExact occurrence =
  case retirementLocatedSource name key world error value nameEq keyEq trace aligned selected occurrence of
    (sourceFiber ** sourceFound) =>
      case generatedCompletePrefixScan name key world error value nameEq Z [] (beforeActionOccurrence occurrence) of
        (ordinal ** live ** scan) =>
          generatedRetirementFromScan name key world error value nameEq keyEq trace selected parent occurrence sourceFiber sourceFound
            (trans (cong fst (actualPrefixEndpointMetadata name key world error value nameEq keyEq trace (beforeActionOccurrence occurrence)
              (MoreTransitions (locatedTransition occurrence) (afterActionOccurrence occurrence)) (actionOccurrenceDecomposition occurrence)
              aligned empty unique selected sourceFiber finalFiber sourceFound finalFound)) parentExact)
            (fst (alignedAppendSplit (beforeActionOccurrence occurrence) (MoreTransitions (locatedTransition occurrence) (afterActionOccurrence occurrence))
              (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym (actionOccurrenceDecomposition occurrence)) aligned)))
            empty ordinal live scan

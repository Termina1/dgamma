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

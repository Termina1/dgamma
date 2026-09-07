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

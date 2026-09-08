module DGamma.CP5O19OperationalAssemblySpike

import DGamma.CP5O19SameChainAssemblySpike
import DGamma.CP5O19ReachedDecompositionSpike
import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19CartesianColumnsSpike
import DGamma.CP5O19CartesianNumericSpike
import DGamma.CP5O19OrdinalPlanSpike
import DGamma.CP5O19ActualCartesianSpike
import DGamma.CP5O19GridCertificationSpike
import DGamma.CP5O19WholeBlockSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5GeneratedOrchestrationMatched
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Genuine external orchestration correspondence along the actual finite
||| derivation. Every node contributes its OWN complete filtered relation,
||| including actual transition occurrences; this is not a label-word map.
export
0 o19FiniteSameExternalInputs :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> {keyEq : DecEq key} ->
  {protocol : RegistrationProtocol key value world error} ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {target : Transitions initial targetFinal} ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq source target ->
  SameExternalOrchestration nameEq source target
o19FiniteSameExternalInputs {source} nameEq FiniteAdjacentSwapDone =
  sameExternalOrchestrationReflexiveSpike nameEq source
o19FiniteSameExternalInputs nameEq
  (FiniteAdjacentSwapStep source earlier left right later orientation diamond result target rest) =
    sameExternalOrchestrationTransitiveSpike nameEq (swappedSameExternalInputs result)
      (o19FiniteSameExternalInputs nameEq rest)

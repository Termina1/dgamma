module DGamma.CP5O19SameChainAssemblySpike

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

||| Endpoint quotient for the ACTUAL finite chain, composing each node's
||| OWN endpoint. No equality of action labels substitutes for replay data.
export
0 o19FiniteEndpoint :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {protocol : RegistrationProtocol key value world error} ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {target : Transitions initial targetFinal} ->
  (derivation : FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq source target) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} sourceFinal = True) ->
  RelationalReplayEndpoint name key world error value nameEq keyEq sourceFinal targetFinal
o19FiniteEndpoint {sourceFinal} nameEq keyEq FiniteAdjacentSwapDone wellFormed =
  relationalReplayEndpointReflexiveSpike nameEq keyEq sourceFinal wellFormed
o19FiniteEndpoint {sourceFinal} {targetFinal} nameEq keyEq
  (FiniteAdjacentSwapStep source earlier left right later orientation diamond result target rest) wellFormed =
    relationalReplayEndpointTransitiveSpike nameEq keyEq sourceFinal (replayedFinal result) targetFinal
      (swappedEndpoint result)
      (o19FiniteEndpoint nameEq keyEq rest (replayedWellFormed (swappedEndpoint result)))

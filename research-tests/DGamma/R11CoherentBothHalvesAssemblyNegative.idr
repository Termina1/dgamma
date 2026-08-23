module DGamma.R11CoherentBothHalvesAssemblyNegative

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import Decidable.Equality

%default total

||| Expected failure after actual O18 reassembly from the exact producer chain:
||| an internally coherent alternate map still cannot become the output.
public export
0 coherentBothHalvesCannotEnterProducerAssembly :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  (alternate : ActionRegistrationReplayCorrespondence name key world error value
    original (sortedTrace (capitalSorted capital))) ->
  canonicalOccurrenceCorrespondence
    (assembleIndependentCanonicalSchedule nameEq keyEq protocol original
      (capitalPremises capital) (capitalReduction capital)
      (capitalOrdering capital) (capitalSorted capital)
      (capitalSupportTransport capital) (capitalAccounting capital)
      (capitalWithdrawnClassified capital)) = alternate
coherentBothHalvesCannotEnterProducerAssembly nameEq keyEq protocol original capital
  alternate = Refl

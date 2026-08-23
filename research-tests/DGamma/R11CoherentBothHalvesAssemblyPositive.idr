module DGamma.R11CoherentBothHalvesAssemblyPositive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import Decidable.Equality

%default total

||| Re-run O18 from an existing capital's exact producer fields. A bare coherent
||| alternate map is accepted only as an ignored attack input and cannot affect
||| the assembled output.
public export
0 assembledCapitalIgnoresBareCoherentMap :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  (alternate : ActionRegistrationReplayCorrespondence name key world error value
    original (canonicalTrace (canonicalSchedule capital))) ->
  canonicalOccurrenceCorrespondence
    (assembleIndependentCanonicalSchedule nameEq keyEq protocol original
      (capitalPremises capital) (capitalReduction capital)
      (capitalOrdering capital) (capitalSorted capital)
      (capitalSupportTransport capital) (capitalAccounting capital)
      (capitalWithdrawnClassified capital)) =
    deletionSortingOccurrenceCorrespondence (capitalReduction capital)
      (capitalSorted capital)
assembledCapitalIgnoresBareCoherentMap nameEq keyEq protocol original capital
  alternate = Refl

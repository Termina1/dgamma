module DGamma.CP5O20RootReplayLawProducerSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O20RootOrdinalBoundarySpike
import Decidable.Equality

%default total
%unbound_implicits off

||| Every actual finite adjacent derivation owns its stored root ordinal law.
||| The step uses the SAME enriched fold projected by its occurrence map.
export
0 o20FiniteAdjacentRootReplayOrdinals :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} ->
  {target : Transitions initial targetFinal} ->
  (derivation : FiniteAdjacentSwapDerivation name key world error value protocol
    nameEq keyEq source target) ->
  O20RootReplayOrdinals name key world error value
    (finiteDerivationOccurrenceCorrespondence derivation)
o20FiniteAdjacentRootReplayOrdinals {source} FiniteAdjacentSwapDone =
  o20IdentityRootReplayOrdinals source
o20FiniteAdjacentRootReplayOrdinals
  (FiniteAdjacentSwapStep original tracePrefix left right suffix orientation
    diamond result target rest) =
  o20ComposeRootReplayOrdinals (swappedOccurrenceCorrespondence result)
    (finiteDerivationOccurrenceCorrespondence rest)
    (MkO20RootReplayOrdinals
      (operationalRootOrdinalPreserved (swappedOccurrenceFold result)))
    (o20FiniteAdjacentRootReplayOrdinals rest)

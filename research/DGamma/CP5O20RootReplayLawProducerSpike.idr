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

||| The actual deletion occurrence builder inherits the root law of its SAME
||| supplied operational capital, not a separately reconstructed generation map.
export
0 o20DeletionProducerRootReplayOrdinals :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq trace) ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq trace) ->
  (result : DeletionResult name key world error value nameEq keyEq trace
    (selectedActor candidate) (selectedEpisode candidate)
    (selectedRegistrations candidate) (selectedStartOrdinal candidate)
    (selectedStartLive candidate)) ->
  (capital : DeletionProducerOperationalCapital name key world error value
    nameEq keyEq trace (selectedActor candidate) (selectedEpisode candidate)
    (selectedRegistrations candidate) (selectedStartOrdinal candidate)
    (selectedStartLive candidate) result) ->
  O20RootReplayOrdinals name key world error value
    (deletionOperationalCorrespondence
      (deletionStepOperationalOccurrenceFoldSpike nameEq keyEq protocol trace
        premises candidate result capital))
o20DeletionProducerRootReplayOrdinals trace premises candidate result capital =
  MkO20RootReplayOrdinals
    (deletionBuiltRootOrdinalPreserved trace premises candidate result capital)

||| Transport the built root law along the step's OWN stored correspondence
||| exactness equation; no equality between independently rebuilt maps is input.
export
0 o20DeletionStepRootReplayOrdinals :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq trace) ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq trace) ->
  (step : DeletionChainStep name key world error value protocol nameEq keyEq
    trace premises candidate) ->
  O20RootReplayOrdinals name key world error value
    (deletionOccurrenceCorrespondence step)
o20DeletionStepRootReplayOrdinals {name} {key} {world} {error} {value}
  trace premises candidate step =
  replace {p = \correspondence =>
    O20RootReplayOrdinals name key world error value correspondence}
    (sym (deletionOccurrenceCorrespondenceExact step))
    (o20DeletionProducerRootReplayOrdinals trace premises candidate
      (deletionResult step) (deletionProducerCapital step))

||| The whole actual deletion derivation owns root ordinals by identity and
||| composition of its exact stored step correspondences.
export
0 o20ClosingFreeDeletionRootReplayOrdinals :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} ->
  {target : Transitions initial targetFinal} ->
  (derivation : ClosingFreeDeletionDerivation name key world error value protocol
    nameEq keyEq source target) ->
  O20RootReplayOrdinals name key world error value
    (closingFreeDeletionOccurrenceFold derivation)
o20ClosingFreeDeletionRootReplayOrdinals (ClosingFreeDeletionDone trace) =
  o20IdentityRootReplayOrdinals trace
o20ClosingFreeDeletionRootReplayOrdinals
  (ClosingFreeDeletionStep trace premises candidate step target rest) =
  o20ComposeRootReplayOrdinals (deletionOccurrenceCorrespondence step)
    (closingFreeDeletionOccurrenceFold rest)
    (o20DeletionStepRootReplayOrdinals trace premises candidate step)
    (o20ClosingFreeDeletionRootReplayOrdinals rest)

||| The actual accepted canonical correspondence owns its root law. The
||| capital's own producer equation exposes the same deletion and sorting folds.
export
0 o20CanonicalRootReplayOrdinals :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, finalState : SystemState name key value world error} ->
  {original : Transitions initial finalState} ->
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  O20RootReplayOrdinals name key world error value
    (canonicalOccurrenceCorrespondence capital)
o20CanonicalRootReplayOrdinals
  (MkIndependentCanonicalSchedule premises reduction ordering sorted
    supportTransport accounting _ Refl classified) =
  o20ComposeRootReplayOrdinals (reductionOccurrenceCorrespondence reduction)
    (sortingOccurrenceCorrespondence sorted)
    (o20ClosingFreeDeletionRootReplayOrdinals
      (reductionDeletionDerivation reduction))
    (o20FiniteAdjacentRootReplayOrdinals (sortingAdjacentDerivation sorted))

||| Every actual operational actor permutation owns root ordinals through the
||| finite adjacent derivation stored by each of its whole-block swaps.
export
0 o20OperationalRootReplayOrdinals :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {sourceOrder, targetOrder : List name} ->
  {certificate : CertifiedActorPermutation name sourceOrder targetOrder} ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {sourceTrace : Transitions initial sourceFinal} ->
  {sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace} ->
  {sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace} ->
  {targetTrace : Transitions initial targetFinal} ->
  (replay : OperationalActorPermutation name key world error value protocol
    nameEq keyEq certificate sourceTrace sourceBlocks sourcePremises targetTrace) ->
  O20RootReplayOrdinals name key world error value
    (operationalPermutationOccurrenceCorrespondence replay)
o20OperationalRootReplayOrdinals {sourceTrace}
  (OperationalActorDone blocks premises) = o20IdentityRootReplayOrdinals sourceTrace
o20OperationalRootReplayOrdinals
  (OperationalActorStep orderSwap restCertificate blocks premises safety step rest) =
  o20ComposeRootReplayOrdinals (blockSwapOccurrenceCorrespondence step)
    (operationalPermutationOccurrenceCorrespondence rest)
    (o20FiniteAdjacentRootReplayOrdinals
      (wholeBlockFiniteDerivation (blockSwapWholeDerivation step)))
    (o20OperationalRootReplayOrdinals rest)

||| Compose the canonical law with the root law of an ACTUAL operational
||| derivation starting at that same canonical trace, with no supplied map law.
export
0 o20CanonicalOperationalRootReplayOrdinals :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, originalFinal, targetFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  {sourceOrder, targetOrder : List name} ->
  {certificate : CertifiedActorPermutation name sourceOrder targetOrder} ->
  {sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder (canonicalTrace (canonicalSchedule capital))} ->
  {sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq (canonicalTrace (canonicalSchedule capital))} ->
  {targetTrace : Transitions initial targetFinal} ->
  (replay : OperationalActorPermutation name key world error value protocol
    nameEq keyEq certificate (canonicalTrace (canonicalSchedule capital))
    sourceBlocks sourcePremises targetTrace) ->
  O20RootReplayOrdinals name key world error value
    (composeActionRegistrationReplayCorrespondence
      (canonicalOccurrenceCorrespondence capital)
      (operationalPermutationOccurrenceCorrespondence replay))
o20CanonicalOperationalRootReplayOrdinals capital replay =
  o20ComposeRootReplayOrdinals (canonicalOccurrenceCorrespondence capital)
    (operationalPermutationOccurrenceCorrespondence replay)
    (o20CanonicalRootReplayOrdinals capital)
    (o20OperationalRootReplayOrdinals replay)

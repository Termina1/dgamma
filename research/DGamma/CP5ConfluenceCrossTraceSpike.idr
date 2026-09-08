module DGamma.CP5ConfluenceCrossTraceSpike

import public DGamma.CP5O19SurfaceSpike
import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5AcceptedSupportTruthSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

public export
data CertifiedActorPermutation :
  (name : Type) -> List name -> List name -> Type where
  ActorPermutationDone : CertifiedActorPermutation name order order
  ActorPermutationStep :
    AdjacentActorOrderSwap name before middle ->
    CertifiedActorPermutation name middle after ->
    CertifiedActorPermutation name before after

||| A shifted block-start/compensating-position alias is impossible at the
||| authoritative whole-block boundary, even though isolated caller blocks can
||| be arithmetically aliased.
public export
0 wholeSelectedCoordinateAliasImpossible :
  (whole : WholeBlockSwapDerivation name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises safety targetTrace) ->
  (leftPosition, rightPosition : Nat) ->
  LTE (S leftPosition) (actorBlockTransitionCount (decomposedBlock sourceBlocks
    (actorLeft orderSwap) (safetyLeftInOrder safety))) ->
  LTE (S rightPosition) (actorBlockTransitionCount (decomposedBlock sourceBlocks
    (actorRight orderSwap) (safetyRightInOrder safety))) ->
  transitionCount (traceBeforeBlock (decomposedBlock sourceBlocks
    (actorLeft orderSwap) (safetyLeftInOrder safety))) + leftPosition =
  transitionCount (traceBeforeBlock (decomposedBlock sourceBlocks
    (actorRight orderSwap) (safetyRightInOrder safety))) + rightPosition ->
  Void
wholeSelectedCoordinateAliasImpossible {safety} whole leftPosition rightPosition
  leftBound rightBound exact =
    selectedLeftRightRangesDisjoint
      (selectedBlockCoordinateInjectivity safety)
      leftPosition rightPosition leftBound rightBound exact

public export
wholeBlockFiniteDerivation :
  WholeBlockSwapDerivation name key world error value protocol nameEq keyEq
    orderSwap sourceTrace sourceBlocks sourcePremises safety targetTrace ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq
    sourceTrace targetTrace
wholeBlockFiniteDerivation whole =
  nonEmptyToFiniteAdjacentSwapDerivation (nonEmptyBlockDerivation whole)

||| One actual whole-block transposition.  The finite derivation is mandatory:
||| every transition crossing is classified A/A, A/O, O/A, or O/O and carries
||| its concrete `AdjacentSwapResult`, including action/registration occurrence
||| correspondence.  Endpoint assertions alone cannot construct this record.
public export
record OperationalAdjacentBlockSwap
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {sourceOrder, targetOrder : List name}
  (orderSwap : AdjacentActorOrderSwap name sourceOrder targetOrder)
  {initial, sourceFinal : SystemState name key value world error}
  (sourceTrace : Transitions initial sourceFinal)
  (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace)
  (sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace)
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises) where
  constructor MkOperationalAdjacentBlockSwap
  blockSwapFinal : SystemState name key value world error
  blockSwapTrace : Transitions initial blockSwapFinal
  blockSwapWholeDerivation : WholeBlockSwapDerivation name key world error value
    protocol nameEq keyEq orderSwap sourceTrace sourceBlocks sourcePremises safety
      blockSwapTrace
  blockSwapBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    targetOrder blockSwapTrace
  blockSwapEndpoint : RelationalReplayEndpoint name key world error value nameEq
    keyEq sourceFinal blockSwapFinal
  blockSwapPremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq blockSwapTrace
  blockSwapSameExternalInputs : SameExternalOrchestration nameEq sourceTrace
    blockSwapTrace

public export
0 blockSwapReplayCorrespondence :
  (step : OperationalAdjacentBlockSwap name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises safety) ->
  RelationalReplayCorrespondence name key world error value sourceTrace
    (blockSwapTrace step)
blockSwapReplayCorrespondence step =
  finiteDerivationReplayCorrespondence
    (wholeBlockFiniteDerivation (blockSwapWholeDerivation step))

public export
0 blockSwapOccurrenceCorrespondence :
  (step : OperationalAdjacentBlockSwap name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises safety) ->
  ActionRegistrationReplayCorrespondence name key world error value sourceTrace
    (blockSwapTrace step)
blockSwapOccurrenceCorrespondence step =
  finiteDerivationOccurrenceCorrespondence
    (wholeBlockFiniteDerivation (blockSwapWholeDerivation step))

||| Exact one-step operational producer.  Its proof must enumerate the finite
||| Cartesian crossing of the two located blocks, derive early applicability and
||| orientation-specific premises from the current bundle/safety, invoke the
||| four local diamonds, and splice every `AdjacentSwapResult`.
public export
0 operationalAdjacentBlockSwapSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} ->
  (orderSwap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} ->
  (sourceTrace : Transitions initial sourceFinal) ->
  (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace) ->
  (sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace) ->
  (0 sourceUnique : UniqueRawNameInsertions name key world error value nameEq keyEq sourceTrace) ->
  (applicableSafety : AdjacentActorSwapSafety name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises) ->
  OperationalAdjacentBlockSwap name key world error value protocol nameEq keyEq
    orderSwap sourceTrace sourceBlocks sourcePremises applicableSafety
operationalAdjacentBlockSwapSpike = ?operationalAdjacentBlockSwapSpike_rhs

||| Every selected list step is now indexed by exact operational safety and its
||| realized block replay.  A caller cannot prepend a pure swap/inverse loop
||| without also constructing both intermediate safety proofs and finite local
||| diamond derivations.
public export
data OperationalActorPermutation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {sourceOrder, targetOrder : List name} ->
  (certificate : CertifiedActorPermutation name sourceOrder targetOrder) ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  (sourceTrace : Transitions initial sourceFinal) ->
  (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace) ->
  (sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace) ->
  (targetTrace : Transitions initial targetFinal) -> Type where
  OperationalActorDone :
    (blocks : ActorBlockDecomposition name key world error value nameEq keyEq
      order trace) ->
    (premises : ReplayInvariantBundle name key world error value protocol nameEq
      keyEq trace) ->
    OperationalActorPermutation name key world error value protocol nameEq keyEq
      ActorPermutationDone trace blocks premises trace
  OperationalActorStep :
    (orderSwap : AdjacentActorOrderSwap name before middle) ->
    (restCertificate : CertifiedActorPermutation name middle after) ->
    (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
      before sourceTrace) ->
    (sourcePremises : ReplayInvariantBundle name key world error value protocol
      nameEq keyEq sourceTrace) ->
    (safety : AdjacentActorSwapSafety name key world error value protocol nameEq
      keyEq orderSwap sourceTrace sourceBlocks sourcePremises) ->
    (step : OperationalAdjacentBlockSwap name key world error value protocol
      nameEq keyEq orderSwap sourceTrace sourceBlocks sourcePremises safety) ->
    (rest : OperationalActorPermutation name key world error value protocol
      nameEq keyEq restCertificate (blockSwapTrace step) (blockSwapBlocks step)
        (blockSwapPremises step) targetTrace) ->
    OperationalActorPermutation name key world error value protocol nameEq keyEq
      (ActorPermutationStep orderSwap restCertificate) sourceTrace sourceBlocks
        sourcePremises targetTrace

public export
0 operationalPermutationReplayCorrespondence :
  OperationalActorPermutation name key world error value protocol nameEq keyEq
    certificate sourceTrace sourceBlocks sourcePremises targetTrace ->
  RelationalReplayCorrespondence name key world error value sourceTrace targetTrace
operationalPermutationReplayCorrespondence
  (OperationalActorDone blocks premises) =
    MkRelationalReplayCorrespondence (\actor, generator => generator)
      (\observedKeyEq, actor, generator =>
        replayTraceGeneratorMapRespects observedKeyEq generator)
      (\actor, stage => stage)
      (\actor, stage, state => Refl)
operationalPermutationReplayCorrespondence
  (OperationalActorStep orderSwap restCertificate sourceBlocks sourcePremises
    safety step rest) =
      composeRelationalReplayCorrespondence (blockSwapReplayCorrespondence step)
        (operationalPermutationReplayCorrespondence rest)

public export
0 operationalPermutationOccurrenceCorrespondence :
  {sourceOrder, targetOrder : List name} ->
  {certificate : CertifiedActorPermutation name sourceOrder targetOrder} ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {sourceTrace : Transitions initial sourceFinal} ->
  {sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace} ->
  {sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace} ->
  {targetTrace : Transitions initial targetFinal} ->
  (replay : OperationalActorPermutation name key world error value protocol nameEq
    keyEq certificate sourceTrace sourceBlocks sourcePremises targetTrace) ->
  ActionRegistrationReplayCorrespondence name key world error value sourceTrace
    targetTrace
operationalPermutationOccurrenceCorrespondence {sourceTrace}
  (OperationalActorDone blocks premises) =
    identityActionRegistrationReplayCorrespondence sourceTrace
operationalPermutationOccurrenceCorrespondence
  (OperationalActorStep orderSwap restCertificate sourceBlocks sourcePremises
    safety step rest) =
      composeActionRegistrationReplayCorrespondence
        (blockSwapOccurrenceCorrespondence step)
        (operationalPermutationOccurrenceCorrespondence rest)

||| Endpoint quotients compose along the sealed operational permutation fold.
||| This is the O20-independent projection needed to package a replayed left
||| execution from O19 capital.
public export
0 operationalPermutationEndpoint :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {sourceOrder, targetOrder : List name} ->
  {certificate : CertifiedActorPermutation name sourceOrder targetOrder} ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {sourceTrace : Transitions initial sourceFinal} ->
  {sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace} ->
  {sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace} ->
  {targetTrace : Transitions initial targetFinal} ->
  OperationalActorPermutation name key world error value protocol nameEq keyEq
    certificate sourceTrace sourceBlocks sourcePremises targetTrace ->
  RelationalReplayEndpoint name key world error value nameEq keyEq sourceFinal
    targetFinal
operationalPermutationEndpoint nameEq keyEq
  (OperationalActorDone blocks premises) =
    relationalReplayEndpointReflexiveSpike nameEq keyEq _
      (replayFinalWellFormed premises)
operationalPermutationEndpoint nameEq keyEq
  (OperationalActorStep orderSwap restCertificate sourceBlocks sourcePremises
    safety step rest) =
      relationalReplayEndpointTransitiveSpike nameEq keyEq _ _ _
        (blockSwapEndpoint step)
        (operationalPermutationEndpoint nameEq keyEq rest)

||| External-input filtering is likewise transitive over the same sealed fold.
public export
0 operationalPermutationSameExternalInputs :
  (nameEq : DecEq name) ->
  {sourceOrder, targetOrder : List name} ->
  {certificate : CertifiedActorPermutation name sourceOrder targetOrder} ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {sourceTrace : Transitions initial sourceFinal} ->
  {sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace} ->
  {sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace} ->
  {targetTrace : Transitions initial targetFinal} ->
  OperationalActorPermutation name key world error value protocol nameEq keyEq
    certificate sourceTrace sourceBlocks sourcePremises targetTrace ->
  SameExternalOrchestration nameEq sourceTrace targetTrace
operationalPermutationSameExternalInputs nameEq
  (OperationalActorDone blocks premises) =
    sameExternalOrchestrationReflexiveSpike nameEq _
operationalPermutationSameExternalInputs nameEq
  (OperationalActorStep orderSwap restCertificate sourceBlocks sourcePremises
    safety step rest) =
      sameExternalOrchestrationTransitiveSpike nameEq
        (blockSwapSameExternalInputs step)
        (operationalPermutationSameExternalInputs nameEq rest)

||| Cross-trace support matching now contains no certificate at all.  It is
||| publicly constructible without risk because O20 never consumes it as an
||| operational schedule; it records only renamed set equality.
public export
record MappedCanonicalSupportOrders
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftFinal, rightFinal : SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal)
  (rightTrace : Transitions initial rightFinal)
  (renaming : NameBijection name)
  (leftSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq leftTrace)
  (rightSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq rightTrace) where
  constructor MkMappedCanonicalSupportOrders
  0 leftSupportMapped : (n : name) -> Elem n (supportOrder leftSchedule) ->
    Elem (renameForward renaming n) (supportOrder rightSchedule)
  0 rightSupportMapped : (n : name) -> Elem n (supportOrder rightSchedule) ->
    Elem (renameBackward renaming n) (supportOrder leftSchedule)

||| Turn pointwise forward support preservation into membership in the right
||| canonical enumeration.  Uniqueness/order concerns remain owned by each
||| schedule's `LinearizesSupport`; this helper performs only one membership
||| elimination.
0 canonicalSupportOrderForwardFromTruth :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {leftInitial, rightInitial, leftFinal, rightFinal :
    SystemState name key value world error} ->
  {leftTrace : Transitions leftInitial leftFinal} ->
  {rightTrace : Transitions rightInitial rightFinal} ->
  (renaming : NameBijection name) ->
  (leftSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq leftTrace) ->
  (rightSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq rightTrace) ->
  ((selected : name) ->
    (isSupported @{nameEq} @{keyEq} selected leftFinal = True) ->
    (isSupported @{nameEq} @{keyEq} (renameForward renaming selected)
      rightFinal = True)) ->
  (selected : name) -> Elem selected (supportOrder leftSchedule) ->
  Elem (renameForward renaming selected) (supportOrder rightSchedule)
canonicalSupportOrderForwardFromTruth nameEq keyEq protocol renaming
  leftSchedule rightSchedule supportForward selected selectedIn =
    orderComplete (supportLinearization rightSchedule)
      (renameForward renaming selected)
      (supportForward selected
        (orderSound (supportLinearization leftSchedule) selected selectedIn))

||| Symmetric membership lift for the inverse name map.
0 canonicalSupportOrderBackwardFromTruth :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {leftInitial, rightInitial, leftFinal, rightFinal :
    SystemState name key value world error} ->
  {leftTrace : Transitions leftInitial leftFinal} ->
  {rightTrace : Transitions rightInitial rightFinal} ->
  (renaming : NameBijection name) ->
  (leftSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq leftTrace) ->
  (rightSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq rightTrace) ->
  ((selected : name) ->
    (isSupported @{nameEq} @{keyEq} selected rightFinal = True) ->
    (isSupported @{nameEq} @{keyEq} (renameBackward renaming selected)
      leftFinal = True)) ->
  (selected : name) -> Elem selected (supportOrder rightSchedule) ->
  Elem (renameBackward renaming selected) (supportOrder leftSchedule)
canonicalSupportOrderBackwardFromTruth nameEq keyEq protocol renaming
  leftSchedule rightSchedule supportBackward selected selectedIn =
    orderComplete (supportLinearization leftSchedule)
      (renameBackward renaming selected)
      (supportBackward selected
        (orderSound (supportLinearization rightSchedule) selected selectedIn))

||| Exact O19 set-matching assembly once both semantic support directions have
||| been obtained from the generation/current-endpoint correspondence.
0 canonicalSupportOrdersFromTruth :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (renaming : NameBijection name) ->
  (leftSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq leftTrace) ->
  (rightSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq rightTrace) ->
  ((selected : name) ->
    (isSupported @{nameEq} @{keyEq} selected leftFinal = True) ->
    (isSupported @{nameEq} @{keyEq} (renameForward renaming selected)
      rightFinal = True)) ->
  ((selected : name) ->
    (isSupported @{nameEq} @{keyEq} selected rightFinal = True) ->
    (isSupported @{nameEq} @{keyEq} (renameBackward renaming selected)
      leftFinal = True)) ->
  MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq
    leftTrace rightTrace renaming leftSchedule rightSchedule
canonicalSupportOrdersFromTruth nameEq keyEq protocol leftTrace rightTrace
  renaming leftSchedule rightSchedule supportForward supportBackward =
    MkMappedCanonicalSupportOrders
      (canonicalSupportOrderForwardFromTruth nameEq keyEq protocol renaming
        leftSchedule rightSchedule supportForward)
      (canonicalSupportOrderBackwardFromTruth nameEq keyEq protocol renaming
        leftSchedule rightSchedule supportBackward)

public export
0 canonicalSupportOrdersMatchSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  (0 leftRightGeneratedMatched : GeneratedOrchestrationMatched name key world error value nameEq
    leftTrace rightTrace (generatedGenerationBijection sameInputs)) ->
  MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq
    leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)
canonicalSupportOrdersMatchSpike {name} {key} {world} {error} {value} nameEq keyEq protocol
  leftTrace rightTrace sameInputs leftCapital rightCapital leftUnique rightUnique leftRightGeneratedMatched =
    canonicalSupportOrdersFromTruth nameEq keyEq protocol leftTrace rightTrace
      (currentNameBijection (endpointRenaming sameInputs)) (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)
      (acceptedSupportedTruthForward name key world error value nameEq keyEq protocol leftTrace rightTrace sameInputs leftRightGeneratedMatched
        (replayAligned (chainReplayCapital (capitalPremises leftCapital)))
        (replayAligned (chainReplayCapital (capitalPremises rightCapital)))
        (replayDiscipline (chainReplayCapital (capitalPremises leftCapital)))
        (replayInitialEmpty (chainReplayCapital (capitalPremises leftCapital))) leftUnique rightUnique)
      (acceptedSupportedTruthBackward name key world error value nameEq keyEq protocol leftTrace rightTrace sameInputs leftRightGeneratedMatched
        (replayAligned (chainReplayCapital (capitalPremises leftCapital)))
        (replayAligned (chainReplayCapital (capitalPremises rightCapital)))
        (replayDiscipline (chainReplayCapital (capitalPremises rightCapital)))
        (replayInitialEmpty (chainReplayCapital (capitalPremises leftCapital))) leftUnique rightUnique)

||| The bridge-facing capital exposes the exact first-state blocks consumed by
||| O19 together with the producer's disjoint-range invariant.
public export
canonicalActorBlockDecomposition :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  ActorBlockDecomposition name key world error value nameEq keyEq
    (supportOrder (canonicalSchedule capital))
    (canonicalTrace (canonicalSchedule capital))
canonicalActorBlockDecomposition
  (MkIndependentCanonicalSchedule premises reduction ordering sorted
    supportTransport accounting _ Refl classified) =
      MkActorBlockDecomposition (sortedBlock sorted)
        (sortedBlocksFollowOrder sorted) (sortedBlockRangesDisjoint sorted)
        (sortedLifecycleCoverage sorted)

||| Sealed-by-evidence O19 output.  The pure certificate and every exact
||| intermediate trace are existential fields of the same package as the
||| operational realization; there is no function from a public pure
||| certificate to O20.
public export
record CertifiedOperationalCanonicalPermutation
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftFinal, rightFinal : SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal)
  (rightTrace : Transitions initial rightFinal)
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace)
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace)
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace)
  (matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)) where
  constructor MkCertifiedOperationalCanonicalPermutation
  selectedActorPermutation : CertifiedActorPermutation name
    (supportOrder (canonicalSchedule leftCapital))
    (map (renameBackward (currentNameBijection (endpointRenaming sameInputs)))
      (supportOrder (canonicalSchedule rightCapital)))
  operationalTargetFinal : SystemState name key value world error
  operationalTargetTrace : Transitions initial operationalTargetFinal
  operationalTargetBlocks : ActorBlockDecomposition name key world error value
    nameEq keyEq
    (map (renameBackward (currentNameBijection (endpointRenaming sameInputs)))
      (supportOrder (canonicalSchedule rightCapital))) operationalTargetTrace
  operationalTargetPremises : ReplayInvariantBundle name key world error value
    protocol nameEq keyEq operationalTargetTrace
  selectedPermutationRealized : OperationalActorPermutation name key world error
    value protocol nameEq keyEq selectedActorPermutation
    (canonicalTrace (canonicalSchedule leftCapital))
    (canonicalActorBlockDecomposition leftCapital)
    (canonicalReplayPremises leftCapital) operationalTargetTrace

||| O19 must choose a permutation and realize it simultaneously.  This is the
||| remaining existence risk when accepted support relations differ through
||| withdrawn intermediates; the type no longer hides that risk in O20.
public export
0 selectOperationalCanonicalPermutationSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  (0 leftRightGeneratedMatched : GeneratedOrchestrationMatched name key world error value nameEq
    leftTrace rightTrace (generatedGenerationBijection sameInputs)) ->
  (matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)) ->
  CertifiedOperationalCanonicalPermutation name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital matching
selectOperationalCanonicalPermutationSpike =
  ?selectOperationalCanonicalPermutationSpike_rhs

||| Honest revision-6 label: this is a static accepted-index interface test, not
||| a concrete reachable O19/O20 run.  It proves that the old full-path field is
||| absent while preserving the exact scanner-deleted birth and real path.
public export
record IntermediateVestigialStaticInterfaceRegression
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftFinal, rightFinal : SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal)
  (rightTrace : Transitions initial rightFinal)
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace)
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace)
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace)
  (matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital))
  (lower, withdrawnMiddle, upper : name) where
  constructor MkIntermediateVestigialStaticInterfaceRegression
  pathThroughWithdrawnIntermediate : SupportPath nameEq leftFinal lower upper
  preciseWithdrawnBirth : RegistrationGeneration name
  0 preciseWithdrawnBirthCurrent : lookupCurrentGeneration @{nameEq}
    withdrawnMiddle (leftFinalGenerations (generatedRegistrationTree sameInputs)) =
      Just preciseWithdrawnBirth
  0 preciseWithdrawnBirthDeleted : Elem preciseWithdrawnBirth
    (leftDeletedGenerations (generatedRegistrationTree sameInputs))
  0 withdrawnIntermediateAbsentRight :
    lookupFiber @{nameEq} {key = key} {value = value} {world = world}
      {error = error}
      (renameForward (currentNameBijection (endpointRenaming sameInputs))
        withdrawnMiddle) (registry rightFinal) = Nothing
  0 withdrawnIntermediateNotAnActor :
    Elem withdrawnMiddle (supportOrder (canonicalSchedule leftCapital)) -> Void

public export
intermediateVestigialStaticInterfaceRegression :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace} ->
  (matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)) ->
  (lower, withdrawnMiddle, upper : name) ->
  SupportEdge nameEq leftFinal lower withdrawnMiddle ->
  SupportPath nameEq leftFinal withdrawnMiddle upper ->
  (leftVestigial : VestigialEndpointGeneration name key world error value nameEq
    keyEq (leftFinalGenerations (generatedRegistrationTree sameInputs))
      (leftDeletedGenerations (generatedRegistrationTree sameInputs))
      withdrawnMiddle leftFinal) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error}
    (renameForward (currentNameBijection (endpointRenaming sameInputs))
      withdrawnMiddle) (registry rightFinal) = Nothing ->
  IntermediateVestigialStaticInterfaceRegression name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital
      matching lower withdrawnMiddle upper
intermediateVestigialStaticInterfaceRegression matching lower withdrawnMiddle
  upper pathFirst pathRest leftVestigial rightAbsent =
    MkIntermediateVestigialStaticInterfaceRegression
      (SupportPathMore pathFirst pathRest)
      (vestigialGeneration leftVestigial)
      (vestigialGenerationCurrent leftVestigial)
      (vestigialBirthDiscarded leftVestigial)
      rightAbsent
      (\middleIn => case trans
        (sym (orderSound
          (supportLinearization (canonicalSchedule leftCapital))
          withdrawnMiddle middleIn))
        (vestigialUnsupported leftVestigial) of Refl impossible)

||| O20 packages the exact already-safe operational target with its endpoint
||| quotient and bridge.  Occurrence correspondence is derived structurally from
||| the sealed operational fold, not asserted from effect-generator capital.
public export
record PermutedCanonicalExecution
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftFinal, rightFinal : SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal)
  (rightTrace : Transitions initial rightFinal)
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace)
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace)
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace)
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)}
  (operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching) where
  constructor MkPermutedCanonicalExecution
  composedPermutationEndpoint : RelationalReplayEndpoint name key world error
    value nameEq keyEq (canonicalFinal (canonicalSchedule leftCapital))
      (operationalTargetFinal operational)
  permutationSameExternalInputs : SameExternalOrchestration nameEq
    (canonicalTrace (canonicalSchedule leftCapital))
      (operationalTargetTrace operational)

||| O19's sealed fold already contains both fields of the replayed-execution
||| wrapper; no O20 endpoint comparison is needed for this assembly.
0 permutedCanonicalExecutionFromOperational :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace} ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  (operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching) ->
  PermutedCanonicalExecution name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital operational
permutedCanonicalExecutionFromOperational nameEq keyEq operational =
  MkPermutedCanonicalExecution
    (operationalPermutationEndpoint nameEq keyEq
      (selectedPermutationRealized operational))
    (operationalPermutationSameExternalInputs nameEq
      (selectedPermutationRealized operational))

public export
0 permutationReplayCorrespondence :
  {operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching} ->
  PermutedCanonicalExecution name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital operational ->
  RelationalReplayCorrespondence name key world error value
    (canonicalTrace (canonicalSchedule leftCapital))
    (operationalTargetTrace operational)
permutationReplayCorrespondence {operational} execution =
  operationalPermutationReplayCorrespondence
    (selectedPermutationRealized operational)

public export
0 permutationOccurrenceCorrespondence :
  {operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching} ->
  PermutedCanonicalExecution name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital operational ->
  ActionRegistrationReplayCorrespondence name key world error value
    (canonicalTrace (canonicalSchedule leftCapital))
    (operationalTargetTrace operational)
permutationOccurrenceCorrespondence {operational} execution =
  operationalPermutationOccurrenceCorrespondence
    (selectedPermutationRealized operational)

public export
record CanonicalConvergenceResult
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftFinal, rightFinal : SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal)
  (rightTrace : Transitions initial rightFinal)
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace)
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace)
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace)
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)}
  (operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching) where
  constructor MkCanonicalConvergenceResult
  permutedLeftExecution : PermutedCanonicalExecution name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital
      operational
  convergenceBridge : ReplayedCanonicalEndpointBridge name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      (operationalTargetTrace operational)
      (permutationOccurrenceCorrespondence permutedLeftExecution) rightCapital

||| Exact final O20 assembly once the operational replay-to-right endpoint bridge
||| is available.  O19 already supplies the permuted execution wrapper.
0 canonicalConvergenceFromBridge :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace} ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  (operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching) ->
  (bridge : ReplayedCanonicalEndpointBridge name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      (operationalTargetTrace operational)
      (permutationOccurrenceCorrespondence
        (permutedCanonicalExecutionFromOperational nameEq keyEq operational))
      rightCapital) ->
  CanonicalConvergenceResult name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital operational
canonicalConvergenceFromBridge nameEq keyEq operational bridge =
  MkCanonicalConvergenceResult
    (permutedCanonicalExecutionFromOperational nameEq keyEq operational) bridge

||| O20 no longer quantifies over a public pure certificate.  It accepts only
||| O19's package containing exact safety and finite local derivations.
public export
0 canonicalSchedulesConvergeSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  (0 leftRightGeneratedMatched : GeneratedOrchestrationMatched name key world error value nameEq
    leftTrace rightTrace (generatedGenerationBijection sameInputs)) ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  (operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching) ->
  CanonicalConvergenceResult name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital operational
canonicalSchedulesConvergeSpike = ?canonicalSchedulesConvergeSpike_rhs

public export
0 originalEndpointsConvergeSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  (0 leftRightGeneratedMatched : GeneratedOrchestrationMatched name key world error value nameEq
    leftTrace rightTrace (generatedGenerationBijection sameInputs)) ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  {operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching} ->
  CanonicalConvergenceResult name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital operational ->
  SystemEquivalentByRenamingModuloVestigial name key world error value nameEq
    keyEq (generatedRegistrationTree sameInputs)
    (currentNameBijection (endpointRenaming sameInputs))
originalEndpointsConvergeSpike nameEq keyEq protocol leftTrace rightTrace
  sameInputs leftCapital rightCapital leftUnique rightUnique leftRightGeneratedMatched convergence =
    replayedCanonicalToOriginalEndpointSpike nameEq keyEq protocol leftTrace
      rightTrace sameInputs leftCapital rightCapital leftUnique rightUnique leftRightGeneratedMatched
      (acceptedDeletionScannerCapitalSpike nameEq keyEq protocol leftTrace
        rightTrace sameInputs leftCapital rightCapital)
      (operationalTargetTrace operational)
      (permutationReplayCorrespondence (permutedLeftExecution convergence))
      (composedPermutationEndpoint (permutedLeftExecution convergence))
      (permutationOccurrenceCorrespondence (permutedLeftExecution convergence))
      (convergenceBridge convergence)

||| Once the two schedules and exact original endpoint bridge are available,
||| the accepted result is direct constructor assembly.
public export
0 confluenceResultFromCanonicalCapital :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace) ->
  (leftSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq leftTrace) ->
  (rightSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq rightTrace) ->
  (equivalent : SystemEquivalentByRenamingModuloVestigial name key world error
    value nameEq keyEq (generatedRegistrationTree sameInputs)
      (currentNameBijection (endpointRenaming sameInputs))) ->
  ConfluenceResult name key world error value protocol nameEq keyEq leftTrace
    rightTrace (generatedGenerationBijection sameInputs)
    (currentNameBijection (endpointRenaming sameInputs))
confluenceResultFromCanonicalCapital nameEq keyEq protocol leftTrace rightTrace
  sameInputs leftSchedule rightSchedule equivalent =
    MkConfluenceResult leftSchedule rightSchedule
      (generatedRegistrationTree sameInputs)
      (endpointRenaming sameInputs) equivalent

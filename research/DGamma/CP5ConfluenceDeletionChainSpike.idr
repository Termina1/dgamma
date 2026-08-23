module DGamma.CP5ConfluenceDeletionChainSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionTheorem
import DGamma.CP4Support
import DGamma.CP5ConfluenceLocalDiamondSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

||| Structural measure for delete-then-match Path A.
public export
traceLength : Transitions first finalState -> Nat
traceLength NoTransitions = 0
traceLength (MoreTransitions transition rest) = S (traceLength rest)

public export
NoClosingEpisodes :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  Transitions initial finalState -> Type
NoClosingEpisodes name key world error value nameEq keyEq trace =
  (selected : name) ->
  LocatedClosedEpisode name key world error value nameEq keyEq selected trace ->
  Void

||| Recursive capital is exactly the shared deletion/swap replay bundle.  In
||| particular, every survivor carries fresh `ReachedFromEmpty` ingredients,
||| precedence/support acyclicity, provenance, ranks, Lemma-70 support equality,
||| and transported Definition-60 independence.
public export
record CanonicalizationPremises
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkCanonicalizationPremises
  chainReplayCapital : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq trace

public export
0 chainReachedFromEmpty :
  {trace : Transitions initial finalState} ->
  CanonicalizationPremises name key world error value protocol nameEq keyEq trace ->
  ReachedFromEmpty name key world error value nameEq keyEq finalState
chainReachedFromEmpty premises = replayReachedFromEmpty (chainReplayCapital premises)

||| All occurrence-local inputs needed for one checked Lemma-72 call.
public export
record DeletableClosingEpisode
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkDeletableClosingEpisode
  selectedActor : name
  selectedEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    selectedActor trace
  selectedRegistrations : List (RegistrationGeneration name)
  0 selectedOutsideRegistrations :
    (generation : RegistrationGeneration name) ->
    Elem generation selectedRegistrations ->
    Not (generationName generation = selectedActor)
  selectedStartOrdinal : Nat
  selectedStartLive : GenerationEnvironment name
  0 selectedBeforeScan : GenerationTraceScan nameEq 0 []
    (traceBeforeOpening selectedEpisode) selectedStartOrdinal selectedStartLive
  0 selectedRegisteredDuring : RegisteredGenerationsDuring selectedActor
    selectedStartOrdinal selectedRegistrations
    (MoreTransitions
      (beginTransition (closedOpening (locatedEpisode selectedEpisode)))
      (closedTransitions (locatedEpisode selectedEpisode)))
  0 selectedNoDependentClose : NoDependentClosingEpisode
    {nameEq = nameEq} {keyEq = keyEq} selectedActor trace
  0 selectedChildrenHaveNoEpisode : NoRegisteredEpisode nameEq
    selectedRegistrations 0 [] trace

||| O7 scan entry: the dependent pair retains the exact actor and located closed
||| episode while the executable ordinal distinguishes repeated episodes.
public export
ClosingEpisodeOccurrence :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  Transitions initial finalState -> Type
ClosingEpisodeOccurrence name key world error value nameEq keyEq trace =
  (selected : name **
    LocatedClosedEpisode name key world error value nameEq keyEq selected trace)

public export
scannedClosingOrdinal :
  ClosingEpisodeOccurrence name key world error value nameEq keyEq trace -> Nat
scannedClosingOrdinal (selected ** episode) =
  transitionCount (traceBeforeOpening episode)

||| Independently testable O7 output.  The scanner enumerates every located
||| closing occurrence exactly once by opening ordinal and turns an empty scan
||| into the executable no-closing predicate consumed by recursion.
public export
record ClosingEpisodeScan
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkClosingEpisodeScan
  scannedClosingOccurrences : List
    (ClosingEpisodeOccurrence name key world error value nameEq keyEq trace)
  0 scannedClosingOrdinalsUnique : UniqueKeys
    (map DGamma.CP5ConfluenceDeletionChainSpike.scannedClosingOrdinal scannedClosingOccurrences)
  0 everyClosingOccurrenceScanned :
    (selected : name) ->
    (episode : LocatedClosedEpisode name key world error value nameEq keyEq
      selected trace) ->
    Elem (transitionCount (traceBeforeOpening episode))
      (map DGamma.CP5ConfluenceDeletionChainSpike.scannedClosingOrdinal scannedClosingOccurrences)
  0 emptyScanIsClosingFree : scannedClosingOccurrences = [] ->
    NoClosingEpisodes name key world error value nameEq keyEq trace

||| O7 is a separate executable producer rather than work hidden in O8/O9.
public export
closingEpisodeOccurrenceScanSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (initial, finalState : SystemState name key value world error) ->
  (trace : Transitions initial finalState) ->
  ClosingEpisodeScan name key world error value nameEq keyEq trace
closingEpisodeOccurrenceScanSpike = ?closingEpisodeOccurrenceScanSpike_rhs

||| Semantic classification retained for each withdrawn generation.  It stores
||| the exact original O-Insert occurrence and the same-parent close on that
||| occurrence's suffix.  It deliberately does *not* claim that a freely chosen
||| `RegistrationEvent` is the scanner's `registrationEventAt`: the two
||| scanner-indexed induction theorems immediately below establish the exact
||| left/right discard-list consequences.
public export
record DeletedGenerationClassification
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (generation : RegistrationGeneration name) where
  constructor MkDeletedGenerationClassification
  deletedParent : name
  deletedComponent : Component key value world error
  deletedOccurrence : LocatedGeneratedRegistration (generationName generation)
    deletedParent deletedComponent original
  0 deletedOccurrenceGeneration :
    registrationGeneration deletedOccurrence = generation
  deletedParentEpisodeCloses : ActionOccurs (LUnload deletedParent)
    (afterRegistration deletedOccurrence)

||| Exact left-scanner induction boundary.  At the located birth the accepted
||| correspondence cannot take a surviving/queued/matched branch: each such
||| branch contains `NoParentUnload`, contradicted by
||| `deletedParentEpisodeCloses`.  Hence the scanner took its own
||| `DiscardLeftDeletedRegistration` branch, whose indexed update records the
||| exact located generation in `indexedDeletedGenerations`.
public export
0 deletedClassificationForcesLeftScannerDiscardSpike :
  (nameEq : DecEq name) ->
  {leftInitial, leftFinal, rightInitial, rightFinal :
    SystemState name key value world error} ->
  {left : Transitions leftInitial leftFinal} ->
  {right : Transitions rightInitial rightFinal} ->
  (renaming : RegistrationGenerationBijection name) ->
  (leftFinalIndex, rightFinalIndex : RegistrationIndexState name) ->
  RegistrationTraceCorrespondence nameEq renaming
    0 (the (RegistrationIndexState name) DGamma.CP3.emptyRegistrationIndex)
    left leftFinalIndex
    0 (the (RegistrationIndexState name) DGamma.CP3.emptyRegistrationIndex)
    right rightFinalIndex [] [] ->
  (generation : RegistrationGeneration name) ->
  DeletedGenerationClassification name key world error value nameEq left
    generation ->
  Elem generation (indexedDeletedGenerations leftFinalIndex)
deletedClassificationForcesLeftScannerDiscardSpike =
  ?deletedClassificationForcesLeftScannerDiscardSpike_rhs

||| Symmetric right-scanner induction boundary.
public export
0 deletedClassificationForcesRightScannerDiscardSpike :
  (nameEq : DecEq name) ->
  {leftInitial, leftFinal, rightInitial, rightFinal :
    SystemState name key value world error} ->
  {left : Transitions leftInitial leftFinal} ->
  {right : Transitions rightInitial rightFinal} ->
  (renaming : RegistrationGenerationBijection name) ->
  (leftFinalIndex, rightFinalIndex : RegistrationIndexState name) ->
  RegistrationTraceCorrespondence nameEq renaming
    0 (the (RegistrationIndexState name) DGamma.CP3.emptyRegistrationIndex)
    left leftFinalIndex
    0 (the (RegistrationIndexState name) DGamma.CP3.emptyRegistrationIndex)
    right rightFinalIndex [] [] ->
  (generation : RegistrationGeneration name) ->
  DeletedGenerationClassification name key world error value nameEq right
    generation ->
  Elem generation (indexedDeletedGenerations rightFinalIndex)
deletedClassificationForcesRightScannerDiscardSpike =
  ?deletedClassificationForcesRightScannerDiscardSpike_rhs

||| Executable retained-position embedding induced by one exact
||| generation-aware subsequence. Keep advances both ordinals; delete advances
||| only the source. `Nothing` means the requested survivor ordinal is outside
||| this segment.
public export
generationSubsequenceSourceOrdinal :
  GenerationActionSubsequence nameEq deletable ordinal live original surviving ->
  Nat -> Maybe Nat
generationSubsequenceSourceOrdinal GenerationActionSubsequenceEnd target = Nothing
generationSubsequenceSourceOrdinal
  (KeepGenerationAction originalTransition originalRest survivingTransition
    survivingRest kept sameAction rest) Z = Just Z
generationSubsequenceSourceOrdinal
  (KeepGenerationAction originalTransition originalRest survivingTransition
    survivingRest kept sameAction rest) (S target) =
      map S (generationSubsequenceSourceOrdinal rest target)
generationSubsequenceSourceOrdinal
  (DeleteGenerationAction originalTransition originalRest deleted rest) target =
    map S (generationSubsequenceSourceOrdinal rest target)

public export
deletionSurvivingBeforeCount :
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered episodeStartOrdinal episodeStartLive) -> Nat
deletionSurvivingBeforeCount result = transitionCount (survivingBefore result)

public export
deletionSurvivingEpisodeCount :
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered episodeStartOrdinal episodeStartLive) -> Nat
deletionSurvivingEpisodeCount result = transitionCount (survivingEpisode result)

public export
deletionOriginalBeforeCount :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  {selected : name} ->
  {episode : LocatedClosedEpisode name key world error value nameEq keyEq selected
    original} ->
  {registered : List (RegistrationGeneration name)} ->
  {episodeStartOrdinal : Nat} ->
  {episodeStartLive : GenerationEnvironment name} ->
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered episodeStartOrdinal episodeStartLive) -> Nat
deletionOriginalBeforeCount {episode} result =
  transitionCount (traceBeforeOpening episode)

public export
deletionOriginalEpisodeCount :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  {selected : name} ->
  {episode : LocatedClosedEpisode name key world error value nameEq keyEq selected
    original} ->
  {registered : List (RegistrationGeneration name)} ->
  {episodeStartOrdinal : Nat} ->
  {episodeStartLive : GenerationEnvironment name} ->
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered episodeStartOrdinal episodeStartLive) -> Nat
deletionOriginalEpisodeCount {episode} result = transitionCount
  (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
    (closedTransitions (locatedEpisode episode)))

||| The three immutable Lemma-72 subsequences are embedded into the full source
||| and survivor traces with their exact segment offsets.
public export
data DeletionSurvivingOrdinalEmbedding :
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered episodeStartOrdinal episodeStartLive) ->
  (survivingOrdinal, originalOrdinal : Nat) -> Type where
  DeletionBeforeEmbedding :
    generationSubsequenceSourceOrdinal (beforeDeletion result)
      survivingOrdinal = Just originalOrdinal ->
    DeletionSurvivingOrdinalEmbedding result survivingOrdinal originalOrdinal
  DeletionEpisodeEmbedding :
    generationSubsequenceSourceOrdinal (episodeDeletion result)
      survivingOrdinal = Just originalOrdinal ->
    DeletionSurvivingOrdinalEmbedding result
      (deletionSurvivingBeforeCount result + survivingOrdinal)
      (deletionOriginalBeforeCount result + originalOrdinal)
  DeletionAfterEmbedding :
    generationSubsequenceSourceOrdinal (afterDeletion result)
      survivingOrdinal = Just originalOrdinal ->
    DeletionSurvivingOrdinalEmbedding result
      ((deletionSurvivingBeforeCount result +
        deletionSurvivingEpisodeCount result) + survivingOrdinal)
      ((deletionOriginalBeforeCount result +
        deletionOriginalEpisodeCount result) + originalOrdinal)

||| Operational O9 certificate.  Every occurrence in the actual survivor trace
||| maps to a source occurrence whose ordinal is justified by one of the exact
||| before/episode/after generation-subsequence embeddings.  Generated/action
||| coherence remains part of the carried generic correspondence.
public export
record DeletionOperationalOccurrenceCertificate
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (selected : name)
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq selected
    original)
  (registered : List (RegistrationGeneration name))
  (episodeStartOrdinal : Nat)
  (episodeStartLive : GenerationEnvironment name)
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered episodeStartOrdinal episodeStartLive) where
  constructor MkDeletionOperationalOccurrenceCertificate
  deletionOperationalCorrespondence : ActionRegistrationReplayCorrespondence name
    key world error value original (survivingTrace result)
  0 everySurvivingOccurrenceEmbedded :
    {action : Action name key value world error} ->
    (occurrence : LocatedActionOccurrence action (survivingTrace result)) ->
    DeletionSurvivingOrdinalEmbedding result
      (locatedActionOrdinal occurrence)
      (locatedActionOrdinal
        (replayActionOrigin deletionOperationalCorrespondence occurrence))

||| O9's first-source occurrence fold.  The immutable Lemma-72 result fixes the
||| surviving trace and all three subsequences; this globally named obligation
||| returns the complete operational certificate, not a bare coherent map.
public export
0 deletionStepOperationalOccurrenceFoldSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq trace) ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq
    trace) ->
  (result : DeletionResult name key world error value nameEq keyEq trace
    (selectedActor candidate) (selectedEpisode candidate)
    (selectedRegistrations candidate) (selectedStartOrdinal candidate)
    (selectedStartLive candidate)) ->
  DeletionOperationalOccurrenceCertificate name key world error value nameEq
    keyEq trace (selectedActor candidate) (selectedEpisode candidate)
    (selectedRegistrations candidate) (selectedStartOrdinal candidate)
    (selectedStartLive candidate) result
deletionStepOperationalOccurrenceFoldSpike =
  ?deletionStepOperationalOccurrenceFoldSpike_rhs

||| Internal enriched result of one D72 call.  The public `DeletionResult` stays
||| immutable, but the checked fold/adapter used by Path A must construct the
||| replay correspondence, exact generated-registration accounting, and every
||| premise consumed by the next iteration.
public export
record DeletionChainStep
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState)
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq trace)
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq
    trace) where
  constructor MkDeletionChainStep
  deletionResult : DeletionResult name key world error value nameEq keyEq trace
    (selectedActor candidate) (selectedEpisode candidate)
    (selectedRegistrations candidate) (selectedStartOrdinal candidate)
    (selectedStartLive candidate)
  deletionReplayCorrespondence : RelationalReplayCorrespondence name key world
    error value trace (survivingTrace deletionResult)
  deletionOccurrenceCorrespondence : ActionRegistrationReplayCorrespondence name
    key world error value trace (survivingTrace deletionResult)
  0 deletionOccurrenceCorrespondenceExact :
    deletionOccurrenceCorrespondence = deletionOperationalCorrespondence
      (deletionStepOperationalOccurrenceFoldSpike nameEq keyEq protocol trace
        premises candidate deletionResult)
  deletionSameExternalInputs : SameExternalOrchestration nameEq trace
    (survivingTrace deletionResult)
  deletionEndpoint : CanonicalEndpointRelation name key world error value nameEq
    keyEq finalState (survivingFinal deletionResult)
  0 deletionWithdrawnGenerationsExact :
    endpointWithdrawnGenerations deletionEndpoint = selectedRegistrations candidate
  deletionGenerationClassified :
    (generation : RegistrationGeneration name) ->
    Elem generation (selectedRegistrations candidate) ->
    DeletedGenerationClassification name key world error value nameEq trace
      generation
  deletionRegistrationAccounting : CanonicalRegistrationCorrespondence trace
    (survivingTrace deletionResult)
    (endpointWithdrawnGenerations deletionEndpoint)
  nextPremises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq (survivingTrace deletionResult)
  0 deletionStrictlyShorter :
    LTE (S (traceLength (survivingTrace deletionResult))) (traceLength trace)

||| Executable/constructive selection boundary for the finite trace.
public export
data ClosingStepChoice :
  (name : Type) -> (key : Type) -> (world : Type) -> (error : Type) ->
  (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq trace) -> Type where
  ClosingFree : NoClosingEpisodes name key world error value nameEq keyEq trace ->
    ClosingStepChoice name key world error value protocol nameEq keyEq trace
      premises
  HasClosingStep :
    (candidate : DeletableClosingEpisode name key world error value nameEq keyEq
      trace) ->
    DeletionChainStep name key world error value protocol nameEq keyEq trace
      premises candidate ->
    ClosingStepChoice name key world error value protocol nameEq keyEq trace
      premises

||| Independently testable O8 result.  A selected maximal/deletable candidate is
||| tied back to an ordinal produced by the exact O7 scan; the empty branch is
||| definitionally separated from the O9 deletion adapter.
public export
data MaximalClosingSelection :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq trace) ->
  (scan : ClosingEpisodeScan name key world error value nameEq keyEq trace) ->
  Type where
  NoMaximalClosingEpisode :
    scannedClosingOccurrences scan = [] ->
    MaximalClosingSelection name key world error value protocol nameEq keyEq
      trace premises scan
  SelectedMaximalClosingEpisode :
    (candidate : DeletableClosingEpisode name key world error value nameEq keyEq
      trace) ->
    Elem (transitionCount
      (traceBeforeOpening (selectedEpisode candidate)))
      (map DGamma.CP5ConfluenceDeletionChainSpike.scannedClosingOrdinal (scannedClosingOccurrences scan)) ->
    MaximalClosingSelection name key world error value protocol nameEq keyEq
      trace premises scan

||| O8 maximal candidate selection is no longer bundled with D72 enrichment.
public export
selectMaximalClosingEpisodeSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (initial, finalState : SystemState name key value world error) ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq trace) ->
  (scan : ClosingEpisodeScan name key world error value nameEq keyEq trace) ->
  MaximalClosingSelection name key world error value protocol nameEq keyEq trace
    premises scan
selectMaximalClosingEpisodeSpike = ?selectMaximalClosingEpisodeSpike_rhs

||| O9 is the separately gateable enriched Lemma-72 adapter.
public export
0 enrichDeletionChainStepSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq trace) ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq
    trace) ->
  DeletionChainStep name key world error value protocol nameEq keyEq trace
    premises candidate
enrichDeletionChainStepSpike = ?enrichDeletionChainStepSpike_rhs

public export
classifiedGeneration :
  (entry : (generation : RegistrationGeneration name **
    DeletedGenerationClassification name key world error value nameEq original
      generation)) -> RegistrationGeneration name
classifiedGeneration (generation ** classification) = generation

||| Explicit recursive deletion derivation.  Each node contains the actual
||| enriched Lemma-72 result and therefore its O9-sealed occurrence fold.  The
||| output occurrence map below is computed by composition over this family.
public export
data ClosingFreeDeletionDerivation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  Transitions initial sourceFinal -> Transitions initial targetFinal -> Type where
  ClosingFreeDeletionDone :
    (trace : Transitions initial finalState) ->
    ClosingFreeDeletionDerivation name key world error value protocol nameEq keyEq
      trace trace
  ClosingFreeDeletionStep :
    (trace : Transitions initial finalState) ->
    (premises : CanonicalizationPremises name key world error value protocol
      nameEq keyEq trace) ->
    (candidate : DeletableClosingEpisode name key world error value nameEq keyEq
      trace) ->
    (step : DeletionChainStep name key world error value protocol nameEq keyEq
      trace premises candidate) ->
    (target : Transitions initial targetFinal) ->
    (rest : ClosingFreeDeletionDerivation name key world error value protocol
      nameEq keyEq (survivingTrace (deletionResult step)) target) ->
    ClosingFreeDeletionDerivation name key world error value protocol nameEq keyEq
      trace target

public export
0 closingFreeDeletionOccurrenceFold :
  (derivation : ClosingFreeDeletionDerivation name key world error value protocol
    nameEq keyEq source target) ->
  ActionRegistrationReplayCorrespondence name key world error value source target
closingFreeDeletionOccurrenceFold (ClosingFreeDeletionDone trace) =
  identityActionRegistrationReplayCorrespondence trace
closingFreeDeletionOccurrenceFold
  (ClosingFreeDeletionStep trace premises candidate step target rest) =
    composeActionRegistrationReplayCorrespondence
      (deletionOccurrenceCorrespondence step)
      (closingFreeDeletionOccurrenceFold rest)

||| O10 recursive result before cumulative endpoint/accounting assembly.  This
||| gate exposes termination, the closing-free trace, replay, and typed deletion
||| history without hiding O11's quotient construction in the recursion hole.
public export
record ClosingFreeTraceCore
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal) where
  constructor MkClosingFreeTraceCore
  coreReducedFinal : SystemState name key value world error
  coreReducedTrace : Transitions initial coreReducedFinal
  coreReducedPremises : CanonicalizationPremises name key world error value
    protocol nameEq keyEq coreReducedTrace
  0 coreClosingFree : NoClosingEpisodes name key world error value nameEq keyEq
    coreReducedTrace
  coreSameExternalInputs : SameExternalOrchestration nameEq original
    coreReducedTrace
  coreReplayCorrespondence : RelationalReplayCorrespondence name key world error
    value original coreReducedTrace
  coreDeletionDerivation : ClosingFreeDeletionDerivation name key world error value
    protocol nameEq keyEq original coreReducedTrace
  coreDeletionGenerationHistory : List
    (generation : RegistrationGeneration name **
      DeletedGenerationClassification name key world error value nameEq original
        generation)

public export
0 coreOccurrenceCorrespondence :
  (core : ClosingFreeTraceCore name key world error value protocol nameEq keyEq
    original) ->
  ActionRegistrationReplayCorrespondence name key world error value original
    (coreReducedTrace core)
coreOccurrenceCorrespondence core =
  closingFreeDeletionOccurrenceFold (coreDeletionDerivation core)

||| Endpoint package after deleting every closing episode.  It now retains the
||| exact same-external-input witness and generated-registration correspondence
||| consumed by `CanonicalSchedule`.  History is a typed list of deleted closing
||| registrations rather than an unconstrained list-of-lists.
public export
record ClosingFreeReduction
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal) where
  constructor MkClosingFreeReduction
  reducedFinal : SystemState name key value world error
  reducedTrace : Transitions initial reducedFinal
  reducedPremises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq reducedTrace
  0 reducedClosingFree : NoClosingEpisodes name key world error value nameEq keyEq
    reducedTrace
  reductionSameExternalInputs : SameExternalOrchestration nameEq original reducedTrace
  reductionReplayCorrespondence : RelationalReplayCorrespondence name key world
    error value original reducedTrace
  reductionDeletionDerivation : ClosingFreeDeletionDerivation name key world error
    value protocol nameEq keyEq original reducedTrace
  deletionGenerationHistory : List
    (generation : RegistrationGeneration name **
      DeletedGenerationClassification name key world error value nameEq original
        generation)
  cumulativeEndpoint : CanonicalEndpointRelation name key world error value
    nameEq keyEq originalFinal reducedFinal
  0 deletionHistoryAligned : map
    DGamma.CP5ConfluenceDeletionChainSpike.classifiedGeneration
    deletionGenerationHistory =
    endpointWithdrawnGenerations cumulativeEndpoint
  cumulativeRegistrationAccounting : CanonicalRegistrationCorrespondence original
    reducedTrace (endpointWithdrawnGenerations cumulativeEndpoint)

||| The reduction's exported occurrence correspondence is a projection of its
||| recursive deletion derivation; it is not a constructor field.
public export
0 reductionOccurrenceCorrespondence :
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  ActionRegistrationReplayCorrespondence name key world error value original
    (reducedTrace reduction)
reductionOccurrenceCorrespondence reduction =
  closingFreeDeletionOccurrenceFold (reductionDeletionDerivation reduction)

||| The already checked public Lemma-72 implementation remains available, but
||| the iterative chain consumes the enriched `DeletionChainStep` above rather
||| than pretending arbitrary public results expose replay generators.
public export
0 checkedDeletionSubroutine : deletionTheorem name key value world error
checkedDeletionSubroutine = deletionTheoremProof

||| Same-external-input algebra is a first-class invariant through every
||| deletion and swap rather than an implicit final assembly assumption.
public export
0 sameExternalOrchestrationReflexiveSpike :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  SameExternalOrchestration {name = name} {key = key} {world = world}
    {error = error} {value = value} nameEq trace trace
sameExternalOrchestrationReflexiveSpike =
  ?sameExternalOrchestrationReflexiveSpike_rhs

public export
0 sameExternalOrchestrationTransitiveSpike :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {leftFirst, leftFinal, middleFirst, middleFinal, rightFirst, rightFinal :
    SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} ->
  {middle : Transitions middleFirst middleFinal} ->
  {right : Transitions rightFirst rightFinal} ->
  SameExternalOrchestration {name = name} {key = key} {world = world}
    {error = error} {value = value} nameEq left middle ->
  SameExternalOrchestration {name = name} {key = key} {world = world}
    {error = error} {value = value} nameEq middle right ->
  SameExternalOrchestration {name = name} {key = key} {world = world}
    {error = error} {value = value} nameEq left right
sameExternalOrchestrationTransitiveSpike =
  ?sameExternalOrchestrationTransitiveSpike_rhs

||| The generic RAR theorem is instantiated only after the internal deletion
||| adapter has produced correspondence capital.  This is type-coherent for an
||| arbitrary result and avoids the rejected universal public-result claim.
public export
0 traceIndependentAfterDeletionReplaySpike :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} -> {selected : name} ->
  {episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected original} ->
  {registered : List (RegistrationGeneration name)} ->
  {episodeStartOrdinal : Nat} ->
  {episodeStartLive : GenerationEnvironment name} ->
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered episodeStartOrdinal episodeStartLive) ->
  RelationalReplayCorrespondence name key world error value original
    (survivingTrace result) ->
  TraceIndependent name key world error value keyEq original ->
  TraceIndependent name key world error value keyEq (survivingTrace result)
traceIndependentAfterDeletionReplaySpike =
  ?traceIndependentAfterDeletionReplaySpike_rhs

||| Complete O7→O8→O9 wrapper.  Each hard producer above can be elaborated and
||| re-estimated independently; this function contains no proof hole.
public export
0 chooseClosingStepSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq trace) ->
  ClosingStepChoice name key world error value protocol nameEq keyEq trace
    premises
chooseClosingStepSpike {initial} {finalState} nameEq keyEq protocol trace
  premises =
  let scan = closingEpisodeOccurrenceScanSpike nameEq keyEq initial finalState
        trace in
    case selectMaximalClosingEpisodeSpike nameEq keyEq protocol initial finalState
      trace premises scan of
      NoMaximalClosingEpisode empty =>
        ClosingFree (emptyScanIsClosingFree scan empty)
      SelectedMaximalClosingEpisode candidate selected =>
        HasClosingStep candidate
          (enrichDeletionChainStepSpike nameEq keyEq protocol trace premises
            candidate)

||| O10: well-founded recursion only.  Cumulative endpoint and registration
||| accounting are intentionally deferred to the independently gateable O11.
public export
0 deleteClosingEpisodesCoreSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  CanonicalizationPremises name key world error value protocol nameEq keyEq trace ->
  ClosingFreeTraceCore name key world error value protocol nameEq keyEq trace
deleteClosingEpisodesCoreSpike = ?deleteClosingEpisodesCoreSpike_rhs

||| O11: assemble cumulative endpoint and generated-registration accounting from
||| the exact O10 trace/history value.
public export
0 assembleClosingFreeAccountingSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (core : ClosingFreeTraceCore name key world error value protocol nameEq keyEq
    trace) ->
  ClosingFreeReduction name key world error value protocol nameEq keyEq trace
assembleClosingFreeAccountingSpike = ?assembleClosingFreeAccountingSpike_rhs

||| Complete O10→O11 wrapper retained for existing consumers.
public export
0 deleteAllClosingEpisodesSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  CanonicalizationPremises name key world error value protocol nameEq keyEq trace ->
  ClosingFreeReduction name key world error value protocol nameEq keyEq trace
deleteAllClosingEpisodesSpike nameEq keyEq protocol trace premises =
  assembleClosingFreeAccountingSpike nameEq keyEq protocol trace
    (deleteClosingEpisodesCoreSpike nameEq keyEq protocol trace premises)

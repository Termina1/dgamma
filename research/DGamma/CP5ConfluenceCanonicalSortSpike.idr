module DGamma.CP5ConfluenceCanonicalSortSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4Support
import DGamma.CP4SupportSolution
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

||| An open episode before sorting: its installed interval may contain arbitrary
||| foreign interleavings all the way to the final Active endpoint.
public export
record LocatedInterleavedOpenEpisode
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState) where
  constructor MkLocatedInterleavedOpenEpisode
  openPreStart : SystemState name key value world error
  openStart : SystemState name key value world error
  openPrefix : Transitions initial openPreStart
  openBegin : BeginStep nameEq keyEq selected openPreStart openStart
  openInside : Transitions openStart finalState
  openInstalled : InstalledTrace name key world error value nameEq keyEq selected
    openInside
  openNoEarlierLifecycle : NoLifecycleBy selected openPrefix
  0 openActiveAtFinal : supportedActiveAt @{nameEq} selected finalState = True
  0 openDecomposition : appendTransitions openPrefix
    (MoreTransitions (beginTransition openBegin) openInside) = global

||| Structural consequence after every closing episode is deleted.  Uniqueness
||| is occurrence-indexed by the begin ordinal (`transitionCount openPrefix`),
||| avoiding the old prose-only claim of “exactly one”.
public export
record ClosingFreeTraceShape
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkClosingFreeTraceShape
  supportedOpenEpisode : (selected : name) ->
    isSupported @{nameEq} @{keyEq} selected finalState = True ->
    LocatedInterleavedOpenEpisode name key world error value nameEq keyEq
      selected trace
  0 supportedOpenEpisodeUnique : (selected : name) ->
    (supported : isSupported @{nameEq} @{keyEq} selected finalState = True) ->
    (other : LocatedInterleavedOpenEpisode name key world error value nameEq keyEq
      selected trace) ->
    transitionCount (openPrefix (supportedOpenEpisode selected supported)) =
      transitionCount (openPrefix other)
  unsupportedTakesNoLifecycle : (selected : name) ->
    isSupported @{nameEq} @{keyEq} selected finalState = False ->
    NoLifecycleBy selected trace

||| Finite topological capital for the exact Equation-62 support relation.
public export
record SupportOrderingCapital
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (state : SystemState name key value world error) where
  constructor MkSupportOrderingCapital
  orderedSupportNames : List name
  orderedSupportLinearization : LinearizesSupport name key world error value
    nameEq keyEq state orderedSupportNames

||| Minimal original-endpoint/reduced-endpoint bridge.  It deliberately does
||| not transport arbitrary `SupportPath`s: accepted endpoint withdrawal permits
||| an unsupported retired child to be present originally and absent after
||| reduction, and such a child can still terminate a raw parent path.  Consumers
||| receive only support-set equality and the two complete schedule facts they
||| actually need.
public export
record CanonicalSupportTransport
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (originalFinal, reducedFinal : SystemState name key value world error)
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal reducedFinal) where
  constructor MkCanonicalSupportTransport
  0 supportTruthPreserved : (n : name) ->
    isSupported @{nameEq} @{keyEq} n originalFinal =
      isSupported @{nameEq} @{keyEq} n reducedFinal
  linearizationToOriginal : (order : List name) ->
    LinearizesSupport name key world error value nameEq keyEq reducedFinal order ->
    LinearizesSupport name key world error value nameEq keyEq originalFinal order
  inputPlacementToOriginal : (order : List name) ->
    {initial, canonicalFinal : SystemState name key value world error} ->
    (canonical : Transitions initial canonicalFinal) ->
    CanonicalInputPlacement name key world error value nameEq keyEq reducedFinal
      order canonical ->
    CanonicalInputPlacement name key world error value nameEq keyEq originalFinal
      order canonical

||| Sorting result with every recursive invariant, replay generator/stage
||| correspondence, external-input witness, and registration-accounting field
||| required by one-trace schedule assembly.
public export
record SortedClosingFreeTrace
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    originalFinal) where
  constructor MkSortedClosingFreeTrace
  sortedFinal : SystemState name key value world error
  sortedTrace : Transitions initial sortedFinal
  sortingReplayCorrespondence : RelationalReplayCorrespondence name key world
    error value original sortedTrace
  sortingAdjacentDerivation : FiniteAdjacentSwapDerivation name key world error
    value protocol nameEq keyEq original sortedTrace
  sortedPremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sortedTrace
  sortedSameInputs : SameExternalOrchestration nameEq original sortedTrace
  sortedBlock : (n : name) -> Elem n (orderedSupportNames ordering) ->
    LocatedOpenEpisodeBlock name key world error value nameEq keyEq n sortedTrace
  sortedBlocksFollowOrder : (earlier, later : name) ->
    (earlierIn : Elem earlier (orderedSupportNames ordering)) ->
    (laterIn : Elem later (orderedSupportNames ordering)) ->
    BeforeIn earlier later (orderedSupportNames ordering) ->
    BlockBefore name key world error value nameEq keyEq sortedTrace earlier later
      (sortedBlock earlier earlierIn) (sortedBlock later laterIn)
  0 sortedBlockRangesDisjoint : (earlier, later : name) ->
    (earlierIn : Elem earlier (orderedSupportNames ordering)) ->
    (laterIn : Elem later (orderedSupportNames ordering)) ->
    BeforeIn earlier later (orderedSupportNames ordering) ->
    (earlierPosition, laterPosition : Nat) ->
    LTE (S earlierPosition)
      (S (transitionCount (blockBody (sortedBlock earlier earlierIn)))) ->
    LTE (S laterPosition)
      (S (transitionCount (blockBody (sortedBlock later laterIn)))) ->
    Not (transitionCount (traceBeforeBlock (sortedBlock earlier earlierIn)) +
      earlierPosition =
      transitionCount (traceBeforeBlock (sortedBlock later laterIn)) +
      laterPosition)
  sortedLifecycleCoverage : LifecycleActorsCovered
    (orderedSupportNames ordering) sortedTrace
  sortedInputPlacement : CanonicalInputPlacement name key world error value
    nameEq keyEq originalFinal (orderedSupportNames ordering) sortedTrace
  sortedEndpoint : CanonicalEndpointRelation name key world error value nameEq
    keyEq originalFinal sortedFinal
  0 sortedWithdrawsNoNames : endpointWithdrawnNames sortedEndpoint = []
  0 sortedWithdrawsNoGenerations :
    endpointWithdrawnGenerations sortedEndpoint = []
  sortedRegistrationTree : CanonicalRegistrationCorrespondence original
    sortedTrace (endpointWithdrawnGenerations sortedEndpoint)

||| Sorting occurrence provenance is computed from the explicit finite sequence
||| of O6-sealed adjacent-swap results.  There is no occurrence-map constructor
||| argument to clone independently of those operational nodes.
public export
0 sortingOccurrenceCorrespondence :
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq keyEq
    original ordering) ->
  ActionRegistrationReplayCorrespondence name key world error value original
    (sortedTrace sorted)
sortingOccurrenceCorrespondence sorted =
  finiteDerivationOccurrenceCorrespondence (sortingAdjacentDerivation sorted)

||| Derive the unique closing-free shape from the exact recursive bundle.
public export
0 closingFreeTraceShapeSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  NoClosingEpisodes name key world error value nameEq keyEq trace ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq trace ->
  ClosingFreeTraceShape name key world error value nameEq keyEq trace
closingFreeTraceShapeSpike = ?closingFreeTraceShapeSpike_rhs

||| Construct the finite linearization from re-established Lemma-68 capital.
public export
0 supportOrderingSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq trace ->
  SupportOrderingCapital name key world error value nameEq keyEq finalState
supportOrderingSpike = ?supportOrderingSpike_rhs

||| Bubble actor blocks by repeated `AdjacentSwapResult`s.  The output itself is
||| the sorting-specific recursive transport package, rather than only final
||| schedule-shaped data.
public export
0 sortClosingFreeTraceSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq trace ->
  ClosingFreeTraceShape name key world error value nameEq keyEq trace ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    finalState) ->
  SortedClosingFreeTrace name key world error value protocol nameEq keyEq trace
    ordering
sortClosingFreeTraceSpike = ?sortClosingFreeTraceSpike_rhs

||| Prove all support/parent/input-placement transport from the cumulative
||| endpoint relation and exact generated-registration accounting.
public export
0 canonicalSupportTransportSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal, reducedFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (reduced : Transitions initial reducedFinal) ->
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal reducedFinal) ->
  CanonicalRegistrationCorrespondence original reduced
    (endpointWithdrawnGenerations endpoint) ->
  CanonicalSupportTransport name key world error value nameEq keyEq originalFinal
    reducedFinal endpoint
canonicalSupportTransportSpike = ?canonicalSupportTransportSpike_rhs

||| Research-only authenticity companion for the immutable CP3 registration
||| tree.  It states exact occurrence equality, not merely equal birth ordinals:
||| the tree map must be the origin chosen by the deletion/sorting action replay.
||| Its indices make the proof unusable after replacing either the tree or the
||| occurrence correspondence.
public export
record AuthenticatedCanonicalRegistrationMap
  (name, key, world, error : Type) (value : key -> Type)
  {initial, originalFinal, canonicalFinal :
    SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (canonical : Transitions initial canonicalFinal)
  (withdrawn : List (RegistrationGeneration name))
  (tree : CanonicalRegistrationCorrespondence original canonical withdrawn)
  (occurrences : ActionRegistrationReplayCorrespondence name key world error value
    original canonical) where
  constructor MkAuthenticatedCanonicalRegistrationMap
  0 canonicalOriginIsReplayOrigin :
    {child, parent : name} ->
    {component : Component key value world error} ->
    (occurrence : LocatedGeneratedRegistration child parent component canonical) ->
    canonicalToOriginal tree occurrence =
      replayGeneratedRegistrationOrigin occurrences occurrence

||| The exact occurrence correspondence constructed by deletion followed by
||| sorting.  There is no caller-selected intermediate map at this boundary.
public export
0 deletionSortingOccurrenceCorrespondence :
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  {ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)} ->
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) ->
  ActionRegistrationReplayCorrespondence name key world error value original
    (sortedTrace sorted)
deletionSortingOccurrenceCorrespondence reduction sorted =
  composeActionRegistrationReplayCorrespondence
    (reductionOccurrenceCorrespondence reduction)
    (sortingOccurrenceCorrespondence sorted)

||| Ordinary CP3 registration-accounting laws stated directly over the exact
||| deletion/sorting occurrence fold.  They contain no strong-authentication
||| equality and no `OneTraceOrchestrationAccounting` value.
public export
record CanonicalReplayAccountingLaws
  (name, key, world, error : Type) (value : key -> Type)
  {initial, originalFinal, canonicalFinal :
    SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (canonical : Transitions initial canonicalFinal)
  (withdrawn : List (RegistrationGeneration name))
  (occurrences : ActionRegistrationReplayCorrespondence name key world error value
    original canonical) where
  constructor MkCanonicalReplayAccountingLaws
  replayOriginalRegistrationAccounted :
    {child, parent : name} ->
    {component : Component key value world error} ->
    (occurrence : LocatedGeneratedRegistration child parent component original) ->
    Either (Elem (registrationGeneration occurrence) withdrawn)
      (canonicalOccurrence : LocatedGeneratedRegistration child parent component
        canonical **
       registrationGeneration
         (replayGeneratedRegistrationOrigin occurrences canonicalOccurrence) =
       registrationGeneration occurrence)
  0 replayCanonicalOccurrenceInjective :
    {child, parent : name} ->
    {component : Component key value world error} ->
    (leftOccurrence, rightOccurrence : LocatedGeneratedRegistration child parent
      component canonical) ->
    registrationGeneration (replayGeneratedRegistrationOrigin occurrences
      leftOccurrence) =
    registrationGeneration (replayGeneratedRegistrationOrigin occurrences
      rightOccurrence) ->
    registrationGeneration leftOccurrence = registrationGeneration rightOccurrence
  0 replayWithdrawnRegistrationRemoved :
    (generation : RegistrationGeneration name) -> Elem generation withdrawn ->
    (parent : name ** component : Component key value world error **
     occurrence : LocatedGeneratedRegistration (generationName generation)
       parent component original **
     (registrationGeneration occurrence = generation,
      (canonicalParent : name) ->
      (canonicalComponent : Component key value world error) ->
      (canonicalOccurrence : LocatedGeneratedRegistration
        (generationName generation) canonicalParent canonicalComponent canonical) ->
      registrationGeneration (replayGeneratedRegistrationOrigin occurrences
        canonicalOccurrence) = generation -> Void))

||| Construct the immutable CP3 tree by definition from the occurrence fold.
||| Consequently the strong authentication proof below is `Refl`.
public export
0 canonicalRegistrationTreeFromReplay :
  (occurrences : ActionRegistrationReplayCorrespondence name key world error value
    original canonical) ->
  (laws : CanonicalReplayAccountingLaws name key world error value original
    canonical withdrawn occurrences) ->
  CanonicalRegistrationCorrespondence original canonical withdrawn
canonicalRegistrationTreeFromReplay occurrences laws =
  MkCanonicalRegistrationCorrespondence
    (replayGeneratedRegistrationOrigin occurrences)
    (replayOriginalRegistrationAccounted laws)
    (replayCanonicalOccurrenceInjective laws)
    (replayWithdrawnRegistrationRemoved laws)

public export
0 replayConstructedTreeAuthentication :
  (occurrences : ActionRegistrationReplayCorrespondence name key world error value
    original canonical) ->
  (laws : CanonicalReplayAccountingLaws name key world error value original
    canonical withdrawn occurrences) ->
  AuthenticatedCanonicalRegistrationMap name key world error value original
    canonical withdrawn (canonicalRegistrationTreeFromReplay occurrences laws)
    occurrences
replayConstructedTreeAuthentication occurrences laws =
  MkAuthenticatedCanonicalRegistrationMap (\occurrence => Refl)

||| Full external/generated orchestration accounting through deletion followed
||| by sorting.  The registration map is authenticated against the exact
||| composed occurrence replay produced by those same indexed fold outputs.
public export
record OneTraceOrchestrationAccounting
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original)
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction))
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) where
  constructor MkOneTraceOrchestrationAccounting
  accountedEndpoint : CanonicalEndpointRelation name key world error value
    nameEq keyEq originalFinal (sortedFinal sorted)
  0 accountedWithdrawnExact : endpointWithdrawnGenerations accountedEndpoint =
    endpointWithdrawnGenerations (cumulativeEndpoint reduction)
  accountedExternalInputs : SameExternalOrchestration nameEq original
    (sortedTrace sorted)
  accountedGeneratedRegistrations : CanonicalRegistrationCorrespondence original
    (sortedTrace sorted) (endpointWithdrawnGenerations accountedEndpoint)
  accountedRegistrationAuthentication : AuthenticatedCanonicalRegistrationMap
    name key world error value original (sortedTrace sorted)
    (endpointWithdrawnGenerations accountedEndpoint)
    accountedGeneratedRegistrations
    (deletionSortingOccurrenceCorrespondence reduction sorted)

||| Checked strong-authentication producer from the raw fold and ordinary CP3
||| accounting laws.  This function does not assume the result accounting value.
public export
0 assembleOneTraceAccountingFromReplay :
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)) ->
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) ->
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal (sortedFinal sorted)) ->
  endpointWithdrawnGenerations endpoint =
    endpointWithdrawnGenerations (cumulativeEndpoint reduction) ->
  SameExternalOrchestration nameEq original (sortedTrace sorted) ->
  (laws : CanonicalReplayAccountingLaws name key world error value original
    (sortedTrace sorted) (endpointWithdrawnGenerations endpoint)
    (deletionSortingOccurrenceCorrespondence reduction sorted)) ->
  OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
    original reduction ordering sorted
assembleOneTraceAccountingFromReplay reduction ordering sorted endpoint exact
  external laws =
    MkOneTraceOrchestrationAccounting endpoint exact external
      (canonicalRegistrationTreeFromReplay
        (deletionSortingOccurrenceCorrespondence reduction sorted) laws)
      (replayConstructedTreeAuthentication
        (deletionSortingOccurrenceCorrespondence reduction sorted) laws)

||| Abstract O16 assembler only.  It assumes the hard deletion reduction, sorting
||| derivation, two located births, singleton withdrawal, and every ordinary CP3
||| replay-accounting law.  It calibrates dependent packaging and Refl
||| authentication but is explicitly not a concrete nontrivial producer fixture.
public export
record AbstractTwoBirthOneWithdrawalAssembly
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original)
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction))
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) where
  constructor MkAbstractTwoBirthOneWithdrawalAssembly
  fixtureEndpoint : CanonicalEndpointRelation name key world error value nameEq
    keyEq originalFinal (sortedFinal sorted)
  fixtureWithdrawnGeneration : RegistrationGeneration name
  0 fixtureOneWithdrawal : endpointWithdrawnGenerations fixtureEndpoint =
    [fixtureWithdrawnGeneration]
  0 fixtureWithdrawalMatchesReduction :
    endpointWithdrawnGenerations fixtureEndpoint =
      endpointWithdrawnGenerations (cumulativeEndpoint reduction)
  fixtureExternalInputs : SameExternalOrchestration nameEq original
    (sortedTrace sorted)
  fixtureFirstChild : name
  fixtureFirstParent : name
  fixtureFirstComponent : Component key value world error
  fixtureFirstBirth : LocatedGeneratedRegistration fixtureFirstChild
    fixtureFirstParent fixtureFirstComponent (sortedTrace sorted)
  fixtureSecondChild : name
  fixtureSecondParent : name
  fixtureSecondComponent : Component key value world error
  fixtureSecondBirth : LocatedGeneratedRegistration fixtureSecondChild
    fixtureSecondParent fixtureSecondComponent (sortedTrace sorted)
  0 fixtureOriginalBirthsDistinct : Not
    (registrationGeneration (replayGeneratedRegistrationOrigin
      (deletionSortingOccurrenceCorrespondence reduction sorted)
      fixtureFirstBirth) =
     registrationGeneration (replayGeneratedRegistrationOrigin
      (deletionSortingOccurrenceCorrespondence reduction sorted)
      fixtureSecondBirth))
  fixtureReplayAccountingLaws : CanonicalReplayAccountingLaws name key world
    error value original (sortedTrace sorted)
    (endpointWithdrawnGenerations fixtureEndpoint)
    (deletionSortingOccurrenceCorrespondence reduction sorted)

||| Construct the abstract assembly record from its complete raw telescope.
||| Neither the assembly nor final accounting is accepted as input, but the hard
||| deletion/sorting and CP3 laws remain premises.
public export
0 assembleAbstractTwoBirthOneWithdrawalAssembly :
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  {reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original} ->
  {ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)} ->
  {sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering} ->
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal (sortedFinal sorted)) ->
  (withdrawn : RegistrationGeneration name) ->
  endpointWithdrawnGenerations endpoint = [withdrawn] ->
  endpointWithdrawnGenerations endpoint =
    endpointWithdrawnGenerations (cumulativeEndpoint reduction) ->
  (external : SameExternalOrchestration nameEq original (sortedTrace sorted)) ->
  (firstChild, firstParent : name) ->
  (firstComponent : Component key value world error) ->
  (firstBirth : LocatedGeneratedRegistration firstChild firstParent firstComponent
    (sortedTrace sorted)) ->
  (secondChild, secondParent : name) ->
  (secondComponent : Component key value world error) ->
  (secondBirth : LocatedGeneratedRegistration secondChild secondParent
    secondComponent (sortedTrace sorted)) ->
  Not (registrationGeneration (replayGeneratedRegistrationOrigin
    (deletionSortingOccurrenceCorrespondence reduction sorted) firstBirth) =
    registrationGeneration (replayGeneratedRegistrationOrigin
      (deletionSortingOccurrenceCorrespondence reduction sorted) secondBirth)) ->
  (laws : CanonicalReplayAccountingLaws name key world error value original
    (sortedTrace sorted) (endpointWithdrawnGenerations endpoint)
    (deletionSortingOccurrenceCorrespondence reduction sorted)) ->
  AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol nameEq keyEq
    original reduction ordering sorted
assembleAbstractTwoBirthOneWithdrawalAssembly endpoint withdrawn one exact external
  firstChild firstParent firstComponent firstBirth secondChild secondParent
  secondComponent secondBirth distinct laws =
    MkAbstractTwoBirthOneWithdrawalAssembly endpoint withdrawn one exact external
      firstChild firstParent firstComponent firstBirth secondChild secondParent
      secondComponent secondBirth distinct laws

public export
0 abstractTwoBirthOneWithdrawalAccounting :
  (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
    nameEq keyEq original reduction ordering sorted) ->
  OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
    original reduction ordering sorted
abstractTwoBirthOneWithdrawalAccounting {reduction} {ordering} {sorted} fixture =
  assembleOneTraceAccountingFromReplay reduction ordering sorted
    (fixtureEndpoint fixture) (fixtureWithdrawalMatchesReduction fixture)
    (fixtureExternalInputs fixture) (fixtureReplayAccountingLaws fixture)

public export
0 deletionSortingOrchestrationAccountingSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)) ->
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) ->
  OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
    original reduction ordering sorted
deletionSortingOrchestrationAccountingSpike =
  ?deletionSortingOrchestrationAccountingSpike_rhs

||| Erased producer schedule used to seal the runtime schedule stored by the
||| bridge-facing capital.  All proof fields come from the exact indexed chain.
public export
0 producerCanonicalSchedule :
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq original) ->
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)) ->
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) ->
  (supportTransport : CanonicalSupportTransport name key world error value
    nameEq keyEq originalFinal (reducedFinal reduction)
      (cumulativeEndpoint reduction)) ->
  (accounting : OneTraceOrchestrationAccounting name key world error value
    protocol nameEq keyEq original reduction ordering sorted) ->
  CanonicalSchedule name key world error value protocol nameEq keyEq original
producerCanonicalSchedule premises reduction ordering sorted supportTransport
  accounting =
    MkCanonicalSchedule
      (sortedFinal sorted)
      (sortedTrace sorted)
      (accountedExternalInputs accounting)
      (replayDiscipline (chainReplayCapital premises))
      (replayDiscipline (sortedPremises sorted))
      (orderedSupportNames ordering)
      (linearizationToOriginal supportTransport (orderedSupportNames ordering)
        (orderedSupportLinearization ordering))
      (sortedBlock sorted)
      (sortedBlocksFollowOrder sorted)
      (sortedLifecycleCoverage sorted)
      (inputPlacementToOriginal supportTransport (orderedSupportNames ordering)
        (sortedTrace sorted) (sortedInputPlacement sorted))
      (accountedEndpoint accounting)
      (accountedGeneratedRegistrations accounting)

||| Bridge-facing capital preserves the exact producer chain.  No canonical
||| schedule, occurrence correspondence, or authentication pair is freely stored:
||| every trusted consumer projection below is definitionally reconstructed from
||| these deletion, ordering, sorting, and accounting values.
public export
record IndependentCanonicalSchedule
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal) where
  constructor MkIndependentCanonicalSchedule
  capitalPremises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq original
  capitalReduction : ClosingFreeReduction name key world error value protocol
    nameEq keyEq original
  capitalOrdering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal capitalReduction)
  capitalSorted : SortedClosingFreeTrace name key world error value protocol
    nameEq keyEq (reducedTrace capitalReduction) capitalOrdering
  capitalSupportTransport : CanonicalSupportTransport name key world error value
    nameEq keyEq originalFinal (reducedFinal capitalReduction)
      (cumulativeEndpoint capitalReduction)
  capitalAccounting : OneTraceOrchestrationAccounting name key world error value
    protocol nameEq keyEq original capitalReduction capitalOrdering capitalSorted
  capitalCanonicalSchedule : CanonicalSchedule name key world error value protocol
    nameEq keyEq original
  0 capitalCanonicalScheduleExact : capitalCanonicalSchedule =
    producerCanonicalSchedule capitalPremises capitalReduction capitalOrdering
      capitalSorted capitalSupportTransport capitalAccounting
  capitalWithdrawnClassified :
    (generation : RegistrationGeneration name) ->
    Elem generation (endpointWithdrawnGenerations
      (accountedEndpoint capitalAccounting)) ->
    DeletedGenerationClassification name key world error value nameEq original
      generation

||| The public CP3 schedule is a projection of the exact producer chain, not a
||| constructor argument.  A coherent caller-selected `(tree,map)` pair has no
||| field through which it can enter this value.
public export
canonicalSchedule :
  IndependentCanonicalSchedule name key world error value protocol nameEq keyEq
    original ->
  CanonicalSchedule name key world error value protocol nameEq keyEq original
canonicalSchedule capital = capitalCanonicalSchedule capital

public export
0 originalTraceIndependent :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  TraceIndependent name key world error value keyEq original
originalTraceIndependent capital =
  replayIndependent (chainReplayCapital (capitalPremises capital))

public export
0 canonicalReplayCorrespondence :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  RelationalReplayCorrespondence name key world error value original
    (canonicalTrace (canonicalSchedule capital))
canonicalReplayCorrespondence
  (MkIndependentCanonicalSchedule premises reduction ordering sorted
    supportTransport accounting _ Refl classified) =
      composeRelationalReplayCorrespondence
        (reductionReplayCorrespondence reduction)
        (sortingReplayCorrespondence sorted)

public export
0 canonicalOccurrenceCorrespondence :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  ActionRegistrationReplayCorrespondence name key world error value original
    (canonicalTrace (canonicalSchedule capital))
canonicalOccurrenceCorrespondence
  (MkIndependentCanonicalSchedule premises reduction ordering sorted
    supportTransport accounting _ Refl classified) =
      deletionSortingOccurrenceCorrespondence reduction sorted

public export
0 canonicalRegistrationAuthentication :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  AuthenticatedCanonicalRegistrationMap name key world error value original
    (canonicalTrace (canonicalSchedule capital))
    (endpointWithdrawnGenerations (canonicalEndpoint (canonicalSchedule capital)))
    (canonicalRegistrationTree (canonicalSchedule capital))
    (canonicalOccurrenceCorrespondence capital)
canonicalRegistrationAuthentication
  (MkIndependentCanonicalSchedule premises reduction ordering sorted
    supportTransport accounting _ Refl classified) =
      accountedRegistrationAuthentication accounting

public export
0 canonicalReplayPremises :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq
    (canonicalTrace (canonicalSchedule capital))
canonicalReplayPremises
  (MkIndependentCanonicalSchedule premises reduction ordering sorted
    supportTransport accounting _ Refl classified) = sortedPremises sorted

public export
0 canonicalTraceIndependent :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  TraceIndependent name key world error value keyEq
    (canonicalTrace (canonicalSchedule capital))
canonicalTraceIndependent
  (MkIndependentCanonicalSchedule premises reduction ordering sorted
    supportTransport accounting _ Refl classified) =
      replayIndependent (sortedPremises sorted)

public export
0 canonicalWithdrawnClassified :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  (generation : RegistrationGeneration name) ->
  Elem generation (endpointWithdrawnGenerations
    (canonicalEndpoint (canonicalSchedule capital))) ->
  DeletedGenerationClassification name key world error value nameEq original
    generation
canonicalWithdrawnClassified
  (MkIndependentCanonicalSchedule premises reduction ordering sorted
    supportTransport accounting _ Refl classified) = classified

||| Complete simultaneous-package constructor.  It merely seals the exact
||| producer values; all consumer-facing maps and schedules are derived above.
public export
0 assembleIndependentCanonicalSchedule :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq original) ->
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)) ->
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) ->
  (supportTransport : CanonicalSupportTransport name key world error value
    nameEq keyEq originalFinal (reducedFinal reduction)
      (cumulativeEndpoint reduction)) ->
  (accounting : OneTraceOrchestrationAccounting name key world error value
    protocol nameEq keyEq original reduction ordering sorted) ->
  ((generation : RegistrationGeneration name) ->
    Elem generation (endpointWithdrawnGenerations
      (accountedEndpoint accounting)) ->
    DeletedGenerationClassification name key world error value nameEq original
      generation) ->
  IndependentCanonicalSchedule name key world error value protocol nameEq keyEq
    original
assembleIndependentCanonicalSchedule nameEq keyEq protocol original premises
  reduction ordering sorted supportTransport accounting classified =
    MkIndependentCanonicalSchedule premises reduction ordering sorted
      supportTransport accounting
      (producerCanonicalSchedule premises reduction ordering sorted
        supportTransport accounting)
      Refl classified

||| The hard producer derives the typed cumulative classification from the
||| deletion history and returns the simultaneous package above.  Consumers no
||| longer receive an opaque schedule detached from replay indices.
public export
0 independentCanonicalScheduleSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  CanonicalizationPremises name key world error value protocol nameEq keyEq original ->
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)) ->
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) ->
  CanonicalSupportTransport name key world error value nameEq keyEq originalFinal
    (reducedFinal reduction) (cumulativeEndpoint reduction) ->
  OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
    original reduction ordering sorted ->
  IndependentCanonicalSchedule name key world error value protocol nameEq keyEq
    original
independentCanonicalScheduleSpike = ?independentCanonicalScheduleSpike_rhs

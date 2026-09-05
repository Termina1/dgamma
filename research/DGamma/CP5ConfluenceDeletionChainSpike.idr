module DGamma.CP5ConfluenceDeletionChainSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionTheorem
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionBoundaryLifecycleCore
import DGamma.CP4DeletionBoundaryRetained
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanEmpty
import DGamma.CP4DeletionPlanEffects
import DGamma.CP4DeletionPremiseSplit
import DGamma.CP4DeletionFilterSuccess
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionGenerationBounds
import DGamma.CP4DeletionGenerationStamped
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionIndependenceRestriction
import DGamma.CP4DeletionNoEpisodeReplay
import DGamma.CP4DeletionCommittedProviderPersistence
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionEmptyTableInvariant
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceCurrent
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceResolved
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceSelected
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceSnapshot
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import DGamma.CP4DeletionRetirementPersistence
import DGamma.CP4DeletionRetainedAction
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorClassify
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorTrace
import DGamma.CP4DeletionSelectedForeignLifecycleProviderFrame
import DGamma.CP4DeletionSelectedForeignLifecycleDispatch
import DGamma.CP4DeletionSelectedForeignLifecycleReplayCore
import DGamma.CP4DeletionSelectedForeignLifecycleStep
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP4DeletionSelectedForeignOrchestrationStep
import DGamma.CP4DeletionSelectedForeignTables
import DGamma.CP4DeletionSelectedForeignAdvanceAgreement
import DGamma.CP4DeletionSelectedForeignControlCore
import DGamma.CP4DeletionSelectedOwn
import DGamma.CP4DeletionSelectedOwnDispatch
import DGamma.CP4DeletionSelectedRetire
import DGamma.CP4DeletionSelectedStart
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedCloseBoundary
import DGamma.CP4DeletionSelectedDeletedDispatch
import DGamma.CP4DeletionSelectedDeletedOrchestration
import DGamma.CP4DeletionSelectedEpisodeFold
import DGamma.CP4DeletionSelectedEpisodeFoldCore
import DGamma.CP4DeletionSelectedEffectCore
import DGamma.CP4DeletionSelectedEpisodeReplay
import DGamma.CP4DeletionPostCloseFold
import DGamma.CP4DeletionPostCloseLifecycle
import DGamma.CP4DeletionSelectedForeignLifecycleReplay
import DGamma.Ordering
import Control.WellFounded
import DGamma.CP4DeletionWithdrawalCurrent
import DGamma.CP4DeletionWithdrawalJoin
import DGamma.CP4RecoveryTrace
import DGamma.CP4RecoveryModelTrace
import DGamma.CP4RecoverySelectedStep
import DGamma.CP4ParentSafety
import DGamma.CP4Support
import DGamma.CP4SupportQuiescence
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
||| A consumer closing episode is relevant to one selected registration
||| generation only when its exact opening occurs inside the selected installed
||| interval.  The start scan authenticates the selected generation; the two
||| ordinal equations tie both openings to the same global trace without
||| comparing erased transition proofs.
public export
record GenerationScopedClosingStart
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState)
  (selected : name) (selectedStartOrdinal : Nat)
  (selectedStartLive : GenerationEnvironment name)
  (selectedEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global)
  (consumer : name)
  (consumerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    consumer global) where
  constructor MkGenerationScopedClosingStart
  0 scopedSelectedOrdinal : transitionCount
    (traceBeforeOpening selectedEpisode) = selectedStartOrdinal
  scopedConsumerOpening : LocatedActionOccurrence (LBegin consumer)
    (closedInside (locatedEpisode selectedEpisode))
  0 scopedConsumerOrdinal : transitionCount
    (traceBeforeOpening consumerEpisode) =
    selectedStartOrdinal + S (locatedActionOrdinal scopedConsumerOpening)

||| Generation-start/activation-interval replacement for the false global raw
||| name predicate.  A later birth or reactivation outside the selected installed
||| interval cannot be used to reject this candidate.
public export
NoDependentClosingEpisodeForGeneration :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, finalState : SystemState name key value world error} ->
  {global : Transitions initial finalState} ->
  (selected : name) -> (selectedStartOrdinal : Nat) ->
  (selectedStartLive : GenerationEnvironment name) ->
  (selectedEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) -> Type
NoDependentClosingEpisodeForGeneration {name} {key} {world} {error} {value}
  {nameEq} {keyEq} {global} selected selectedStartOrdinal selectedStartLive
  selectedEpisode =
    (consumer : name) ->
    (consumerEpisode : LocatedClosedEpisode name key world error value nameEq
      keyEq consumer global) ->
    GenerationScopedClosingStart name key world error value nameEq keyEq global
      selected selectedStartOrdinal selectedStartLive selectedEpisode consumer
      consumerEpisode ->
    PrecedenceEdge nameEq selected consumer
      (closedStartState (locatedEpisode consumerEpisode)) -> Void

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
  0 selectedNoDependentClose : NoDependentClosingEpisodeForGeneration
    {nameEq = nameEq} {keyEq = keyEq} {global = trace} selectedActor
    selectedStartOrdinal selectedStartLive selectedEpisode
  0 selectedChildrenHaveNoEpisode : NoRegisteredEpisode nameEq
    selectedRegistrations 0 [] trace

||| Fully instantiated first-action projection used only at erased equality
||| boundaries.  Keeping every type and state argument explicit prevents an
||| equal-position `Refl` elimination from leaving anonymous dependent indices.
0 firstTraceActionPreInterval :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (first, finalState : SystemState name key value world error) ->
  Transitions first finalState -> Maybe (Action name key value world error)
firstTraceActionPreInterval name key world error value first finalState trace =
  case trace of
    NoTransitions => Nothing
    MoreTransitions transition rest => Just (transitionAction transition)

||| Producer-owned common-head view for two nonempty exact traces.  Its sole
||| constructor binds the erased middle state and transition before exposing
||| the tail equation.
data SharedExactPreIntervalHead :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (first, finalState : SystemState name key value world error) ->
  (selected, foreign : Transitions first finalState) -> Type where
  SharedExactPreIntervalHeadWitness :
    (name, key, world, error : Type) -> (value : key -> Type) ->
    (first, middle, finalState : SystemState name key value world error) ->
    (head : Transition first middle) ->
    (selectedTail, foreignTail : Transitions middle finalState) ->
    (0 tailAlignment : (selectedTail = foreignTail)) ->
    SharedExactPreIntervalHead name key world error value first finalState
      (MoreTransitions head selectedTail) (MoreTransitions head foreignTail)

||| P2 cure: transport a reflexive head view instead of asking a nonlinear
||| `Refl` clause to identify two independently elaborated dependent heads.
0 sharedExactPreIntervalHead :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (first, selectedMiddle, foreignMiddle, finalState :
    SystemState name key value world error) ->
  (selectedHead : Transition first selectedMiddle) ->
  (selectedTail : Transitions selectedMiddle finalState) ->
  (foreignHead : Transition first foreignMiddle) ->
  (foreignTail : Transitions foreignMiddle finalState) ->
  (0 alignment :
    (MoreTransitions selectedHead selectedTail =
      MoreTransitions foreignHead foreignTail)) ->
  SharedExactPreIntervalHead name key world error value first finalState
    (MoreTransitions selectedHead selectedTail)
    (MoreTransitions foreignHead foreignTail)
sharedExactPreIntervalHead name key world error value first selectedMiddle
  foreignMiddle finalState selectedHead selectedTail foreignHead foreignTail
  alignment =
    replace
      {p = \candidate => SharedExactPreIntervalHead name key world error value
        first finalState (MoreTransitions selectedHead selectedTail) candidate}
      alignment
      (SharedExactPreIntervalHeadWitness name key world error value first
        selectedMiddle finalState selectedHead selectedTail selectedTail Refl)

||| Checked P2 consumer: after one head-view elimination, `cong` mentions only
||| the constructor-owned common head.
0 liftSharedExactPreIntervalHead :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (first, finalState : SystemState name key value world error) ->
  (selected, foreign : Transitions first finalState) ->
  SharedExactPreIntervalHead name key world error value first finalState selected
    foreign ->
  (selected = foreign)
liftSharedExactPreIntervalHead name key world error value first finalState
  selected foreign headView =
    case headView of
      SharedExactPreIntervalHeadWitness viewName viewKey viewWorld viewError
        viewValue viewFirst viewMiddle viewFinal viewHead viewSelectedTail
        viewForeignTail tailAlignment =>
          cong (MoreTransitions viewHead) tailAlignment

||| Exact positional classification of two distinct distinguished transitions.
||| The result retains a state-indexed trace between the openings and the exact
||| suffix equation; no Nat-only ordinal comparison is used.
data ExactPreIntervalPrefixClassification :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (first, selectedBefore, selectedAfter, foreignBefore, foreignAfter,
    finalState : SystemState name key value world error) ->
  (selectedPrefix : Transitions first selectedBefore) ->
  (selectedOpening : Transition selectedBefore selectedAfter) ->
  (selectedInside : Transitions selectedAfter finalState) ->
  (foreignPrefix : Transitions first foreignBefore) ->
  (foreignOpening : Transition foreignBefore foreignAfter) ->
  (foreignSuffix : Transitions foreignAfter finalState) -> Type where
  ExactForeignOpeningInsideSelectedInterval :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, selectedBefore, selectedAfter, foreignBefore, foreignAfter,
      finalState : SystemState name key value world error} ->
    {selectedPrefix : Transitions first selectedBefore} ->
    {selectedOpening : Transition selectedBefore selectedAfter} ->
    {selectedInside : Transitions selectedAfter finalState} ->
    {foreignPrefix : Transitions first foreignBefore} ->
    {foreignOpening : Transition foreignBefore foreignAfter} ->
    {foreignSuffix : Transitions foreignAfter finalState} ->
    (0 selectedToForeign : Transitions selectedAfter foreignBefore) ->
    (0 selectedInsideExact :
      (selectedInside = appendTransitions selectedToForeign
        (MoreTransitions foreignOpening foreignSuffix))) ->
    (0 foreignPrefixCountExact :
      transitionCount foreignPrefix =
        transitionCount selectedPrefix + S (transitionCount selectedToForeign)) ->
    ExactPreIntervalPrefixClassification name key world error value first
      selectedBefore selectedAfter foreignBefore foreignAfter finalState
      selectedPrefix selectedOpening selectedInside foreignPrefix foreignOpening
      foreignSuffix
  ExactForeignOpeningBeforeSelectedInterval :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, selectedBefore, selectedAfter, foreignBefore, foreignAfter,
      finalState : SystemState name key value world error} ->
    {selectedPrefix : Transitions first selectedBefore} ->
    {selectedOpening : Transition selectedBefore selectedAfter} ->
    {selectedInside : Transitions selectedAfter finalState} ->
    {foreignPrefix : Transitions first foreignBefore} ->
    {foreignOpening : Transition foreignBefore foreignAfter} ->
    {foreignSuffix : Transitions foreignAfter finalState} ->
    (0 foreignToSelected : Transitions foreignAfter selectedBefore) ->
    (0 foreignSuffixExact :
      (foreignSuffix = appendTransitions foreignToSelected
        (MoreTransitions selectedOpening selectedInside))) ->
    ExactPreIntervalPrefixClassification name key world error value first
      selectedBefore selectedAfter foreignBefore foreignAfter finalState
      selectedPrefix selectedOpening selectedInside foreignPrefix foreignOpening
      foreignSuffix

||| A1 cure: the opening source and full projection telescope are explicit.
||| `justInjective` exposes action equality, and `cong actionOwner` contradicts
||| the caller's distinct-owner premise without dependent `Refl` inference.
0 equalPositionDistinctOpeningsImpossible :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (openingSource, selectedAfter, foreignAfter, finalState :
    SystemState name key value world error) ->
  (selectedOpening : Transition openingSource selectedAfter) ->
  (selectedInside : Transitions selectedAfter finalState) ->
  (foreignOpening : Transition openingSource foreignAfter) ->
  (foreignSuffix : Transitions foreignAfter finalState) ->
  (0 ownerDistinct : Not
    (actionOwner (transitionAction selectedOpening) =
      actionOwner (transitionAction foreignOpening))) ->
  (0 alignment :
    (MoreTransitions selectedOpening selectedInside =
      MoreTransitions foreignOpening foreignSuffix)) -> Void
equalPositionDistinctOpeningsImpossible name key world error value openingSource
  selectedAfter foreignAfter finalState selectedOpening selectedInside
  foreignOpening foreignSuffix ownerDistinct alignment =
    ownerDistinct
      (cong actionOwner
        (justInjective
          (cong
            (firstTraceActionPreInterval name key world error value openingSource
              finalState)
            alignment)))

||| Selected opening is the common head; one P2-view elimination yields the
||| exact selected-inside suffix demanded by the classification constructor.
0 selectedOpeningHeadClassification :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (first, selectedAfter, foreignMiddle, foreignBefore, foreignAfter,
    finalState : SystemState name key value world error) ->
  (selectedOpening : Transition first selectedAfter) ->
  (selectedInside : Transitions selectedAfter finalState) ->
  (foreignHead : Transition first foreignMiddle) ->
  (foreignRest : Transitions foreignMiddle foreignBefore) ->
  (foreignOpening : Transition foreignBefore foreignAfter) ->
  (foreignSuffix : Transitions foreignAfter finalState) ->
  SharedExactPreIntervalHead name key world error value first finalState
    (MoreTransitions selectedOpening selectedInside)
    (MoreTransitions foreignHead
      (appendTransitions foreignRest
        (MoreTransitions foreignOpening foreignSuffix))) ->
  ExactPreIntervalPrefixClassification name key world error value first first
    selectedAfter foreignBefore foreignAfter finalState NoTransitions
    selectedOpening selectedInside (MoreTransitions foreignHead foreignRest)
    foreignOpening foreignSuffix
selectedOpeningHeadClassification name key world error value first selectedAfter
  foreignMiddle foreignBefore foreignAfter finalState selectedOpening
  selectedInside foreignHead foreignRest foreignOpening foreignSuffix headView =
    case headView of
      SharedExactPreIntervalHeadWitness viewName viewKey viewWorld viewError
        viewValue viewFirst viewMiddle viewFinal viewHead _ _ tailAlignment =>
          ExactForeignOpeningInsideSelectedInterval foreignRest tailAlignment Refl

||| Foreign opening is the common head; the mirror P2-view elimination yields
||| the exact foreign suffix through the selected opening.
0 foreignOpeningHeadClassification :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (first, selectedMiddle, selectedBefore, selectedAfter, foreignAfter,
    finalState : SystemState name key value world error) ->
  (selectedHead : Transition first selectedMiddle) ->
  (selectedRest : Transitions selectedMiddle selectedBefore) ->
  (selectedOpening : Transition selectedBefore selectedAfter) ->
  (selectedInside : Transitions selectedAfter finalState) ->
  (foreignOpening : Transition first foreignAfter) ->
  (foreignSuffix : Transitions foreignAfter finalState) ->
  SharedExactPreIntervalHead name key world error value first finalState
    (MoreTransitions selectedHead
      (appendTransitions selectedRest
        (MoreTransitions selectedOpening selectedInside)))
    (MoreTransitions foreignOpening foreignSuffix) ->
  ExactPreIntervalPrefixClassification name key world error value first
    selectedBefore selectedAfter first foreignAfter finalState
    (MoreTransitions selectedHead selectedRest) selectedOpening selectedInside
    NoTransitions foreignOpening foreignSuffix
foreignOpeningHeadClassification name key world error value first selectedMiddle
  selectedBefore selectedAfter foreignAfter finalState selectedHead selectedRest
  selectedOpening selectedInside foreignOpening foreignSuffix headView =
    case headView of
      SharedExactPreIntervalHeadWitness viewName viewKey viewWorld viewError
        viewValue viewFirst viewMiddle viewFinal viewHead _ _ tailAlignment =>
          ExactForeignOpeningBeforeSelectedInterval selectedRest
            (sym tailAlignment)

||| Re-index a recursive tail verdict under the two caller-owned prefix heads.
||| The interval equation itself is unchanged, so this helper performs only the
||| single classification elimination and never reconstructs a head equality.
0 prependExactPreIntervalClassification :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (first, middle, selectedBefore, selectedAfter, foreignBefore, foreignAfter,
    finalState : SystemState name key value world error) ->
  (selectedHead : Transition first middle) ->
  (selectedRest : Transitions middle selectedBefore) ->
  (selectedOpening : Transition selectedBefore selectedAfter) ->
  (selectedInside : Transitions selectedAfter finalState) ->
  (foreignHead : Transition first middle) ->
  (foreignRest : Transitions middle foreignBefore) ->
  (foreignOpening : Transition foreignBefore foreignAfter) ->
  (foreignSuffix : Transitions foreignAfter finalState) ->
  ExactPreIntervalPrefixClassification name key world error value middle
    selectedBefore selectedAfter foreignBefore foreignAfter finalState
    selectedRest selectedOpening selectedInside foreignRest foreignOpening
    foreignSuffix ->
  ExactPreIntervalPrefixClassification name key world error value first
    selectedBefore selectedAfter foreignBefore foreignAfter finalState
    (MoreTransitions selectedHead selectedRest) selectedOpening selectedInside
    (MoreTransitions foreignHead foreignRest) foreignOpening foreignSuffix
prependExactPreIntervalClassification name key world error value first middle
  selectedBefore selectedAfter foreignBefore foreignAfter finalState selectedHead
  selectedRest selectedOpening selectedInside foreignHead foreignRest
  foreignOpening foreignSuffix verdict =
    case verdict of
      ExactForeignOpeningInsideSelectedInterval selectedToForeign
        selectedInsideExact foreignPrefixCountExact =>
          ExactForeignOpeningInsideSelectedInterval selectedToForeign
            selectedInsideExact (cong S foreignPrefixCountExact)
      ExactForeignOpeningBeforeSelectedInterval foreignToSelected
        foreignSuffixExact =>
          ExactForeignOpeningBeforeSelectedInterval foreignToSelected
            foreignSuffixExact

mutual
  ||| Covering exact-prefix classifier.  Its sole elimination exposes only the
  ||| selected prefix; a top-level helper performs the foreign-prefix split.
  0 exactPreIntervalPrefixClassifier :
    (name, key, world, error : Type) -> (value : key -> Type) ->
    (first, selectedBefore, selectedAfter, foreignBefore, foreignAfter,
      finalState : SystemState name key value world error) ->
    (selectedPrefix : Transitions first selectedBefore) ->
    (selectedOpening : Transition selectedBefore selectedAfter) ->
    (selectedInside : Transitions selectedAfter finalState) ->
    (foreignPrefix : Transitions first foreignBefore) ->
    (foreignOpening : Transition foreignBefore foreignAfter) ->
    (foreignSuffix : Transitions foreignAfter finalState) ->
    (0 ownerDistinct : Not
      (actionOwner (transitionAction selectedOpening) =
        actionOwner (transitionAction foreignOpening))) ->
    (0 alignment :
      (appendTransitions selectedPrefix
        (MoreTransitions selectedOpening selectedInside) =
       appendTransitions foreignPrefix
        (MoreTransitions foreignOpening foreignSuffix))) ->
    ExactPreIntervalPrefixClassification name key world error value first
      selectedBefore selectedAfter foreignBefore foreignAfter finalState
      selectedPrefix selectedOpening selectedInside foreignPrefix foreignOpening
      foreignSuffix
  exactPreIntervalPrefixClassifier name key world error value first
    selectedBefore selectedAfter foreignBefore foreignAfter finalState
    selectedPrefix selectedOpening selectedInside foreignPrefix foreignOpening
    foreignSuffix ownerDistinct alignment =
      case selectedPrefix of
        NoTransitions =>
          exactPreIntervalSelectedEmpty name key world error value first
            selectedAfter foreignBefore foreignAfter finalState selectedOpening
            selectedInside foreignPrefix foreignOpening foreignSuffix
            ownerDistinct alignment
        MoreTransitions {middle = selectedMiddle} selectedHead selectedRest =>
          exactPreIntervalSelectedNonempty name key world error value first
            selectedMiddle selectedBefore selectedAfter foreignBefore
            foreignAfter finalState selectedHead selectedRest selectedOpening
            selectedInside foreignPrefix foreignOpening foreignSuffix
            ownerDistinct alignment

  ||| Selected-prefix empty case.  This helper performs only the foreign-prefix
  ||| elimination; the equal and strict cases are delegated to proven cures.
  0 exactPreIntervalSelectedEmpty :
    (name, key, world, error : Type) -> (value : key -> Type) ->
    (first, selectedAfter, foreignBefore, foreignAfter, finalState :
      SystemState name key value world error) ->
    (selectedOpening : Transition first selectedAfter) ->
    (selectedInside : Transitions selectedAfter finalState) ->
    (foreignPrefix : Transitions first foreignBefore) ->
    (foreignOpening : Transition foreignBefore foreignAfter) ->
    (foreignSuffix : Transitions foreignAfter finalState) ->
    (0 ownerDistinct : Not
      (actionOwner (transitionAction selectedOpening) =
        actionOwner (transitionAction foreignOpening))) ->
    (0 alignment :
      (MoreTransitions selectedOpening selectedInside =
       appendTransitions foreignPrefix
        (MoreTransitions foreignOpening foreignSuffix))) ->
    ExactPreIntervalPrefixClassification name key world error value first first
      selectedAfter foreignBefore foreignAfter finalState NoTransitions
      selectedOpening selectedInside foreignPrefix foreignOpening foreignSuffix
  exactPreIntervalSelectedEmpty name key world error value first selectedAfter
    foreignBefore foreignAfter finalState selectedOpening selectedInside
    foreignPrefix foreignOpening foreignSuffix ownerDistinct alignment =
      case foreignPrefix of
        NoTransitions =>
          void (equalPositionDistinctOpeningsImpossible name key world error
            value first selectedAfter foreignAfter finalState selectedOpening
            selectedInside foreignOpening foreignSuffix ownerDistinct alignment)
        MoreTransitions {middle = foreignMiddle} foreignHead foreignRest =>
          selectedOpeningHeadClassification name key world error value first
            selectedAfter foreignMiddle foreignBefore foreignAfter finalState
            selectedOpening selectedInside foreignHead foreignRest foreignOpening
            foreignSuffix
            (sharedExactPreIntervalHead name key world error value first
              selectedAfter foreignMiddle finalState selectedOpening
              selectedInside foreignHead
              (appendTransitions foreignRest
                (MoreTransitions foreignOpening foreignSuffix)) alignment)

  ||| Selected-prefix nonempty case.  Its sole elimination exposes the foreign
  ||| prefix and delegates the recursive case to the common-head helper.
  0 exactPreIntervalSelectedNonempty :
    (name, key, world, error : Type) -> (value : key -> Type) ->
    (first, selectedMiddle, selectedBefore, selectedAfter, foreignBefore,
      foreignAfter, finalState : SystemState name key value world error) ->
    (selectedHead : Transition first selectedMiddle) ->
    (selectedRest : Transitions selectedMiddle selectedBefore) ->
    (selectedOpening : Transition selectedBefore selectedAfter) ->
    (selectedInside : Transitions selectedAfter finalState) ->
    (foreignPrefix : Transitions first foreignBefore) ->
    (foreignOpening : Transition foreignBefore foreignAfter) ->
    (foreignSuffix : Transitions foreignAfter finalState) ->
    (0 ownerDistinct : Not
      (actionOwner (transitionAction selectedOpening) =
        actionOwner (transitionAction foreignOpening))) ->
    (0 alignment :
      (MoreTransitions selectedHead
        (appendTransitions selectedRest
          (MoreTransitions selectedOpening selectedInside)) =
       appendTransitions foreignPrefix
        (MoreTransitions foreignOpening foreignSuffix))) ->
    ExactPreIntervalPrefixClassification name key world error value first
      selectedBefore selectedAfter foreignBefore foreignAfter finalState
      (MoreTransitions selectedHead selectedRest) selectedOpening selectedInside
      foreignPrefix foreignOpening foreignSuffix
  exactPreIntervalSelectedNonempty name key world error value first
    selectedMiddle selectedBefore selectedAfter foreignBefore foreignAfter
    finalState selectedHead selectedRest selectedOpening selectedInside
    foreignPrefix foreignOpening foreignSuffix ownerDistinct alignment =
      case foreignPrefix of
        NoTransitions =>
          foreignOpeningHeadClassification name key world error value first
            selectedMiddle selectedBefore selectedAfter foreignAfter finalState
            selectedHead selectedRest selectedOpening selectedInside
            foreignOpening foreignSuffix
            (sharedExactPreIntervalHead name key world error value first
              selectedMiddle foreignAfter finalState selectedHead
              (appendTransitions selectedRest
                (MoreTransitions selectedOpening selectedInside))
              foreignOpening foreignSuffix alignment)
        MoreTransitions {middle = foreignMiddle} foreignHead foreignRest =>
          bothNonemptyPreIntervalClassification name key world error value first
            selectedMiddle foreignMiddle selectedBefore selectedAfter
            foreignBefore foreignAfter finalState selectedHead selectedRest
            selectedOpening selectedInside foreignHead foreignRest foreignOpening
            foreignSuffix ownerDistinct
            (sharedExactPreIntervalHead name key world error value first
              selectedMiddle foreignMiddle finalState selectedHead
              (appendTransitions selectedRest
                (MoreTransitions selectedOpening selectedInside)) foreignHead
              (appendTransitions foreignRest
                (MoreTransitions foreignOpening foreignSuffix)) alignment)

  ||| Consume the P2 common-head view, thread P3's explicit final state through
  ||| the structurally smaller recursive call, then re-index its verdict.
  0 bothNonemptyPreIntervalClassification :
    (name, key, world, error : Type) -> (value : key -> Type) ->
    (first, selectedMiddle, foreignMiddle, selectedBefore, selectedAfter,
      foreignBefore, foreignAfter, finalState :
        SystemState name key value world error) ->
    (selectedHead : Transition first selectedMiddle) ->
    (selectedRest : Transitions selectedMiddle selectedBefore) ->
    (selectedOpening : Transition selectedBefore selectedAfter) ->
    (selectedInside : Transitions selectedAfter finalState) ->
    (foreignHead : Transition first foreignMiddle) ->
    (foreignRest : Transitions foreignMiddle foreignBefore) ->
    (foreignOpening : Transition foreignBefore foreignAfter) ->
    (foreignSuffix : Transitions foreignAfter finalState) ->
    (0 ownerDistinct : Not
      (actionOwner (transitionAction selectedOpening) =
        actionOwner (transitionAction foreignOpening))) ->
    SharedExactPreIntervalHead name key world error value first finalState
      (MoreTransitions selectedHead
        (appendTransitions selectedRest
          (MoreTransitions selectedOpening selectedInside)))
      (MoreTransitions foreignHead
        (appendTransitions foreignRest
          (MoreTransitions foreignOpening foreignSuffix))) ->
    ExactPreIntervalPrefixClassification name key world error value first
      selectedBefore selectedAfter foreignBefore foreignAfter finalState
      (MoreTransitions selectedHead selectedRest) selectedOpening selectedInside
      (MoreTransitions foreignHead foreignRest) foreignOpening foreignSuffix
  bothNonemptyPreIntervalClassification name key world error value first
    selectedMiddle foreignMiddle selectedBefore selectedAfter foreignBefore
    foreignAfter finalState selectedHead selectedRest selectedOpening
    selectedInside foreignHead foreignRest foreignOpening foreignSuffix
    ownerDistinct headView =
      case headView of
        SharedExactPreIntervalHeadWitness viewName viewKey viewWorld viewError
          viewValue viewFirst viewMiddle viewFinal viewHead _ _ tailAlignment =>
            prependExactPreIntervalClassification name key world error value
              first viewMiddle selectedBefore selectedAfter foreignBefore
              foreignAfter finalState viewHead selectedRest
              selectedOpening selectedInside viewHead foreignRest foreignOpening
              foreignSuffix
              (exactPreIntervalPrefixClassifier name key world error value
                viewMiddle selectedBefore selectedAfter foreignBefore
                foreignAfter finalState selectedRest selectedOpening
                selectedInside foreignRest foreignOpening foreignSuffix
                ownerDistinct tailAlignment)

||| Lifecycle-specialized erased verdict used by route B.  Both constructors
||| retain the foreign installation evidence and the exact intervening trace.
public export
data ErasedFirstLifecyclePreIntervalView :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) ->
  (first, selectedBefore, selectedAfter, foreignBefore, foreignAfter,
    finalState : SystemState name key value world error) ->
  (selectedPrefix : Transitions first selectedBefore) ->
  (selectedOpening : BeginStep nameEq keyEq selected selectedBefore
    selectedAfter) ->
  (selectedInside : Transitions selectedAfter finalState) ->
  (foreignPrefix : Transitions first foreignBefore) ->
  (foreignOpening : BeginStep nameEq keyEq actor foreignBefore foreignAfter) ->
  (foreignSuffix : Transitions foreignAfter finalState) -> Type where
  ForeignOpeningInsideSelectedInterval :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {selected, actor : name} ->
    {first, selectedBefore, selectedAfter, foreignBefore, foreignAfter,
      finalState : SystemState name key value world error} ->
    {selectedPrefix : Transitions first selectedBefore} ->
    {selectedOpening : BeginStep nameEq keyEq selected selectedBefore
      selectedAfter} ->
    {selectedInside : Transitions selectedAfter finalState} ->
    {foreignPrefix : Transitions first foreignBefore} ->
    {foreignOpening : BeginStep nameEq keyEq actor foreignBefore foreignAfter} ->
    {foreignSuffix : Transitions foreignAfter finalState} ->
    (0 selectedToForeign : Transitions selectedAfter foreignBefore) ->
    (0 selectedInsideExact :
      (selectedInside = appendTransitions selectedToForeign
        (MoreTransitions (beginTransition foreignOpening) foreignSuffix))) ->
    (0 foreignPrefixCountExact :
      transitionCount foreignPrefix =
        transitionCount selectedPrefix + S (transitionCount selectedToForeign)) ->
    (0 foreignInstalled : InstalledTrace name key world error value nameEq keyEq
      actor foreignSuffix) ->
    ErasedFirstLifecyclePreIntervalView name key world error value nameEq keyEq
      selected actor first selectedBefore selectedAfter foreignBefore
      foreignAfter finalState selectedPrefix selectedOpening selectedInside
      foreignPrefix foreignOpening foreignSuffix
  ForeignOpeningBeforeSelectedInterval :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {selected, actor : name} ->
    {first, selectedBefore, selectedAfter, foreignBefore, foreignAfter,
      finalState : SystemState name key value world error} ->
    {selectedPrefix : Transitions first selectedBefore} ->
    {selectedOpening : BeginStep nameEq keyEq selected selectedBefore
      selectedAfter} ->
    {selectedInside : Transitions selectedAfter finalState} ->
    {foreignPrefix : Transitions first foreignBefore} ->
    {foreignOpening : BeginStep nameEq keyEq actor foreignBefore foreignAfter} ->
    {foreignSuffix : Transitions foreignAfter finalState} ->
    (0 foreignToSelected : Transitions foreignAfter selectedBefore) ->
    (0 foreignSuffixExact :
      (foreignSuffix = appendTransitions foreignToSelected
        (MoreTransitions (beginTransition selectedOpening) selectedInside))) ->
    (0 foreignInstalled : InstalledTrace name key world error value nameEq keyEq
      actor foreignSuffix) ->
    ErasedFirstLifecyclePreIntervalView name key world error value nameEq keyEq
      selected actor first selectedBefore selectedAfter foreignBefore
      foreignAfter finalState selectedPrefix selectedOpening selectedInside
      foreignPrefix foreignOpening foreignSuffix

||| One generic-verdict elimination packages the foreign installed evidence.
0 exactPreIntervalToLifecycleView :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) ->
  (first, selectedBefore, selectedAfter, foreignBefore, foreignAfter,
    finalState : SystemState name key value world error) ->
  (selectedPrefix : Transitions first selectedBefore) ->
  (selectedOpening : BeginStep nameEq keyEq selected selectedBefore
    selectedAfter) ->
  (selectedInside : Transitions selectedAfter finalState) ->
  (foreignPrefix : Transitions first foreignBefore) ->
  (foreignOpening : BeginStep nameEq keyEq actor foreignBefore foreignAfter) ->
  (foreignSuffix : Transitions foreignAfter finalState) ->
  (0 foreignInstalled : InstalledTrace name key world error value nameEq keyEq
    actor foreignSuffix) ->
  ExactPreIntervalPrefixClassification name key world error value first
    selectedBefore selectedAfter foreignBefore foreignAfter finalState
    selectedPrefix (beginTransition selectedOpening) selectedInside
    foreignPrefix (beginTransition foreignOpening) foreignSuffix ->
  ErasedFirstLifecyclePreIntervalView name key world error value nameEq keyEq
    selected actor first selectedBefore selectedAfter foreignBefore foreignAfter
    finalState selectedPrefix selectedOpening selectedInside foreignPrefix
    foreignOpening foreignSuffix
exactPreIntervalToLifecycleView name key world error value nameEq keyEq selected
  actor first selectedBefore selectedAfter foreignBefore foreignAfter finalState
  selectedPrefix selectedOpening selectedInside foreignPrefix foreignOpening
  foreignSuffix foreignInstalled classification =
    case classification of
      ExactForeignOpeningInsideSelectedInterval selectedToForeign
        selectedInsideExact foreignPrefixCountExact =>
          ForeignOpeningInsideSelectedInterval selectedToForeign
            selectedInsideExact foreignPrefixCountExact foreignInstalled
      ExactForeignOpeningBeforeSelectedInterval foreignToSelected
        foreignSuffixExact =>
          ForeignOpeningBeforeSelectedInterval foreignToSelected
            foreignSuffixExact foreignInstalled

0 distinctBeginOpeningOwners :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) ->
  (selectedBefore, selectedAfter, foreignBefore, foreignAfter :
    SystemState name key value world error) ->
  (selectedOpening : BeginStep nameEq keyEq selected selectedBefore
    selectedAfter) ->
  (foreignOpening : BeginStep nameEq keyEq actor foreignBefore foreignAfter) ->
  (0 actorDistinct : Not (actor = selected)) ->
  Not
    (actionOwner (transitionAction (beginTransition selectedOpening)) =
      actionOwner (transitionAction (beginTransition foreignOpening)))
distinctBeginOpeningOwners name key world error value nameEq keyEq selected actor
  selectedBefore selectedAfter foreignBefore foreignAfter selectedOpening
  foreignOpening actorDistinct sameOwner = actorDistinct (sym sameOwner)

||| Route-B pre-interval classifier: exact prefixes, exact suffixes, and the
||| foreign installed segment are preserved in either positional branch.
public export
0 erasedFirstLifecyclePreIntervalCovering :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) ->
  (0 actorDistinct : Not (actor = selected)) ->
  (first, selectedBefore, selectedAfter, foreignBefore, foreignAfter,
    finalState : SystemState name key value world error) ->
  (selectedPrefix : Transitions first selectedBefore) ->
  (selectedOpening : BeginStep nameEq keyEq selected selectedBefore
    selectedAfter) ->
  (selectedInside : Transitions selectedAfter finalState) ->
  (foreignPrefix : Transitions first foreignBefore) ->
  (foreignOpening : BeginStep nameEq keyEq actor foreignBefore foreignAfter) ->
  (foreignSuffix : Transitions foreignAfter finalState) ->
  (0 foreignInstalled : InstalledTrace name key world error value nameEq keyEq
    actor foreignSuffix) ->
  (0 alignment :
    (appendTransitions selectedPrefix
      (MoreTransitions (beginTransition selectedOpening) selectedInside) =
     appendTransitions foreignPrefix
      (MoreTransitions (beginTransition foreignOpening) foreignSuffix))) ->
  ErasedFirstLifecyclePreIntervalView name key world error value nameEq keyEq
    selected actor first selectedBefore selectedAfter foreignBefore foreignAfter
    finalState selectedPrefix selectedOpening selectedInside foreignPrefix
    foreignOpening foreignSuffix
erasedFirstLifecyclePreIntervalCovering name key world error value nameEq keyEq
  selected actor actorDistinct first selectedBefore selectedAfter foreignBefore
  foreignAfter finalState selectedPrefix selectedOpening selectedInside
  foreignPrefix foreignOpening foreignSuffix foreignInstalled alignment =
    exactPreIntervalToLifecycleView name key world error value nameEq keyEq
      selected actor first selectedBefore selectedAfter foreignBefore
      foreignAfter finalState selectedPrefix selectedOpening selectedInside
      foreignPrefix foreignOpening foreignSuffix foreignInstalled
      (exactPreIntervalPrefixClassifier name key world error value first
        selectedBefore selectedAfter foreignBefore foreignAfter finalState
        selectedPrefix (beginTransition selectedOpening) selectedInside
        foreignPrefix (beginTransition foreignOpening) foreignSuffix
        (distinctBeginOpeningOwners name key world error value nameEq keyEq
          selected actor selectedBefore selectedAfter foreignBefore foreignAfter
          selectedOpening foreignOpening actorDistinct)
        alignment)

||| Canonized erased view for one O7 occurrence.  The actor and located episode
||| remain exactly quantified as before, but neither can escape into runtime code
||| after eliminating the view.
public export
data ClosingEpisodeOccurrence :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  Transitions initial finalState -> Type where
  ErasedClosingEpisodeOccurrence :
    (0 selected : name) ->
    (0 episode : LocatedClosedEpisode name key world error value nameEq keyEq
      selected trace) ->
    ClosingEpisodeOccurrence name key world error value nameEq keyEq trace

public export
0 scannedClosingOrdinal :
  ClosingEpisodeOccurrence name key world error value nameEq keyEq trace -> Nat
scannedClosingOrdinal (ErasedClosingEpisodeOccurrence selected episode) =
  transitionCount (traceBeforeOpening episode)

0 prependLocatedClosingEpisode :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  LocatedClosedEpisode name key world error value nameEq keyEq selected rest ->
  LocatedClosedEpisode name key world error value nameEq keyEq selected
    (MoreTransitions head rest)
prependLocatedClosingEpisode head rest
  (MkLocatedClosedEpisode preStart afterState beforeOpening episode afterClosing
    decomposition) =
      MkLocatedClosedEpisode preStart afterState
        (MoreTransitions head beforeOpening) episode afterClosing
        (cong (MoreTransitions head) decomposition)

0 prependClosingOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  ClosingEpisodeOccurrence name key world error value nameEq keyEq rest ->
  ClosingEpisodeOccurrence name key world error value nameEq keyEq
    (MoreTransitions head rest)
prependClosingOccurrence head rest
  (ErasedClosingEpisodeOccurrence selected episode) =
    ErasedClosingEpisodeOccurrence selected
      (prependLocatedClosingEpisode head rest episode)

0 prependClosingOrdinal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (occurrence : ClosingEpisodeOccurrence name key world error value nameEq keyEq
    rest) ->
  scannedClosingOrdinal (prependClosingOccurrence head rest occurrence) =
    S (scannedClosingOrdinal occurrence)
prependClosingOrdinal head rest
  (ErasedClosingEpisodeOccurrence selected
    (MkLocatedClosedEpisode preStart afterState beforeOpening episode afterClosing
      decomposition)) = Refl

0 prependClosingOccurrences :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  List (ClosingEpisodeOccurrence name key world error value nameEq keyEq rest) ->
  List (ClosingEpisodeOccurrence name key world error value nameEq keyEq
    (MoreTransitions head rest))
prependClosingOccurrences head rest [] = []
prependClosingOccurrences head rest (occurrence :: later) =
  prependClosingOccurrence head rest occurrence ::
    prependClosingOccurrences head rest later

0 prependClosingOrdinals :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (occurrences : List
    (ClosingEpisodeOccurrence name key world error value nameEq keyEq rest)) ->
  map (\occurrence => scannedClosingOrdinal occurrence)
      (prependClosingOccurrences head rest occurrences) =
    map S (map (\occurrence => scannedClosingOrdinal occurrence) occurrences)
prependClosingOrdinals head rest [] = Refl
prependClosingOrdinals head rest (occurrence :: later) =
  rewrite prependClosingOrdinal head rest occurrence in
  rewrite prependClosingOrdinals head rest later in Refl

0 successorElem :
  {value : Nat} -> {values : List Nat} ->
  Elem value values -> Elem (S value) (map S values)
successorElem Here = Here
successorElem (There later) = There (successorElem later)

0 reflectSuccessorElem :
  (value : Nat) -> (values : List Nat) ->
  Elem (S value) (map S values) -> Elem value values
reflectSuccessorElem value [] present impossible
reflectSuccessorElem value (_ :: later) Here = Here
reflectSuccessorElem value (current :: later) (There present) =
  There (reflectSuccessorElem value later present)

0 zeroAbsentFromSuccessors :
  (values : List Nat) -> Not (Elem Z (map S values))
zeroAbsentFromSuccessors [] present impossible
zeroAbsentFromSuccessors (current :: later) Here impossible
zeroAbsentFromSuccessors (current :: later) (There present) =
  zeroAbsentFromSuccessors later present

0 uniqueSuccessors :
  {values : List Nat} -> UniqueKeys values -> UniqueKeys (map S values)
uniqueSuccessors UniqueNil = UniqueNil
uniqueSuccessors {values = current :: later} (UniqueCons fresh uniqueLater) =
  UniqueCons
    (\present => fresh (reflectSuccessorElem current later present))
    (uniqueSuccessors uniqueLater)

data LocatedClosingHeadView :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) -> name -> Nat -> Type where
  ClosingOpensHere :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
    {first, middle, finalState : SystemState name key value world error} ->
    {head : Transition first middle} ->
    {rest : Transitions middle finalState} ->
    (0 opening : BeginStep nameEq keyEq selected first middle) ->
    (0 firstClosing : FirstClosingResult name key world error value nameEq keyEq
      selected rest) ->
    (0 headOpening : head = beginTransition opening) ->
    LocatedClosingHeadView name key world error value nameEq keyEq head rest
      selected Z
  ClosingOpensLater :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
    {first, middle, finalState : SystemState name key value world error} ->
    {head : Transition first middle} ->
    {rest : Transitions middle finalState} ->
    (0 tailEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
      selected rest) ->
    LocatedClosingHeadView name key world error value nameEq keyEq head rest
      selected (S (transitionCount (traceBeforeOpening tailEpisode)))

0 closingAtHeadAfterDecomposition :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {first, middle, finalState,
    openingBefore, openingAfter, closeBefore, closeAfter :
      SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (opening : BeginStep nameEq keyEq selected openingBefore openingAfter) ->
  (inside : Transitions openingAfter closeBefore) ->
  (0 installedInside : InstalledTrace name key world error value nameEq keyEq
    selected inside) ->
  (closing : UnloadStep nameEq keyEq selected closeBefore closeAfter) ->
  (afterClosing : Transitions closeAfter finalState) ->
  (0 decomposition :
    MoreTransitions (beginTransition opening)
      (appendTransitions
        (appendTransitions inside
          (MoreTransitions (unloadTransition closing) NoTransitions))
        afterClosing) = MoreTransitions head rest) ->
  LocatedClosingHeadView name key world error value nameEq keyEq head rest
    selected Z
closingAtHeadAfterDecomposition head rest opening inside installedInside closing
  afterClosing decomposition =
    case decomposition of
      Refl => ClosingOpensHere opening
        (MkFirstClosingResult closeBefore closeAfter inside installedInside closing
          afterClosing
          (sym (appendTransitionsAssociative inside
            (MoreTransitions (unloadTransition closing) NoTransitions)
            afterClosing))) Refl

0 closingEpisodeAtHeadView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {first, middle, finalState, preStart, afterState :
    SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (episode : ClosedEpisode name key world error value nameEq keyEq selected
    preStart afterState) ->
  (afterClosing : Transitions afterState finalState) ->
  (0 decomposition :
    MoreTransitions (beginTransition (closedOpening episode))
      (appendTransitions (closedTransitions episode) afterClosing) =
    MoreTransitions head rest) ->
  LocatedClosingHeadView name key world error value nameEq keyEq head rest
    selected Z
closingEpisodeAtHeadView head rest
  (MkClosedEpisode openingAfter closeBefore opening inside installedInside closing)
  afterClosing decomposition =
    closingAtHeadAfterDecomposition head rest opening inside installedInside closing
      afterClosing decomposition

0 closingInTailAfterDecomposition :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {first, middle, prefixMiddle, finalState, preStart, afterState :
    SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (prefixHead : Transition first prefixMiddle) ->
  (prefixRest : Transitions prefixMiddle preStart) ->
  (episode : ClosedEpisode name key world error value nameEq keyEq selected
    preStart afterState) ->
  (afterClosing : Transitions afterState finalState) ->
  (0 decomposition :
    MoreTransitions prefixHead
      (appendTransitions prefixRest
        (MoreTransitions (beginTransition (closedOpening episode))
          (appendTransitions (closedTransitions episode) afterClosing))) =
    MoreTransitions head rest) ->
  LocatedClosingHeadView name key world error value nameEq keyEq head rest
    selected (S (transitionCount prefixRest))
closingInTailAfterDecomposition head rest prefixHead prefixRest episode
  afterClosing decomposition =
    case decomposition of
      Refl => ClosingOpensLater
        (MkLocatedClosedEpisode preStart afterState prefixRest episode afterClosing
          Refl)

0 locatedClosingPrefixHeadView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {first, middle, finalState, preStart, afterState :
    SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (beforeOpening : Transitions first preStart) ->
  (episode : ClosedEpisode name key world error value nameEq keyEq selected
    preStart afterState) ->
  (afterClosing : Transitions afterState finalState) ->
  (0 decomposition :
    appendTransitions beforeOpening
      (MoreTransitions (beginTransition (closedOpening episode))
        (appendTransitions (closedTransitions episode) afterClosing)) =
    MoreTransitions head rest) ->
  LocatedClosingHeadView name key world error value nameEq keyEq head rest
    selected (transitionCount beforeOpening)
locatedClosingPrefixHeadView head rest NoTransitions episode afterClosing
  decomposition =
    closingEpisodeAtHeadView head rest episode afterClosing decomposition
locatedClosingPrefixHeadView head rest
  (MoreTransitions prefixHead prefixRest) episode afterClosing decomposition =
    closingInTailAfterDecomposition head rest prefixHead prefixRest episode
      afterClosing decomposition

0 locatedClosingHeadView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected (MoreTransitions head rest)) ->
  LocatedClosingHeadView name key world error value nameEq keyEq head rest
    selected (transitionCount (traceBeforeOpening episode))
locatedClosingHeadView head rest
  (MkLocatedClosedEpisode preStart afterState beforeOpening episode afterClosing
    decomposition) =
      locatedClosingPrefixHeadView head rest beforeOpening episode afterClosing
        decomposition

0 falseNotTrueO7 : False = True -> Void
falseNotTrueO7 Refl impossible

0 unloadStepTargetUninstalledO7 :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {before, afterState : SystemState name key value world error} ->
  UnloadStep nameEq keyEq selected before afterState ->
  installedAt @{nameEq} selected afterState = False
unloadStepTargetUninstalledO7 nameEq keyEq selected {before} {afterState}
  (MkUnloadStep checked) =
    snd (snd (lUnloadBoundary nameEq keyEq selected before afterState LUnloadTag
      (checkedActionProjects nameEq keyEq (LUnload selected) before afterState
        LUnloadTag checked)))

0 closingOccursAfterPrefix :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {first, before, afterState, finalState :
    SystemState name key value world error} ->
  (earlier : Transitions first before) ->
  (closing : UnloadStep nameEq keyEq selected before afterState) ->
  (suffix : Transitions afterState finalState) ->
  OccursIn (unloadTransition closing)
    (appendTransitions earlier
      (MoreTransitions (unloadTransition closing) suffix))
closingOccursAfterPrefix NoTransitions closing suffix = OccursHere
closingOccursAfterPrefix (MoreTransitions prefixHead prefixRest) closing suffix =
  OccursLater (closingOccursAfterPrefix prefixRest closing suffix)

0 transportClosingOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {first, before, afterState, finalState :
    SystemState name key value world error} ->
  {closing : UnloadStep nameEq keyEq selected before afterState} ->
  {left, right : Transitions first finalState} ->
  left = right ->
  OccursIn (unloadTransition closing) left ->
  OccursIn (unloadTransition closing) right
transportClosingOccurrence Refl occurs = occurs

0 firstClosingOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (result : FirstClosingResult name key world error value nameEq keyEq selected
    trace) ->
  OccursIn (unloadTransition (firstClosingStep result)) trace
firstClosingOccurrence
  (MkFirstClosingResult before afterState earlier installedPrefix closing suffix
    decomposition) =
      transportClosingOccurrence decomposition
        (closingOccursAfterPrefix earlier closing suffix)

0 installedTraceRejectsClosing :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, before, afterState, finalState :
    SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  (0 installed : InstalledTrace name key world error value nameEq keyEq selected
    trace) ->
  (closing : UnloadStep nameEq keyEq selected before afterState) ->
  (0 occurs : OccursIn (unloadTransition closing) trace) -> Void
installedTraceRejectsClosing nameEq keyEq selected trace installed closing occurs =
  case splitInstalledAtOccurrence (unloadTransition closing) trace installed
    occurs of
      MkInstalledOccurrenceSplit earlier suffix installedPrefix installedSuffix
        sourceInstalled targetInstalled decomposition =>
          falseNotTrueO7
            (trans (sym (unloadStepTargetUninstalledO7 nameEq keyEq selected
              closing)) targetInstalled)

0 installedTraceRejectsFirstClosing :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  (0 installed : InstalledTrace name key world error value nameEq keyEq selected
    trace) ->
  (0 result : FirstClosingResult name key world error value nameEq keyEq selected
    trace) -> Void
installedTraceRejectsFirstClosing nameEq keyEq selected trace installed result =
  installedTraceRejectsClosing nameEq keyEq selected trace installed
    (firstClosingStep result) (firstClosingOccurrence result)

0 prependClosingUnique :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (occurrences : List
    (ClosingEpisodeOccurrence name key world error value nameEq keyEq rest)) ->
  UniqueKeys (map (\occurrence => scannedClosingOrdinal occurrence) occurrences) ->
  UniqueKeys (map (\occurrence => scannedClosingOrdinal occurrence)
    (prependClosingOccurrences head rest occurrences))
prependClosingUnique head rest occurrences unique =
  rewrite prependClosingOrdinals head rest occurrences in
    uniqueSuccessors unique

0 prependClosingComplete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (occurrences : List
    (ClosingEpisodeOccurrence name key world error value nameEq keyEq rest)) ->
  (0 complete : (selected : name) ->
    (episode : LocatedClosedEpisode name key world error value nameEq keyEq
      selected rest) ->
    Elem (transitionCount (traceBeforeOpening episode))
      (map (\occurrence => scannedClosingOrdinal occurrence) occurrences)) ->
  (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected rest) ->
  Elem (S (transitionCount (traceBeforeOpening episode)))
    (map (\occurrence => scannedClosingOrdinal occurrence)
      (prependClosingOccurrences head rest occurrences))
prependClosingComplete head rest occurrences complete selected episode =
  rewrite prependClosingOrdinals head rest occurrences in
    successorElem (complete selected episode)

0 prependClosingOccurrencesEmpty :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (occurrences : List
    (ClosingEpisodeOccurrence name key world error value nameEq keyEq rest)) ->
  prependClosingOccurrences head rest occurrences = [] -> occurrences = []
prependClosingOccurrencesEmpty head rest [] empty = Refl
prependClosingOccurrencesEmpty head rest (occurrence :: later) empty =
  case empty of Refl impossible

0 noLocatedClosingEmptyPrefix :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {initial, preStart, afterState : SystemState name key value world error} ->
  (beforeOpening : Transitions initial preStart) ->
  (episode : ClosedEpisode name key world error value nameEq keyEq selected
    preStart afterState) ->
  (afterClosing : Transitions afterState initial) ->
  (0 decomposition :
    appendTransitions beforeOpening
      (MoreTransitions (beginTransition (closedOpening episode))
        (appendTransitions (closedTransitions episode) afterClosing)) =
    NoTransitions) -> Void
noLocatedClosingEmptyPrefix NoTransitions episode afterClosing decomposition =
  case decomposition of Refl impossible
noLocatedClosingEmptyPrefix (MoreTransitions head rest) episode afterClosing
  decomposition = case decomposition of Refl impossible

0 noLocatedClosingInEmpty :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {state : SystemState name key value world error} ->
  LocatedClosedEpisode name key world error value nameEq keyEq selected
    (NoTransitions {state}) -> Void
noLocatedClosingInEmpty
  (MkLocatedClosedEpisode preStart afterState beforeOpening episode afterClosing
    decomposition) =
      noLocatedClosingEmptyPrefix beforeOpening episode afterClosing decomposition

||| Proof-level O7 output.  The scanner enumerates every located closing
||| occurrence exactly once by opening ordinal and turns an empty erased scan
||| into the no-closing predicate consumed by proof-level recursion.
public export
record ClosingEpisodeScan
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkClosingEpisodeScan
  0 scannedClosingOccurrences : List
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

0 locatedClosingAtHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (opening : BeginStep nameEq keyEq selected first middle) ->
  (rest : Transitions middle finalState) ->
  (result : FirstClosingResult name key world error value nameEq keyEq selected
    rest) ->
  LocatedClosedEpisode name key world error value nameEq keyEq selected
    (MoreTransitions (beginTransition opening) rest)
locatedClosingAtHead opening rest
  (MkFirstClosingResult closeBefore closeAfter beforeClosing installedBefore
    closing afterClosing closingSplit) =
      MkLocatedClosedEpisode first closeAfter NoTransitions
        (MkClosedEpisode middle closeBefore opening beforeClosing installedBefore
          closing)
        afterClosing
        (cong (MoreTransitions (beginTransition opening))
          (trans
            (appendTransitionsAssociative beforeClosing
              (MoreTransitions (unloadTransition closing) NoTransitions)
              afterClosing)
            closingSplit))

0 headClosingOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (opening : BeginStep nameEq keyEq selected first middle) ->
  (rest : Transitions middle finalState) ->
  (result : FirstClosingResult name key world error value nameEq keyEq selected
    rest) ->
  ClosingEpisodeOccurrence name key world error value nameEq keyEq
    (MoreTransitions (beginTransition opening) rest)
headClosingOccurrence opening rest result =
  ErasedClosingEpisodeOccurrence selected
    (locatedClosingAtHead opening rest result)

0 headClosingOrdinalZero :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (opening : BeginStep nameEq keyEq selected first middle) ->
  (rest : Transitions middle finalState) ->
  (result : FirstClosingResult name key world error value nameEq keyEq selected
    rest) ->
  scannedClosingOrdinal (headClosingOccurrence opening rest result) = Z
headClosingOrdinalZero opening rest
  (MkFirstClosingResult closeBefore closeAfter beforeClosing installedBefore
    closing afterClosing closingSplit) = Refl

0 headClosingFresh :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (opening : BeginStep nameEq keyEq selected first middle) ->
  (rest : Transitions middle finalState) ->
  (result : FirstClosingResult name key world error value nameEq keyEq selected
    rest) ->
  (occurrences : List
    (ClosingEpisodeOccurrence name key world error value nameEq keyEq rest)) ->
  Not (Elem (scannedClosingOrdinal
      (headClosingOccurrence opening rest result))
    (map (\occurrence => scannedClosingOrdinal occurrence)
      (prependClosingOccurrences (beginTransition opening) rest occurrences)))
headClosingFresh opening rest result occurrences present =
  zeroAbsentFromSuccessors
    (map (\occurrence => scannedClosingOrdinal occurrence) occurrences)
    (replace {p = \entries => Elem Z entries}
      (prependClosingOrdinals (beginTransition opening) rest occurrences)
      (replace {p = \ordinal => Elem ordinal
        (map (\occurrence => scannedClosingOrdinal occurrence)
          (prependClosingOccurrences (beginTransition opening) rest occurrences))}
        (headClosingOrdinalZero opening rest result) present))

0 headClosingCompleteFromView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (opening : BeginStep nameEq keyEq selected first middle) ->
  (rest : Transitions middle finalState) ->
  (result : FirstClosingResult name key world error value nameEq keyEq selected
    rest) ->
  (occurrences : List
    (ClosingEpisodeOccurrence name key world error value nameEq keyEq rest)) ->
  (0 complete : (actor : name) ->
    (episode : LocatedClosedEpisode name key world error value nameEq keyEq actor
      rest) ->
    Elem (transitionCount (traceBeforeOpening episode))
      (map (\occurrence => scannedClosingOrdinal occurrence) occurrences)) ->
  (actor : name) -> {ordinal : Nat} ->
  LocatedClosingHeadView name key world error value nameEq keyEq
    (beginTransition opening) rest actor ordinal ->
  Elem ordinal
    (map (\occurrence => scannedClosingOrdinal occurrence)
      (headClosingOccurrence opening rest result ::
        prependClosingOccurrences (beginTransition opening) rest occurrences))
headClosingCompleteFromView opening rest result occurrences complete actor
  (ClosingOpensHere suppliedOpening suppliedClosing headOpening) =
    rewrite headClosingOrdinalZero opening rest result in Here
headClosingCompleteFromView opening rest result occurrences complete actor
  (ClosingOpensLater tailEpisode) =
    There (prependClosingComplete (beginTransition opening) rest occurrences
      complete actor tailEpisode)

0 headClosingComplete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (opening : BeginStep nameEq keyEq selected first middle) ->
  (rest : Transitions middle finalState) ->
  (result : FirstClosingResult name key world error value nameEq keyEq selected
    rest) ->
  (occurrences : List
    (ClosingEpisodeOccurrence name key world error value nameEq keyEq rest)) ->
  (0 complete : (actor : name) ->
    (episode : LocatedClosedEpisode name key world error value nameEq keyEq actor
      rest) ->
    Elem (transitionCount (traceBeforeOpening episode))
      (map (\occurrence => scannedClosingOrdinal occurrence) occurrences)) ->
  (actor : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq actor
    (MoreTransitions (beginTransition opening) rest)) ->
  Elem (transitionCount (traceBeforeOpening episode))
    (map (\occurrence => scannedClosingOrdinal occurrence)
      (headClosingOccurrence opening rest result ::
        prependClosingOccurrences (beginTransition opening) rest occurrences))
headClosingComplete opening rest result occurrences complete actor episode =
  headClosingCompleteFromView opening rest result occurrences complete actor
    (locatedClosingHeadView (beginTransition opening) rest episode)

0 withoutHeadClosingCompleteFromView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (0 headImpossible : (actor : name) ->
    (opening : BeginStep nameEq keyEq actor first middle) ->
    FirstClosingResult name key world error value nameEq keyEq actor rest ->
    head = beginTransition opening -> Void) ->
  (occurrences : List
    (ClosingEpisodeOccurrence name key world error value nameEq keyEq rest)) ->
  (0 complete : (actor : name) ->
    (episode : LocatedClosedEpisode name key world error value nameEq keyEq actor
      rest) ->
    Elem (transitionCount (traceBeforeOpening episode))
      (map (\occurrence => scannedClosingOrdinal occurrence) occurrences)) ->
  (actor : name) -> {ordinal : Nat} ->
  LocatedClosingHeadView name key world error value nameEq keyEq head rest actor
    ordinal ->
  Elem ordinal
    (map (\occurrence => scannedClosingOrdinal occurrence)
      (prependClosingOccurrences head rest occurrences))
withoutHeadClosingCompleteFromView head rest headImpossible occurrences complete
  actor (ClosingOpensHere opening firstClosing headOpening) =
    void (headImpossible actor opening firstClosing headOpening)
withoutHeadClosingCompleteFromView head rest headImpossible occurrences complete
  actor (ClosingOpensLater tailEpisode) =
    prependClosingComplete head rest occurrences complete actor tailEpisode

0 withoutHeadClosingComplete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (0 headImpossible : (actor : name) ->
    (opening : BeginStep nameEq keyEq actor first middle) ->
    FirstClosingResult name key world error value nameEq keyEq actor rest ->
    head = beginTransition opening -> Void) ->
  (occurrences : List
    (ClosingEpisodeOccurrence name key world error value nameEq keyEq rest)) ->
  (0 complete : (actor : name) ->
    (episode : LocatedClosedEpisode name key world error value nameEq keyEq actor
      rest) ->
    Elem (transitionCount (traceBeforeOpening episode))
      (map (\occurrence => scannedClosingOrdinal occurrence) occurrences)) ->
  (actor : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq actor
    (MoreTransitions head rest)) ->
  Elem (transitionCount (traceBeforeOpening episode))
    (map (\occurrence => scannedClosingOrdinal occurrence)
      (prependClosingOccurrences head rest occurrences))
withoutHeadClosingComplete head rest headImpossible occurrences complete actor
  episode =
    withoutHeadClosingCompleteFromView head rest headImpossible occurrences
      complete actor (locatedClosingHeadView head rest episode)

0 withoutHeadClosingFreeFromView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (0 headImpossible : (actor : name) ->
    (opening : BeginStep nameEq keyEq actor first middle) ->
    FirstClosingResult name key world error value nameEq keyEq actor rest ->
    head = beginTransition opening -> Void) ->
  (occurrences : List
    (ClosingEpisodeOccurrence name key world error value nameEq keyEq rest)) ->
  (0 tailFree : occurrences = [] ->
    NoClosingEpisodes name key world error value nameEq keyEq rest) ->
  (0 empty : prependClosingOccurrences head rest occurrences = []) ->
  (actor : name) -> {ordinal : Nat} ->
  LocatedClosingHeadView name key world error value nameEq keyEq head rest actor
    ordinal -> Void
withoutHeadClosingFreeFromView head rest headImpossible occurrences tailFree
  empty actor (ClosingOpensHere opening firstClosing headOpening) =
    headImpossible actor opening firstClosing headOpening
withoutHeadClosingFreeFromView head rest headImpossible occurrences tailFree
  empty actor (ClosingOpensLater tailEpisode) =
    tailFree (prependClosingOccurrencesEmpty head rest occurrences empty)
      actor tailEpisode

0 withoutHeadClosingFree :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (0 headImpossible : (actor : name) ->
    (opening : BeginStep nameEq keyEq actor first middle) ->
    FirstClosingResult name key world error value nameEq keyEq actor rest ->
    head = beginTransition opening -> Void) ->
  (occurrences : List
    (ClosingEpisodeOccurrence name key world error value nameEq keyEq rest)) ->
  (0 tailFree : occurrences = [] ->
    NoClosingEpisodes name key world error value nameEq keyEq rest) ->
  prependClosingOccurrences head rest occurrences = [] ->
  NoClosingEpisodes name key world error value nameEq keyEq
    (MoreTransitions head rest)
withoutHeadClosingFree head rest headImpossible occurrences tailFree empty actor
  episode =
    withoutHeadClosingFreeFromView head rest headImpossible occurrences tailFree
      empty actor (locatedClosingHeadView head rest episode)

0 emptyScanCompleteness :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {state : SystemState name key value world error} ->
  (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected (NoTransitions {state})) ->
  Elem (transitionCount (traceBeforeOpening episode)) []
emptyScanCompleteness selected episode =
  void (noLocatedClosingInEmpty episode)

0 emptyScanClosingFree :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {state : SystemState name key value world error} ->
  [] = [] -> NoClosingEpisodes name key world error value nameEq keyEq
    (NoTransitions {state})
emptyScanClosingFree empty selected episode = noLocatedClosingInEmpty episode

0 emptyClosingEpisodeScan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  ClosingEpisodeScan name key world error value nameEq keyEq
    (NoTransitions {state})
emptyClosingEpisodeScan nameEq keyEq state =
  MkClosingEpisodeScan [] UniqueNil emptyScanCompleteness emptyScanClosingFree

0 closingScanWithoutHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (0 headImpossible : (actor : name) ->
    (opening : BeginStep nameEq keyEq actor first middle) ->
    FirstClosingResult name key world error value nameEq keyEq actor rest ->
    head = beginTransition opening -> Void) ->
  (0 tailScan : ClosingEpisodeScan name key world error value nameEq keyEq
    rest) ->
  ClosingEpisodeScan name key world error value nameEq keyEq
    (MoreTransitions head rest)
closingScanWithoutHead head rest headImpossible tailScan =
  MkClosingEpisodeScan
    (prependClosingOccurrences head rest (scannedClosingOccurrences tailScan))
    (prependClosingUnique head rest (scannedClosingOccurrences tailScan)
      (scannedClosingOrdinalsUnique tailScan))
    (withoutHeadClosingComplete head rest headImpossible
      (scannedClosingOccurrences tailScan)
      (everyClosingOccurrenceScanned tailScan))
    (withoutHeadClosingFree head rest headImpossible
      (scannedClosingOccurrences tailScan) (emptyScanIsClosingFree tailScan))

0 headClosingScanNonEmpty :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (opening : BeginStep nameEq keyEq selected first middle) ->
  (rest : Transitions middle finalState) ->
  (result : FirstClosingResult name key world error value nameEq keyEq selected
    rest) ->
  (occurrences : List
    (ClosingEpisodeOccurrence name key world error value nameEq keyEq rest)) ->
  headClosingOccurrence opening rest result ::
    prependClosingOccurrences (beginTransition opening) rest occurrences = [] ->
  NoClosingEpisodes name key world error value nameEq keyEq
    (MoreTransitions (beginTransition opening) rest)
headClosingScanNonEmpty opening rest result occurrences empty =
  case empty of Refl impossible

0 closingScanWithHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (opening : BeginStep nameEq keyEq selected first middle) ->
  (rest : Transitions middle finalState) ->
  (result : FirstClosingResult name key world error value nameEq keyEq selected
    rest) ->
  (0 tailScan : ClosingEpisodeScan name key world error value nameEq keyEq
    rest) ->
  ClosingEpisodeScan name key world error value nameEq keyEq
    (MoreTransitions (beginTransition opening) rest)
closingScanWithHead opening rest result tailScan =
  MkClosingEpisodeScan
    (headClosingOccurrence opening rest result ::
      prependClosingOccurrences (beginTransition opening) rest
        (scannedClosingOccurrences tailScan))
    (UniqueCons
      (headClosingFresh opening rest result
        (scannedClosingOccurrences tailScan))
      (prependClosingUnique (beginTransition opening) rest
        (scannedClosingOccurrences tailScan)
        (scannedClosingOrdinalsUnique tailScan)))
    (headClosingComplete opening rest result
      (scannedClosingOccurrences tailScan)
      (everyClosingOccurrenceScanned tailScan))
    (headClosingScanNonEmpty opening rest result
      (scannedClosingOccurrences tailScan))

data NonBeginAction :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  Action name key value world error -> Type where
  NonBeginOInsert : NonBeginAction (OInsert actor parent component)
  NonBeginORetire : NonBeginAction (ORetire actor)
  NonBeginORemove : NonBeginAction (ORemove actor)
  NonBeginLAdvance : NonBeginAction (LAdvance actor)
  NonBeginLDivert : NonBeginAction (LDivert actor)
  NonBeginLLeave : NonBeginAction (LLeave actor)
  NonBeginLUnload : NonBeginAction (LUnload actor)

0 nonBeginActionDistinct :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {action : Action name key value world error} ->
  NonBeginAction action -> (actor : name) -> action = LBegin actor -> Void
nonBeginActionDistinct NonBeginOInsert actor same =
  case same of Refl impossible
nonBeginActionDistinct NonBeginORetire actor same =
  case same of Refl impossible
nonBeginActionDistinct NonBeginORemove actor same =
  case same of Refl impossible
nonBeginActionDistinct NonBeginLAdvance actor same =
  case same of Refl impossible
nonBeginActionDistinct NonBeginLDivert actor same =
  case same of Refl impossible
nonBeginActionDistinct NonBeginLLeave actor same =
  case same of Refl impossible
nonBeginActionDistinct NonBeginLUnload actor same =
  case same of Refl impossible

0 openingHeadAction :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, middle : SystemState name key value world error} ->
  {action : Action name key value world error} -> {tag : RuleTag} ->
  {checked : checkedApplyAction @{nameEq} @{keyEq} action first =
    Just (tag, middle)} ->
  (actor : name) ->
  (opening : BeginStep nameEq keyEq actor first middle) ->
  Fired nameEq keyEq action tag checked = beginTransition opening ->
  action = LBegin actor
openingHeadAction actor opening Refl = Refl

0 nonBeginHeadImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action first =
    Just (tag, middle)) ->
  (rest : Transitions middle finalState) ->
  (0 nonBegin : NonBeginAction action) ->
  (actor : name) ->
  (opening : BeginStep nameEq keyEq actor first middle) ->
  FirstClosingResult name key world error value nameEq keyEq actor rest ->
  Fired nameEq keyEq action tag checked = beginTransition opening -> Void
nonBeginHeadImpossible action tag checked rest nonBegin actor opening firstClosing
  headOpening =
    nonBeginActionDistinct nonBegin actor
      (openingHeadAction actor opening headOpening)

0 beginOpeningActorEquality :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, middle : SystemState name key value world error} ->
  (owner : name) -> {tag : RuleTag} ->
  {checked : checkedApplyAction @{nameEq} @{keyEq} (LBegin owner) first =
    Just (tag, middle)} ->
  (actor : name) ->
  (opening : BeginStep nameEq keyEq actor first middle) ->
  Fired nameEq keyEq (LBegin owner) tag checked = beginTransition opening ->
  owner = actor
beginOpeningActorEquality owner actor opening headOpening =
  case headOpening of Refl => Refl

0 installedBeginHeadImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (owner : name) -> {tag : RuleTag} ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LBegin owner) first =
    Just (tag, middle)) ->
  (rest : Transitions middle finalState) ->
  (0 installed : InstalledTrace name key world error value nameEq keyEq owner
    rest) ->
  (actor : name) ->
  (opening : BeginStep nameEq keyEq actor first middle) ->
  (firstClosing : FirstClosingResult name key world error value nameEq keyEq
    actor rest) ->
  Fired nameEq keyEq (LBegin owner) tag checked = beginTransition opening -> Void
installedBeginHeadImpossible nameEq keyEq owner checked rest installed actor
  opening firstClosing headOpening =
    case beginOpeningActorEquality owner actor opening headOpening of
      Refl => installedTraceRejectsFirstClosing nameEq keyEq owner rest installed
        firstClosing

0 scanBeginContinuation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (owner : name) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LBegin owner) first =
    Just (LBeginTag, middle)) ->
  (rest : Transitions middle finalState) ->
  (0 tailScan : ClosingEpisodeScan name key world error value nameEq keyEq
    {initial = middle} {finalState = finalState} rest) ->
  InstalledContinuation name key world error value nameEq keyEq owner
    {first = middle} {finalState = finalState} rest ->
  ClosingEpisodeScan name key world error value nameEq keyEq
    {initial = first} {finalState = finalState} (MoreTransitions (Fired nameEq keyEq (LBegin owner) LBeginTag checked) rest)
scanBeginContinuation nameEq keyEq owner checked rest tailScan
  (ContinuationCloses firstClosing) =
    closingScanWithHead (MkBeginStep checked) rest firstClosing tailScan
scanBeginContinuation nameEq keyEq owner checked rest tailScan
  (ContinuationStaysInstalled installed) =
    closingScanWithoutHead
      (Fired nameEq keyEq (LBegin owner) LBeginTag checked) rest
      (installedBeginHeadImpossible nameEq keyEq owner checked rest installed)
      tailScan

0 scanBeginTagShape :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (owner : name) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LBegin owner) first =
    Just (tag, middle)) ->
  (rest : Transitions middle finalState) ->
  (0 alignedRest : AlignedTransitions name key world error value nameEq keyEq
    rest) ->
  (0 targetInstalled : installedAt @{nameEq} owner middle = True) ->
  (0 tailScan : ClosingEpisodeScan name key world error value nameEq keyEq
    {initial = middle} {finalState = finalState} rest) ->
  tag = LBeginTag ->
  ClosingEpisodeScan name key world error value nameEq keyEq
    {initial = first} {finalState = finalState} (MoreTransitions (Fired nameEq keyEq (LBegin owner) tag checked) rest)
scanBeginTagShape nameEq keyEq owner tag checked rest alignedRest targetInstalled
  tailScan tagShape =
    case tagShape of
      Refl => scanBeginContinuation nameEq keyEq owner checked rest tailScan
        (classifyInstalledContinuation nameEq keyEq owner rest alignedRest
          targetInstalled)

0 scanBeginBoundary :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (owner : name) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LBegin owner) first =
    Just (tag, middle)) ->
  (rest : Transitions middle finalState) ->
  (0 alignedRest : AlignedTransitions name key world error value nameEq keyEq
    rest) ->
  (0 tailScan : ClosingEpisodeScan name key world error value nameEq keyEq
    {initial = middle} {finalState = finalState} rest) ->
  (tag = LBeginTag,
   installedAt @{nameEq} owner first = False,
   installedAt @{nameEq} owner middle = True) ->
  ClosingEpisodeScan name key world error value nameEq keyEq
    {initial = first} {finalState = finalState} (MoreTransitions (Fired nameEq keyEq (LBegin owner) tag checked) rest)
scanBeginBoundary nameEq keyEq owner tag checked rest alignedRest tailScan
  (tagShape, sourceUninstalled, targetInstalled) =
    scanBeginTagShape nameEq keyEq owner tag checked rest alignedRest
      targetInstalled tailScan tagShape

0 scanBeginHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (owner : name) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LBegin owner) first =
    Just (tag, middle)) ->
  (rest : Transitions middle finalState) ->
  (0 alignedRest : AlignedTransitions name key world error value nameEq keyEq
    rest) ->
  (0 tailScan : ClosingEpisodeScan name key world error value nameEq keyEq
    {initial = middle} {finalState = finalState} rest) ->
  ClosingEpisodeScan name key world error value nameEq keyEq
    {initial = first} {finalState = finalState} (MoreTransitions (Fired nameEq keyEq (LBegin owner) tag checked) rest)
scanBeginHead nameEq keyEq owner tag checked rest alignedRest tailScan =
  scanBeginBoundary nameEq keyEq owner tag checked rest alignedRest tailScan
    (lBeginBoundary nameEq keyEq owner _ _ tag checked)

0 scanActionHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action first =
    Just (tag, middle)) ->
  (rest : Transitions middle finalState) ->
  (0 alignedRest : AlignedTransitions name key world error value nameEq keyEq
    rest) ->
  (0 tailScan : ClosingEpisodeScan name key world error value nameEq keyEq
    {initial = middle} {finalState = finalState} rest) ->
  ClosingEpisodeScan name key world error value nameEq keyEq
    {initial = first} {finalState = finalState}
    (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
scanActionHead nameEq keyEq (OInsert actor parent component) tag checked rest
  alignedRest tailScan =
    closingScanWithoutHead
      (Fired nameEq keyEq (OInsert actor parent component) tag checked) rest
      (nonBeginHeadImpossible (OInsert actor parent component) tag checked rest
        NonBeginOInsert)
      tailScan
scanActionHead nameEq keyEq (ORetire actor) tag checked rest alignedRest
  tailScan =
    closingScanWithoutHead (Fired nameEq keyEq (ORetire actor) tag checked) rest
      (nonBeginHeadImpossible (ORetire actor) tag checked rest NonBeginORetire)
      tailScan
scanActionHead nameEq keyEq (ORemove actor) tag checked rest alignedRest
  tailScan =
    closingScanWithoutHead (Fired nameEq keyEq (ORemove actor) tag checked) rest
      (nonBeginHeadImpossible (ORemove actor) tag checked rest NonBeginORemove)
      tailScan
scanActionHead nameEq keyEq (LBegin actor) tag checked rest alignedRest tailScan =
  scanBeginHead nameEq keyEq actor tag checked rest alignedRest tailScan
scanActionHead nameEq keyEq (LAdvance actor) tag checked rest alignedRest
  tailScan =
    closingScanWithoutHead (Fired nameEq keyEq (LAdvance actor) tag checked) rest
      (nonBeginHeadImpossible (LAdvance actor) tag checked rest
        NonBeginLAdvance)
      tailScan
scanActionHead nameEq keyEq (LDivert actor) tag checked rest alignedRest
  tailScan =
    closingScanWithoutHead (Fired nameEq keyEq (LDivert actor) tag checked) rest
      (nonBeginHeadImpossible (LDivert actor) tag checked rest NonBeginLDivert)
      tailScan
scanActionHead nameEq keyEq (LLeave actor) tag checked rest alignedRest
  tailScan =
    closingScanWithoutHead (Fired nameEq keyEq (LLeave actor) tag checked) rest
      (nonBeginHeadImpossible (LLeave actor) tag checked rest NonBeginLLeave)
      tailScan
scanActionHead nameEq keyEq (LUnload actor) tag checked rest alignedRest
  tailScan =
    closingScanWithoutHead (Fired nameEq keyEq (LUnload actor) tag checked) rest
      (nonBeginHeadImpossible (LUnload actor) tag checked rest NonBeginLUnload)
      tailScan

||| O7 is a separate erased producer rather than work hidden in O8/O9.  Quantity
||| 0 is essential because `MoreTransitions` erases its middle-state index.  The
||| exact trace alignment is the minimum authentication needed to reclassify
||| every stored checked transition under the scan's explicit dictionaries.
public export
0 closingEpisodeOccurrenceScanSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (initial, finalState : SystemState name key value world error) ->
  (trace : Transitions initial finalState) ->
  (0 aligned : AlignedTransitions name key world error value nameEq keyEq trace) ->
  ClosingEpisodeScan name key world error value nameEq keyEq trace
closingEpisodeOccurrenceScanSpike nameEq keyEq _ state NoTransitions aligned =
  case aligned of
    AlignedEnd => emptyClosingEpisodeScan nameEq keyEq state
closingEpisodeOccurrenceScanSpike nameEq keyEq initial finalState
  (MoreTransitions head rest) aligned =
    case aligned of
      AlignedStep action tag checked _ alignedRest =>
        scanActionHead nameEq keyEq action tag checked rest alignedRest
          (closingEpisodeOccurrenceScanSpike nameEq keyEq _ finalState rest
            alignedRest)

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

||| Producer-owned exact lookup equation for the only dependent branch of an
||| L-Begin registration-index advance.
0 advanceBeginRegistrationIndexDeletedAt :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (ordinal : Nat) -> (actor : name) ->
  (live : GenerationEnvironment name) ->
  (activations : List (name, RegistrationActivation name)) ->
  (counts : List (RegistrationActivation name, Nat)) ->
  (deleted : List (RegistrationGeneration name)) ->
  (found : Maybe (RegistrationGeneration name)) ->
  lookupCurrentGeneration @{nameEq} actor live = found ->
  indexedDeletedGenerations
    (advanceRegistrationIndex @{nameEq} {key = key} {value = value}
      {world = world} {error = error} ordinal (LBegin actor)
      (MkRegistrationIndexState live activations counts deleted)) = deleted
advanceBeginRegistrationIndexDeletedAt nameEq ordinal actor live activations
  counts deleted Nothing found = rewrite found in Refl
advanceBeginRegistrationIndexDeletedAt nameEq ordinal actor live activations
  counts deleted (Just generation) found = rewrite found in Refl

||| Producer-owned exact activation equation for the sole dependent branch of a
||| surviving child-registration index advance.
0 advanceSurvivingRegistrationIndexDeletedAt :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (child, parent : name) ->
  (component : Component key value world error) ->
  (live : GenerationEnvironment name) ->
  (activations : List (name, RegistrationActivation name)) ->
  (counts : List (RegistrationActivation name, Nat)) ->
  (deleted : List (RegistrationGeneration name)) ->
  (found : Maybe (RegistrationActivation name)) ->
  lookupParentActivation @{nameEq} parent activations = found ->
  indexedDeletedGenerations
    (advanceSurvivingRegistrationIndex @{nameEq} ordinal child parent component
      (MkRegistrationIndexState live activations counts deleted)) = deleted
advanceSurvivingRegistrationIndexDeletedAt nameEq ordinal child parent component
  live activations counts deleted Nothing found = rewrite found in Refl
advanceSurvivingRegistrationIndexDeletedAt nameEq ordinal child parent component
  live activations counts deleted (Just activation) found = rewrite found in Refl

||| Ordinary scanner advancement never removes an already discarded exact
||| generation.  This small projection isolates the only lookup split in the
||| generic index update from the correspondence induction below.
0 advanceRegistrationIndexDeletedExact :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (action : Action name key value world error) ->
  (index : RegistrationIndexState name) ->
  indexedDeletedGenerations
    (advanceRegistrationIndex @{nameEq} ordinal action index) =
  indexedDeletedGenerations index
advanceRegistrationIndexDeletedExact nameEq ordinal
  (OInsert child (ChildOf parent) component)
  (MkRegistrationIndexState live activations counts deleted) = Refl
advanceRegistrationIndexDeletedExact nameEq ordinal
  (OInsert root Root component)
  (MkRegistrationIndexState live activations counts deleted) = Refl
advanceRegistrationIndexDeletedExact nameEq ordinal (ORetire actor) index = Refl
advanceRegistrationIndexDeletedExact nameEq ordinal (ORemove actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
advanceRegistrationIndexDeletedExact nameEq ordinal (LBegin actor)
  (MkRegistrationIndexState live activations counts deleted) =
    advanceBeginRegistrationIndexDeletedAt nameEq ordinal actor live activations
      counts deleted (lookupCurrentGeneration @{nameEq} actor live) Refl
advanceRegistrationIndexDeletedExact nameEq ordinal (LAdvance actor) index = Refl
advanceRegistrationIndexDeletedExact nameEq ordinal (LDivert actor) index = Refl
advanceRegistrationIndexDeletedExact nameEq ordinal (LLeave actor) index = Refl
advanceRegistrationIndexDeletedExact nameEq ordinal (LUnload actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl

||| A deleted-registration advance prepends exactly its stamped generation.
0 advanceDeletedRegistrationIndexHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (child, parent : name) ->
  (component : Component key value world error) ->
  (index : RegistrationIndexState name) ->
  indexedDeletedGenerations
    (advanceDeletedRegistrationIndex @{nameEq} ordinal child parent component
      index) =
  MkRegistrationGeneration child ordinal :: indexedDeletedGenerations index
advanceDeletedRegistrationIndexHead nameEq ordinal child parent component
  (MkRegistrationIndexState live activations counts deleted) = Refl

||| A surviving-registration advance leaves the exact deleted list unchanged.
0 advanceSurvivingRegistrationIndexDeletedExact :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (child, parent : name) ->
  (component : Component key value world error) ->
  (index : RegistrationIndexState name) ->
  indexedDeletedGenerations
    (advanceSurvivingRegistrationIndex @{nameEq} ordinal child parent component
      index) =
  indexedDeletedGenerations index
advanceSurvivingRegistrationIndexDeletedExact nameEq ordinal child parent
  component (MkRegistrationIndexState live activations counts deleted) =
    advanceSurvivingRegistrationIndexDeletedAt nameEq ordinal child parent
      component live activations counts deleted
      (lookupParentActivation @{nameEq} parent activations) Refl

||| Once an exact generation is in the left scanner's deleted index, every
||| accepted continuation preserves that membership through every scanner
||| constructor class.
0 leftCorrespondencePreservesDeleted :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {renaming : RegistrationGenerationBijection name} ->
  {leftOrdinal : Nat} -> {leftIndex : RegistrationIndexState name} ->
  {leftFirst, leftFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} ->
  {leftFinalIndex : RegistrationIndexState name} ->
  {rightOrdinal : Nat} -> {rightIndex : RegistrationIndexState name} ->
  {rightFirst, rightFinal : SystemState name key value world error} ->
  {right : Transitions rightFirst rightFinal} ->
  {rightFinalIndex : RegistrationIndexState name} ->
  {pendingLeft, pendingRight :
    List (RegistrationEvent name key world error value)} ->
  (correspondence : RegistrationTraceCorrespondence nameEq renaming leftOrdinal
    leftIndex left leftFinalIndex rightOrdinal rightIndex right rightFinalIndex
    pendingLeft pendingRight) ->
  (generation : RegistrationGeneration name) ->
  Elem generation (indexedDeletedGenerations leftIndex) ->
  Elem generation (indexedDeletedGenerations leftFinalIndex)
leftCorrespondencePreservesDeleted nameEq RegistrationCorrespondenceEnd
  generation member = member
leftCorrespondencePreservesDeleted nameEq
  (SkipLeftNonRegistration action transition leftRest sameAction generated
    rest) generation member =
      leftCorrespondencePreservesDeleted nameEq rest generation
        (replace {p = \deleted => Elem generation deleted}
          (sym (advanceRegistrationIndexDeletedExact nameEq _ action _)) member)
leftCorrespondencePreservesDeleted nameEq
  (SkipRightNonRegistration action transition rightRest sameAction generated
    rest) generation member =
      leftCorrespondencePreservesDeleted nameEq rest generation member
leftCorrespondencePreservesDeleted nameEq
  (DiscardLeftDeletedRegistration {child} {parent} {component} transition
    leftRest sameAction deleted rest) generation member =
      leftCorrespondencePreservesDeleted nameEq rest generation
        (replace {p = \items => Elem generation items}
          (sym (advanceDeletedRegistrationIndexHead nameEq _ child parent
            component _)) (There member))
leftCorrespondencePreservesDeleted nameEq
  (DiscardRightDeletedRegistration transition rightRest sameAction deleted rest)
  generation member =
    leftCorrespondencePreservesDeleted nameEq rest generation member
leftCorrespondencePreservesDeleted nameEq
  (QueueLeftGeneratedRegistration {child} {parent} {component} transition
    leftRest sameAction surviving rest) generation member =
      leftCorrespondencePreservesDeleted nameEq rest generation
        (replace {p = \deleted => Elem generation deleted}
          (sym (advanceSurvivingRegistrationIndexDeletedExact nameEq _ child
            parent component _)) member)
leftCorrespondencePreservesDeleted nameEq
  (QueueRightGeneratedRegistration transition rightRest sameAction surviving
    rest) generation member =
      leftCorrespondencePreservesDeleted nameEq rest generation member
leftCorrespondencePreservesDeleted nameEq
  (MatchLeftWithPendingRight {child} {parent} {component} transition leftRest
    sameAction surviving rightPrefix rightEvent rightSuffix matched rest)
  generation member =
    leftCorrespondencePreservesDeleted nameEq rest generation
      (replace {p = \deleted => Elem generation deleted}
        (sym (advanceSurvivingRegistrationIndexDeletedExact nameEq _ child
          parent component _)) member)
leftCorrespondencePreservesDeleted nameEq
  (MatchRightWithPendingLeft transition rightRest sameAction surviving leftPrefix
    leftEvent leftSuffix matched rest) generation member =
      leftCorrespondencePreservesDeleted nameEq rest generation member

||| A surviving scanner classification and a later unload occurrence are
||| disjoint.  This is the local contradiction used exactly at the located
||| generated-registration head.
0 scannerNoParentUnloadRejectsOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {parent : name} -> {trace : Transitions first finalState} ->
  NoParentUnload parent trace -> ActionOccurs (LUnload parent) trace -> Void
scannerNoParentUnloadRejectsOccurrence NoParentUnloadEnd occurrence impossible
scannerNoParentUnloadRejectsOccurrence
  (NoParentUnloadStep transition rest different laterSafe)
  (ActionOccursHere transition rest unload) = different unload
scannerNoParentUnloadRejectsOccurrence
  (NoParentUnloadStep transition rest different laterSafe)
  (ActionOccursLater transition rest laterOccurrence) =
    scannerNoParentUnloadRejectsOccurrence laterSafe laterOccurrence

||| A generated registration head cannot be classified as a non-registration
||| scanner action.
0 generatedRegistrationHeadNotSkipped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  (transition : Transition before afterState) ->
  (action : Action name key value world error) ->
  (child, parent : name) ->
  (component : Component key value world error) ->
  transitionAction transition = action ->
  transitionAction transition = OInsert child (ChildOf parent) component ->
  isGeneratedRegistrationAction action = False -> Void
generatedRegistrationHeadNotSkipped transition action child parent component
  sameAction generatedAction nonRegistration =
    case trans (sym nonRegistration)
      (cong isGeneratedRegistrationAction
        (trans (sym sameAction) generatedAction)) of
      Refl impossible

||| The scanner event producer stores the supplied raw parent independently of
||| its activation lookup.
0 registrationEventAtParentExact :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (index : RegistrationIndexState name) -> (child, parent : name) ->
  (component : Component key value world error) ->
  eventParent
    (registrationEventAt @{nameEq} ordinal index child parent component) = parent
registrationEventAtParentExact nameEq ordinal
  (MkRegistrationIndexState live activations counts deleted) child parent
  component = Refl

||| A scanner surviving classification for the exact registration head
||| contradicts the producer-owned later parent-unload occurrence.
0 generatedRegistrationHeadNotSurviving :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {ordinal : Nat} ->
  {index : RegistrationIndexState name} ->
  {before, afterState, finalState : SystemState name key value world error} ->
  (transition : Transition before afterState) ->
  (rest : Transitions afterState finalState) ->
  (scannerChild, scannerParent, child, parent : name) ->
  (scannerComponent, component : Component key value world error) ->
  transitionAction transition =
    OInsert scannerChild (ChildOf scannerParent) scannerComponent ->
  transitionAction transition = OInsert child (ChildOf parent) component ->
  SurvivingRegistration
    (registrationEventAt @{nameEq} ordinal index scannerChild scannerParent
      scannerComponent) rest ->
  ActionOccurs (LUnload parent) rest -> Void
generatedRegistrationHeadNotSurviving transition rest scannerChild scannerParent
  child parent scannerComponent component scannerAction generatedAction
  surviving closes =
    case trans (sym generatedAction) scannerAction of
      Refl => scannerNoParentUnloadRejectsOccurrence
        (replace {p = \selected => NoParentUnload selected rest}
          (registrationEventAtParentExact nameEq ordinal index child parent
            component)
          (survivingParentEpisodeOpen surviving)) closes

||| The exact discard head enters the index and remains there for the accepted
||| scanner continuation.
0 leftDiscardedRegistrationHeadRetained :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {renaming : RegistrationGenerationBijection name} ->
  (leftOrdinal : Nat) -> (leftIndex : RegistrationIndexState name) ->
  {leftFirst, leftMiddle, leftFinal : SystemState name key value world error} ->
  (transition : Transition leftFirst leftMiddle) ->
  (leftRest : Transitions leftMiddle leftFinal) ->
  (scannerChild, scannerParent, child, parent : name) ->
  (scannerComponent, component : Component key value world error) ->
  transitionAction transition =
    OInsert scannerChild (ChildOf scannerParent) scannerComponent ->
  transitionAction transition = OInsert child (ChildOf parent) component ->
  {leftFinalIndex : RegistrationIndexState name} ->
  {rightOrdinal : Nat} -> {rightIndex : RegistrationIndexState name} ->
  {rightFirst, rightFinal : SystemState name key value world error} ->
  {right : Transitions rightFirst rightFinal} ->
  {rightFinalIndex : RegistrationIndexState name} ->
  {pendingLeft, pendingRight :
    List (RegistrationEvent name key world error value)} ->
  RegistrationTraceCorrespondence nameEq renaming (S leftOrdinal)
    (advanceDeletedRegistrationIndex @{nameEq} leftOrdinal scannerChild
      scannerParent scannerComponent leftIndex)
    leftRest leftFinalIndex rightOrdinal rightIndex right rightFinalIndex
    pendingLeft pendingRight ->
  Elem (MkRegistrationGeneration child leftOrdinal)
    (indexedDeletedGenerations leftFinalIndex)
leftDiscardedRegistrationHeadRetained nameEq leftOrdinal leftIndex transition
  leftRest scannerChild scannerParent child parent scannerComponent component
  scannerAction generatedAction rest =
    case trans (sym generatedAction) scannerAction of
      Refl => leftCorrespondencePreservesDeleted nameEq rest
        (MkRegistrationGeneration child leftOrdinal)
        (replace {p = \items => Elem
          (MkRegistrationGeneration child leftOrdinal) items}
          (sym (advanceDeletedRegistrationIndexHead nameEq leftOrdinal child
            parent component leftIndex)) Here)

||| Producer-owned head/tail view for one exact generated registration in the
||| left scanner trace.  Both the local ordinal and the dependent suffix are
||| retained, so recursive scanner consumers never reconstruct either from an
||| action equality.
data LeftScannerGeneratedHeadView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (child, parent : name) ->
  (component : Component key value world error) ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (occurrence : LocatedGeneratedRegistration child parent component
    (MoreTransitions head rest)) -> Type where
  LeftScannerGeneratedAtHead :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, middle, finalState : SystemState name key value world error} ->
    {child, parent : name} ->
    {component : Component key value world error} ->
    {head : Transition first middle} ->
    {rest : Transitions middle finalState} ->
    {occurrence : LocatedGeneratedRegistration child parent component
      (MoreTransitions head rest)} ->
    (0 actionShape : transitionAction head =
      OInsert child (ChildOf parent) component) ->
    (0 exactAfterState : registrationAfter occurrence = middle) ->
    (0 exactAfter : replace
      {p = \state => Transitions state finalState} exactAfterState
      (afterRegistration occurrence) = rest) ->
    (0 exactOrdinal : registrationOrdinal occurrence = Z) ->
    LeftScannerGeneratedHeadView child parent component head rest occurrence
  LeftScannerGeneratedInTail :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, middle, finalState : SystemState name key value world error} ->
    {child, parent : name} ->
    {component : Component key value world error} ->
    {head : Transition first middle} ->
    {rest : Transitions middle finalState} ->
    {occurrence : LocatedGeneratedRegistration child parent component
      (MoreTransitions head rest)} ->
    (0 tailOccurrence : LocatedGeneratedRegistration child parent component
      rest) ->
    (0 exactAfterState : registrationAfter occurrence =
      registrationAfter tailOccurrence) ->
    (0 exactAfter : replace
      {p = \state => Transitions state finalState} exactAfterState
      (afterRegistration occurrence) = afterRegistration tailOccurrence) ->
    (0 exactOrdinal : registrationOrdinal occurrence =
      S (registrationOrdinal tailOccurrence)) ->
    LeftScannerGeneratedHeadView child parent component head rest occurrence

0 leftScannerGeneratedAtHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState, afterState :
    SystemState name key value world error} ->
  (child, parent : name) ->
  (component : Component key value world error) ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (transition : Transition first afterState) ->
  (later : Transitions afterState finalState) ->
  (0 actionShape : transitionAction transition =
    OInsert child (ChildOf parent) component) ->
  (0 decomposition : MoreTransitions transition later =
    MoreTransitions head rest) ->
  LeftScannerGeneratedHeadView child parent component head rest
    (MkLocatedGeneratedRegistration first afterState NoTransitions transition
      later actionShape decomposition)
leftScannerGeneratedAtHead child parent component head rest transition later
  actionShape decomposition =
    case decomposition of
      Refl => LeftScannerGeneratedAtHead actionShape Refl Refl Refl

0 leftScannerGeneratedInTail :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, prefixMiddle, before, afterState, finalState :
    SystemState name key value world error} ->
  (child, parent : name) ->
  (component : Component key value world error) ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (prefixHead : Transition first prefixMiddle) ->
  (prefixRest : Transitions prefixMiddle before) ->
  (transition : Transition before afterState) ->
  (later : Transitions afterState finalState) ->
  (0 actionShape : transitionAction transition =
    OInsert child (ChildOf parent) component) ->
  (0 decomposition : MoreTransitions prefixHead
    (appendTransitions prefixRest (MoreTransitions transition later)) =
    MoreTransitions head rest) ->
  LeftScannerGeneratedHeadView child parent component head rest
    (MkLocatedGeneratedRegistration before afterState
      (MoreTransitions prefixHead prefixRest) transition later actionShape
      decomposition)
leftScannerGeneratedInTail child parent component head rest prefixHead prefixRest
  transition later actionShape decomposition =
    case decomposition of
      Refl => LeftScannerGeneratedInTail
        (MkLocatedGeneratedRegistration _ _ prefixRest transition later
          actionShape Refl)
        Refl Refl Refl

0 leftScannerGeneratedHeadParts :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, before, afterState, finalState :
    SystemState name key value world error} ->
  (child, parent : name) ->
  (component : Component key value world error) ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (beforeTrace : Transitions first before) ->
  (transition : Transition before afterState) ->
  (later : Transitions afterState finalState) ->
  (0 actionShape : transitionAction transition =
    OInsert child (ChildOf parent) component) ->
  (0 decomposition : appendTransitions beforeTrace
    (MoreTransitions transition later) = MoreTransitions head rest) ->
  LeftScannerGeneratedHeadView child parent component head rest
    (MkLocatedGeneratedRegistration before afterState beforeTrace transition
      later actionShape decomposition)
leftScannerGeneratedHeadParts child parent component head rest NoTransitions
  transition later actionShape decomposition =
    leftScannerGeneratedAtHead child parent component head rest transition later
      actionShape decomposition
leftScannerGeneratedHeadParts child parent component head rest
  (MoreTransitions prefixHead prefixRest) transition later actionShape
  decomposition =
    leftScannerGeneratedInTail child parent component head rest prefixHead
      prefixRest transition later actionShape decomposition

0 leftScannerGeneratedHeadView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (child, parent : name) ->
  (component : Component key value world error) ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (occurrence : LocatedGeneratedRegistration child parent component
    (MoreTransitions head rest)) ->
  LeftScannerGeneratedHeadView child parent component head rest occurrence
leftScannerGeneratedHeadView child parent component head rest occurrence =
  case occurrence of
    MkLocatedGeneratedRegistration before afterState beforeTrace transition later
      actionShape decomposition =>
        leftScannerGeneratedHeadParts child parent component head rest beforeTrace
          transition later actionShape decomposition

0 leftScannerActionOccursTraceEquality :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (left, right : Transitions first finalState) ->
  (0 exact : left = right) -> ActionOccurs action left -> ActionOccurs action right
leftScannerActionOccursTraceEquality action left right exact occurrence =
  case exact of
    Refl => occurrence

0 leftScannerActionOccursAfterExact :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {leftFirst, rightFirst, finalState :
    SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (left : Transitions leftFirst finalState) ->
  (right : Transitions rightFirst finalState) ->
  (0 exactFirst : leftFirst = rightFirst) ->
  (0 exactTrace : replace
    {p = \state => Transitions state finalState} exactFirst left = right) ->
  ActionOccurs action left -> ActionOccurs action right
leftScannerActionOccursAfterExact action left right exactFirst exactTrace
  occurrence =
    case exactFirst of
      Refl => leftScannerActionOccursTraceEquality action left right exactTrace
        occurrence

0 leftScannerLocatedInEmptyImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {state : SystemState name key value world error} ->
  {child, parent : name} ->
  {component : Component key value world error} ->
  LocatedGeneratedRegistration child parent component
    (NoTransitions {state = state}) -> Void
leftScannerLocatedInEmptyImpossible
  (MkLocatedGeneratedRegistration before afterState beforeTrace transition later
    actionShape decomposition) =
      case beforeTrace of
        NoTransitions => case decomposition of Refl impossible
        MoreTransitions prefixHead prefixRest =>
          case decomposition of Refl impossible

mutual
  0 leftScannerLocatedDiscardFold :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) ->
    {renaming : RegistrationGenerationBijection name} ->
    (leftOrdinal : Nat) -> (leftIndex : RegistrationIndexState name) ->
    {leftFirst, leftFinal : SystemState name key value world error} ->
    {left : Transitions leftFirst leftFinal} ->
    {leftFinalIndex : RegistrationIndexState name} ->
    {rightOrdinal : Nat} -> {rightIndex : RegistrationIndexState name} ->
    {rightFirst, rightFinal : SystemState name key value world error} ->
    {right : Transitions rightFirst rightFinal} ->
    {rightFinalIndex : RegistrationIndexState name} ->
    {pendingLeft, pendingRight :
      List (RegistrationEvent name key world error value)} ->
    (correspondence : RegistrationTraceCorrespondence nameEq renaming leftOrdinal
      leftIndex left leftFinalIndex rightOrdinal rightIndex right rightFinalIndex
      pendingLeft pendingRight) ->
    (child, parent : name) ->
    (component : Component key value world error) ->
    (occurrence : LocatedGeneratedRegistration child parent component left) ->
    ActionOccurs (LUnload parent) (afterRegistration occurrence) ->
    Elem (MkRegistrationGeneration child
      (leftOrdinal + registrationOrdinal occurrence))
      (indexedDeletedGenerations leftFinalIndex)
  leftScannerLocatedDiscardFold nameEq leftOrdinal leftIndex
    RegistrationCorrespondenceEnd child parent component occurrence closes =
      void (leftScannerLocatedInEmptyImpossible occurrence)
  leftScannerLocatedDiscardFold nameEq leftOrdinal leftIndex
    (SkipLeftNonRegistration action transition leftRest sameAction generated
      rest) child parent component occurrence closes =
        leftScannerSkipView nameEq leftOrdinal leftIndex action transition leftRest
          sameAction generated rest child parent component occurrence closes
          (leftScannerGeneratedHeadView child parent component transition leftRest
            occurrence)
  leftScannerLocatedDiscardFold nameEq leftOrdinal leftIndex
    (SkipRightNonRegistration action transition rightRest sameAction generated
      rest) child parent component occurrence closes =
        leftScannerLocatedDiscardFold nameEq leftOrdinal leftIndex rest child
          parent component occurrence closes
  leftScannerLocatedDiscardFold nameEq leftOrdinal leftIndex
    (DiscardLeftDeletedRegistration transition leftRest sameAction deleted rest)
    child parent component occurrence closes =
      leftScannerDiscardView nameEq leftOrdinal leftIndex transition leftRest
        sameAction deleted rest child parent component occurrence closes
        (leftScannerGeneratedHeadView child parent component transition leftRest
          occurrence)
  leftScannerLocatedDiscardFold nameEq leftOrdinal leftIndex
    (DiscardRightDeletedRegistration transition rightRest sameAction deleted rest)
    child parent component occurrence closes =
      leftScannerLocatedDiscardFold nameEq leftOrdinal leftIndex rest child
        parent component occurrence closes
  leftScannerLocatedDiscardFold nameEq leftOrdinal leftIndex
    (QueueLeftGeneratedRegistration transition leftRest sameAction surviving rest)
    child parent component occurrence closes =
      leftScannerQueueView nameEq leftOrdinal leftIndex transition leftRest
        sameAction surviving rest child parent component occurrence closes
        (leftScannerGeneratedHeadView child parent component transition leftRest
          occurrence)
  leftScannerLocatedDiscardFold nameEq leftOrdinal leftIndex
    (QueueRightGeneratedRegistration transition rightRest sameAction surviving
      rest) child parent component occurrence closes =
        leftScannerLocatedDiscardFold nameEq leftOrdinal leftIndex rest child
          parent component occurrence closes
  leftScannerLocatedDiscardFold nameEq leftOrdinal leftIndex
    (MatchLeftWithPendingRight transition leftRest sameAction surviving rightPrefix
      rightEvent rightSuffix matched rest) child parent component occurrence
      closes =
        leftScannerMatchView nameEq leftOrdinal leftIndex transition leftRest
          sameAction surviving rightPrefix rightEvent rightSuffix matched rest
          child parent component occurrence closes
          (leftScannerGeneratedHeadView child parent component transition leftRest
            occurrence)
  leftScannerLocatedDiscardFold nameEq leftOrdinal leftIndex
    (MatchRightWithPendingLeft transition rightRest sameAction surviving leftPrefix
      leftEvent leftSuffix matched rest) child parent component occurrence closes =
        leftScannerLocatedDiscardFold nameEq leftOrdinal leftIndex rest child
          parent component occurrence closes

  0 leftScannerSkipView :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) ->
    {renaming : RegistrationGenerationBijection name} ->
    (leftOrdinal : Nat) -> (leftIndex : RegistrationIndexState name) ->
    {leftFirst, leftMiddle, leftFinal :
      SystemState name key value world error} ->
    (action : Action name key value world error) ->
    (transition : Transition leftFirst leftMiddle) ->
    (leftRest : Transitions leftMiddle leftFinal) ->
    (0 sameAction : transitionAction transition = action) ->
    (0 generated : isGeneratedRegistrationAction action = False) ->
    {leftFinalIndex : RegistrationIndexState name} ->
    {rightOrdinal : Nat} -> {rightIndex : RegistrationIndexState name} ->
    {rightFirst, rightFinal : SystemState name key value world error} ->
    {right : Transitions rightFirst rightFinal} ->
    {rightFinalIndex : RegistrationIndexState name} ->
    {pendingLeft, pendingRight :
      List (RegistrationEvent name key world error value)} ->
    (rest : RegistrationTraceCorrespondence nameEq renaming (S leftOrdinal)
      (advanceRegistrationIndex @{nameEq} leftOrdinal action leftIndex)
      leftRest leftFinalIndex rightOrdinal rightIndex right rightFinalIndex
      pendingLeft pendingRight) ->
    (child, parent : name) ->
    (component : Component key value world error) ->
    (occurrence : LocatedGeneratedRegistration child parent component
      (MoreTransitions transition leftRest)) ->
    ActionOccurs (LUnload parent) (afterRegistration occurrence) ->
    LeftScannerGeneratedHeadView child parent component transition leftRest
      occurrence ->
    Elem (MkRegistrationGeneration child
      (leftOrdinal + registrationOrdinal occurrence))
      (indexedDeletedGenerations leftFinalIndex)
  leftScannerSkipView nameEq leftOrdinal leftIndex action transition leftRest
    sameAction generated rest child parent component occurrence closes
    (LeftScannerGeneratedAtHead actionShape exactAfterState exactAfter
      exactOrdinal) =
        void (generatedRegistrationHeadNotSkipped transition action child parent
          component sameAction actionShape generated)
  leftScannerSkipView nameEq leftOrdinal leftIndex action transition leftRest
    sameAction generated rest child parent component occurrence closes
    (LeftScannerGeneratedInTail tailOccurrence exactAfterState exactAfter
      exactOrdinal) =
        replace {p = \generation => Elem generation
          (indexedDeletedGenerations leftFinalIndex)}
          (sym (cong (MkRegistrationGeneration child)
            (trans (cong (leftOrdinal +) exactOrdinal)
              (sym (plusSuccRightSucc leftOrdinal
                (registrationOrdinal tailOccurrence))))))
          (leftScannerLocatedDiscardFold nameEq (S leftOrdinal)
            (advanceRegistrationIndex @{nameEq} leftOrdinal action leftIndex)
            rest child parent component tailOccurrence
            (leftScannerActionOccursAfterExact (LUnload parent)
              (afterRegistration occurrence) (afterRegistration tailOccurrence)
              exactAfterState exactAfter closes))

  0 leftScannerDiscardView :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) ->
    {renaming : RegistrationGenerationBijection name} ->
    (leftOrdinal : Nat) -> (leftIndex : RegistrationIndexState name) ->
    {leftFirst, leftMiddle, leftFinal :
      SystemState name key value world error} ->
    (transition : Transition leftFirst leftMiddle) ->
    (leftRest : Transitions leftMiddle leftFinal) ->
    {scannerChild, scannerParent : name} ->
    {scannerComponent : Component key value world error} ->
    (0 sameAction : transitionAction transition =
      OInsert scannerChild (ChildOf scannerParent) scannerComponent) ->
    (0 deleted : DeletedClosingRegistration
      (registrationEventAt @{nameEq} leftOrdinal leftIndex scannerChild
        scannerParent scannerComponent) leftRest) ->
    {leftFinalIndex : RegistrationIndexState name} ->
    {rightOrdinal : Nat} -> {rightIndex : RegistrationIndexState name} ->
    {rightFirst, rightFinal : SystemState name key value world error} ->
    {right : Transitions rightFirst rightFinal} ->
    {rightFinalIndex : RegistrationIndexState name} ->
    {pendingLeft, pendingRight :
      List (RegistrationEvent name key world error value)} ->
    (rest : RegistrationTraceCorrespondence nameEq renaming (S leftOrdinal)
      (advanceDeletedRegistrationIndex @{nameEq} leftOrdinal scannerChild
        scannerParent scannerComponent leftIndex)
      leftRest leftFinalIndex rightOrdinal rightIndex right rightFinalIndex
      pendingLeft pendingRight) ->
    (child, parent : name) ->
    (component : Component key value world error) ->
    (occurrence : LocatedGeneratedRegistration child parent component
      (MoreTransitions transition leftRest)) ->
    ActionOccurs (LUnload parent) (afterRegistration occurrence) ->
    LeftScannerGeneratedHeadView child parent component transition leftRest
      occurrence ->
    Elem (MkRegistrationGeneration child
      (leftOrdinal + registrationOrdinal occurrence))
      (indexedDeletedGenerations leftFinalIndex)
  leftScannerDiscardView nameEq leftOrdinal leftIndex transition leftRest
    sameAction deleted rest child parent component occurrence closes
    (LeftScannerGeneratedAtHead actionShape exactAfterState exactAfter
      exactOrdinal) =
        replace {p = \generation => Elem generation
          (indexedDeletedGenerations leftFinalIndex)}
          (sym (cong (MkRegistrationGeneration child)
            (trans (cong (leftOrdinal +) exactOrdinal)
              (plusZeroRightNeutral leftOrdinal))))
          (leftDiscardedRegistrationHeadRetained nameEq leftOrdinal leftIndex
            transition leftRest scannerChild scannerParent child parent
            scannerComponent component sameAction actionShape rest)
  leftScannerDiscardView nameEq leftOrdinal leftIndex transition leftRest
    sameAction deleted rest child parent component occurrence closes
    (LeftScannerGeneratedInTail tailOccurrence exactAfterState exactAfter
      exactOrdinal) =
        replace {p = \generation => Elem generation
          (indexedDeletedGenerations leftFinalIndex)}
          (sym (cong (MkRegistrationGeneration child)
            (trans (cong (leftOrdinal +) exactOrdinal)
              (sym (plusSuccRightSucc leftOrdinal
                (registrationOrdinal tailOccurrence))))))
          (leftScannerLocatedDiscardFold nameEq (S leftOrdinal)
            (advanceDeletedRegistrationIndex @{nameEq} leftOrdinal scannerChild
              scannerParent scannerComponent leftIndex)
            rest child parent component tailOccurrence
            (leftScannerActionOccursAfterExact (LUnload parent)
              (afterRegistration occurrence) (afterRegistration tailOccurrence)
              exactAfterState exactAfter closes))

  0 leftScannerQueueView :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) ->
    {renaming : RegistrationGenerationBijection name} ->
    (leftOrdinal : Nat) -> (leftIndex : RegistrationIndexState name) ->
    {leftFirst, leftMiddle, leftFinal :
      SystemState name key value world error} ->
    (transition : Transition leftFirst leftMiddle) ->
    (leftRest : Transitions leftMiddle leftFinal) ->
    {scannerChild, scannerParent : name} ->
    {scannerComponent : Component key value world error} ->
    (0 sameAction : transitionAction transition =
      OInsert scannerChild (ChildOf scannerParent) scannerComponent) ->
    (0 surviving : SurvivingRegistration
      (registrationEventAt @{nameEq} leftOrdinal leftIndex scannerChild
        scannerParent scannerComponent) leftRest) ->
    {leftFinalIndex : RegistrationIndexState name} ->
    {rightOrdinal : Nat} -> {rightIndex : RegistrationIndexState name} ->
    {rightFirst, rightFinal : SystemState name key value world error} ->
    {right : Transitions rightFirst rightFinal} ->
    {rightFinalIndex : RegistrationIndexState name} ->
    {pendingLeft, pendingRight :
      List (RegistrationEvent name key world error value)} ->
    (rest : RegistrationTraceCorrespondence nameEq renaming (S leftOrdinal)
      (advanceSurvivingRegistrationIndex @{nameEq} leftOrdinal scannerChild
        scannerParent scannerComponent leftIndex)
      leftRest leftFinalIndex rightOrdinal rightIndex right rightFinalIndex
      (registrationEventAt @{nameEq} leftOrdinal leftIndex scannerChild
        scannerParent scannerComponent :: pendingLeft) pendingRight) ->
    (child, parent : name) ->
    (component : Component key value world error) ->
    (occurrence : LocatedGeneratedRegistration child parent component
      (MoreTransitions transition leftRest)) ->
    ActionOccurs (LUnload parent) (afterRegistration occurrence) ->
    LeftScannerGeneratedHeadView child parent component transition leftRest
      occurrence ->
    Elem (MkRegistrationGeneration child
      (leftOrdinal + registrationOrdinal occurrence))
      (indexedDeletedGenerations leftFinalIndex)
  leftScannerQueueView nameEq leftOrdinal leftIndex transition leftRest sameAction
    surviving rest child parent component occurrence closes
    (LeftScannerGeneratedAtHead actionShape exactAfterState exactAfter
      exactOrdinal) =
        void (generatedRegistrationHeadNotSurviving transition leftRest
          scannerChild scannerParent child parent scannerComponent component
          sameAction actionShape surviving
          (leftScannerActionOccursAfterExact (LUnload parent)
            (afterRegistration occurrence) leftRest exactAfterState exactAfter
            closes))
  leftScannerQueueView nameEq leftOrdinal leftIndex transition leftRest sameAction
    surviving rest child parent component occurrence closes
    (LeftScannerGeneratedInTail tailOccurrence exactAfterState exactAfter
      exactOrdinal) =
        replace {p = \generation => Elem generation
          (indexedDeletedGenerations leftFinalIndex)}
          (sym (cong (MkRegistrationGeneration child)
            (trans (cong (leftOrdinal +) exactOrdinal)
              (sym (plusSuccRightSucc leftOrdinal
                (registrationOrdinal tailOccurrence))))))
          (leftScannerLocatedDiscardFold nameEq (S leftOrdinal)
            (advanceSurvivingRegistrationIndex @{nameEq} leftOrdinal scannerChild
              scannerParent scannerComponent leftIndex)
            rest child parent component tailOccurrence
            (leftScannerActionOccursAfterExact (LUnload parent)
              (afterRegistration occurrence) (afterRegistration tailOccurrence)
              exactAfterState exactAfter closes))

  0 leftScannerMatchView :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) ->
    {renaming : RegistrationGenerationBijection name} ->
    (leftOrdinal : Nat) -> (leftIndex : RegistrationIndexState name) ->
    {leftFirst, leftMiddle, leftFinal :
      SystemState name key value world error} ->
    (transition : Transition leftFirst leftMiddle) ->
    (leftRest : Transitions leftMiddle leftFinal) ->
    {scannerChild, scannerParent : name} ->
    {scannerComponent : Component key value world error} ->
    (0 sameAction : transitionAction transition =
      OInsert scannerChild (ChildOf scannerParent) scannerComponent) ->
    (0 surviving : SurvivingRegistration
      (registrationEventAt @{nameEq} leftOrdinal leftIndex scannerChild
        scannerParent scannerComponent) leftRest) ->
    (rightPrefix : List (RegistrationEvent name key world error value)) ->
    (rightEvent : RegistrationEvent name key world error value) ->
    (rightSuffix : List (RegistrationEvent name key world error value)) ->
    (0 matched : RegistrationEventMatch renaming
      (registrationEventAt @{nameEq} leftOrdinal leftIndex scannerChild
        scannerParent scannerComponent) rightEvent) ->
    {leftFinalIndex : RegistrationIndexState name} ->
    {rightOrdinal : Nat} -> {rightIndex : RegistrationIndexState name} ->
    {rightFirst, rightFinal : SystemState name key value world error} ->
    {right : Transitions rightFirst rightFinal} ->
    {rightFinalIndex : RegistrationIndexState name} ->
    {pendingLeft : List (RegistrationEvent name key world error value)} ->
    (rest : RegistrationTraceCorrespondence nameEq renaming (S leftOrdinal)
      (advanceSurvivingRegistrationIndex @{nameEq} leftOrdinal scannerChild
        scannerParent scannerComponent leftIndex)
      leftRest leftFinalIndex rightOrdinal rightIndex right rightFinalIndex
      pendingLeft (rightPrefix ++ rightSuffix)) ->
    (child, parent : name) ->
    (component : Component key value world error) ->
    (occurrence : LocatedGeneratedRegistration child parent component
      (MoreTransitions transition leftRest)) ->
    ActionOccurs (LUnload parent) (afterRegistration occurrence) ->
    LeftScannerGeneratedHeadView child parent component transition leftRest
      occurrence ->
    Elem (MkRegistrationGeneration child
      (leftOrdinal + registrationOrdinal occurrence))
      (indexedDeletedGenerations leftFinalIndex)
  leftScannerMatchView nameEq leftOrdinal leftIndex transition leftRest sameAction
    surviving rightPrefix rightEvent rightSuffix matched rest child parent
    component occurrence closes
    (LeftScannerGeneratedAtHead actionShape exactAfterState exactAfter
      exactOrdinal) =
        void (generatedRegistrationHeadNotSurviving transition leftRest
          scannerChild scannerParent child parent scannerComponent component
          sameAction actionShape surviving
          (leftScannerActionOccursAfterExact (LUnload parent)
            (afterRegistration occurrence) leftRest exactAfterState exactAfter
            closes))
  leftScannerMatchView nameEq leftOrdinal leftIndex transition leftRest sameAction
    surviving rightPrefix rightEvent rightSuffix matched rest child parent
    component occurrence closes
    (LeftScannerGeneratedInTail tailOccurrence exactAfterState exactAfter
      exactOrdinal) =
        replace {p = \generation => Elem generation
          (indexedDeletedGenerations leftFinalIndex)}
          (sym (cong (MkRegistrationGeneration child)
            (trans (cong (leftOrdinal +) exactOrdinal)
              (sym (plusSuccRightSucc leftOrdinal
                (registrationOrdinal tailOccurrence))))))
          (leftScannerLocatedDiscardFold nameEq (S leftOrdinal)
            (advanceSurvivingRegistrationIndex @{nameEq} leftOrdinal scannerChild
              scannerParent scannerComponent leftIndex)
            rest child parent component tailOccurrence
            (leftScannerActionOccursAfterExact (LUnload parent)
              (afterRegistration occurrence) (afterRegistration tailOccurrence)
              exactAfterState exactAfter closes))

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
deletedClassificationForcesLeftScannerDiscardSpike nameEq renaming
  leftFinalIndex rightFinalIndex correspondence generation
  (MkDeletedGenerationClassification parent component occurrence
    occurrenceGeneration closes) =
      replace {p = \observed => Elem observed
        (indexedDeletedGenerations leftFinalIndex)}
        occurrenceGeneration
        (leftScannerLocatedDiscardFold nameEq 0
          (the (RegistrationIndexState name) DGamma.CP3.emptyRegistrationIndex)
          correspondence (generationName generation) parent component occurrence
          closes)

||| Right-side mirror of deleted-index retention through every accepted scanner
||| constructor.
0 rightCorrespondencePreservesDeleted :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {renaming : RegistrationGenerationBijection name} ->
  {leftOrdinal : Nat} -> {leftIndex : RegistrationIndexState name} ->
  {leftFirst, leftFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} ->
  {leftFinalIndex : RegistrationIndexState name} ->
  {rightOrdinal : Nat} -> {rightIndex : RegistrationIndexState name} ->
  {rightFirst, rightFinal : SystemState name key value world error} ->
  {right : Transitions rightFirst rightFinal} ->
  {rightFinalIndex : RegistrationIndexState name} ->
  {pendingLeft, pendingRight :
    List (RegistrationEvent name key world error value)} ->
  (correspondence : RegistrationTraceCorrespondence nameEq renaming leftOrdinal
    leftIndex left leftFinalIndex rightOrdinal rightIndex right rightFinalIndex
    pendingLeft pendingRight) ->
  (generation : RegistrationGeneration name) ->
  Elem generation (indexedDeletedGenerations rightIndex) ->
  Elem generation (indexedDeletedGenerations rightFinalIndex)
rightCorrespondencePreservesDeleted nameEq RegistrationCorrespondenceEnd
  generation member = member
rightCorrespondencePreservesDeleted nameEq
  (SkipLeftNonRegistration action transition leftRest sameAction generated rest)
  generation member =
    rightCorrespondencePreservesDeleted nameEq rest generation member
rightCorrespondencePreservesDeleted nameEq
  (SkipRightNonRegistration action transition rightRest sameAction generated
    rest) generation member =
      rightCorrespondencePreservesDeleted nameEq rest generation
        (replace {p = \deleted => Elem generation deleted}
          (sym (advanceRegistrationIndexDeletedExact nameEq _ action _)) member)
rightCorrespondencePreservesDeleted nameEq
  (DiscardLeftDeletedRegistration transition leftRest sameAction deleted rest)
  generation member =
    rightCorrespondencePreservesDeleted nameEq rest generation member
rightCorrespondencePreservesDeleted nameEq
  (DiscardRightDeletedRegistration {child} {parent} {component} transition
    rightRest sameAction deleted rest) generation member =
      rightCorrespondencePreservesDeleted nameEq rest generation
        (replace {p = \items => Elem generation items}
          (sym (advanceDeletedRegistrationIndexHead nameEq _ child parent
            component _)) (There member))
rightCorrespondencePreservesDeleted nameEq
  (QueueLeftGeneratedRegistration transition leftRest sameAction surviving rest)
  generation member =
    rightCorrespondencePreservesDeleted nameEq rest generation member
rightCorrespondencePreservesDeleted nameEq
  (QueueRightGeneratedRegistration {child} {parent} {component} transition
    rightRest sameAction surviving rest) generation member =
      rightCorrespondencePreservesDeleted nameEq rest generation
        (replace {p = \deleted => Elem generation deleted}
          (sym (advanceSurvivingRegistrationIndexDeletedExact nameEq _ child
            parent component _)) member)
rightCorrespondencePreservesDeleted nameEq
  (MatchLeftWithPendingRight transition leftRest sameAction surviving rightPrefix
    rightEvent rightSuffix matched rest) generation member =
      rightCorrespondencePreservesDeleted nameEq rest generation member
rightCorrespondencePreservesDeleted nameEq
  (MatchRightWithPendingLeft {child} {parent} {component} transition rightRest
    sameAction surviving leftPrefix leftEvent leftSuffix matched rest)
  generation member =
    rightCorrespondencePreservesDeleted nameEq rest generation
      (replace {p = \deleted => Elem generation deleted}
        (sym (advanceSurvivingRegistrationIndexDeletedExact nameEq _ child parent
          component _)) member)

0 rightDiscardedRegistrationHeadRetained :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {renaming : RegistrationGenerationBijection name} ->
  {leftOrdinal : Nat} -> {leftIndex : RegistrationIndexState name} ->
  {leftFirst, leftFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} ->
  {leftFinalIndex : RegistrationIndexState name} ->
  (rightOrdinal : Nat) -> (rightIndex : RegistrationIndexState name) ->
  {rightFirst, rightMiddle, rightFinal :
    SystemState name key value world error} ->
  (transition : Transition rightFirst rightMiddle) ->
  (rightRest : Transitions rightMiddle rightFinal) ->
  (scannerChild, scannerParent, child, parent : name) ->
  (scannerComponent, component : Component key value world error) ->
  transitionAction transition =
    OInsert scannerChild (ChildOf scannerParent) scannerComponent ->
  transitionAction transition = OInsert child (ChildOf parent) component ->
  {rightFinalIndex : RegistrationIndexState name} ->
  {pendingLeft, pendingRight :
    List (RegistrationEvent name key world error value)} ->
  RegistrationTraceCorrespondence nameEq renaming leftOrdinal leftIndex left
    leftFinalIndex (S rightOrdinal)
    (advanceDeletedRegistrationIndex @{nameEq} rightOrdinal scannerChild
      scannerParent scannerComponent rightIndex)
    rightRest rightFinalIndex pendingLeft pendingRight ->
  Elem (MkRegistrationGeneration child rightOrdinal)
    (indexedDeletedGenerations rightFinalIndex)
rightDiscardedRegistrationHeadRetained nameEq rightOrdinal rightIndex transition
  rightRest scannerChild scannerParent child parent scannerComponent component
  scannerAction generatedAction rest =
    case trans (sym generatedAction) scannerAction of
      Refl => rightCorrespondencePreservesDeleted nameEq rest
        (MkRegistrationGeneration child rightOrdinal)
        (replace {p = \items => Elem
          (MkRegistrationGeneration child rightOrdinal) items}
          (sym (advanceDeletedRegistrationIndexHead nameEq rightOrdinal child
            parent component rightIndex)) Here)

0 inverseRegistrationGenerationBijection :
  RegistrationGenerationBijection name -> RegistrationGenerationBijection name
inverseRegistrationGenerationBijection renaming =
  MkRegistrationGenerationBijection
    (generationBackward renaming)
    (generationForward renaming)
    (generationRightInverse renaming)
    (generationLeftInverse renaming)

0 inverseRegistrationEventMatch :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (renaming : RegistrationGenerationBijection name) ->
  (left, right : RegistrationEvent name key world error value) ->
  RegistrationEventMatch renaming left right ->
  RegistrationEventMatch (inverseRegistrationGenerationBijection renaming)
    right left
inverseRegistrationEventMatch renaming left right
  (MkRegistrationEventMatch component leftActivation rightActivation leftPresent
    rightPresent childGeneration parentGeneration position) =
      MkRegistrationEventMatch (sym component) rightActivation leftActivation
        rightPresent leftPresent
        (trans
          (sym (cong (generationBackward renaming) childGeneration))
          (generationLeftInverse renaming (eventChildGeneration left)))
        (trans
          (sym (cong (generationBackward renaming) parentGeneration))
          (generationLeftInverse renaming
            (activationParentGeneration leftActivation)))
        (sym position)

0 symmetricRegistrationTraceCorrespondence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  (renaming : RegistrationGenerationBijection name) ->
  {leftOrdinal : Nat} -> {leftIndex : RegistrationIndexState name} ->
  {leftFirst, leftFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} ->
  {leftFinalIndex : RegistrationIndexState name} ->
  {rightOrdinal : Nat} -> {rightIndex : RegistrationIndexState name} ->
  {rightFirst, rightFinal : SystemState name key value world error} ->
  {right : Transitions rightFirst rightFinal} ->
  {rightFinalIndex : RegistrationIndexState name} ->
  {pendingLeft, pendingRight :
    List (RegistrationEvent name key world error value)} ->
  RegistrationTraceCorrespondence nameEq renaming leftOrdinal leftIndex left
    leftFinalIndex rightOrdinal rightIndex right rightFinalIndex pendingLeft
    pendingRight ->
  RegistrationTraceCorrespondence nameEq
    (inverseRegistrationGenerationBijection renaming)
    rightOrdinal rightIndex right rightFinalIndex leftOrdinal leftIndex left
    leftFinalIndex pendingRight pendingLeft
symmetricRegistrationTraceCorrespondence nameEq renaming
  RegistrationCorrespondenceEnd = RegistrationCorrespondenceEnd
symmetricRegistrationTraceCorrespondence nameEq renaming
  (SkipLeftNonRegistration action transition leftRest sameAction generated rest) =
    SkipRightNonRegistration action transition leftRest sameAction generated
      (symmetricRegistrationTraceCorrespondence nameEq renaming rest)
symmetricRegistrationTraceCorrespondence nameEq renaming
  (SkipRightNonRegistration action transition rightRest sameAction generated
    rest) =
      SkipLeftNonRegistration action transition rightRest sameAction generated
        (symmetricRegistrationTraceCorrespondence nameEq renaming rest)
symmetricRegistrationTraceCorrespondence nameEq renaming
  (DiscardLeftDeletedRegistration transition leftRest sameAction deleted rest) =
    DiscardRightDeletedRegistration transition leftRest sameAction deleted
      (symmetricRegistrationTraceCorrespondence nameEq renaming rest)
symmetricRegistrationTraceCorrespondence nameEq renaming
  (DiscardRightDeletedRegistration transition rightRest sameAction deleted
    rest) =
      DiscardLeftDeletedRegistration transition rightRest sameAction deleted
        (symmetricRegistrationTraceCorrespondence nameEq renaming rest)
symmetricRegistrationTraceCorrespondence nameEq renaming
  (QueueLeftGeneratedRegistration transition leftRest sameAction surviving rest) =
    QueueRightGeneratedRegistration transition leftRest sameAction surviving
      (symmetricRegistrationTraceCorrespondence nameEq renaming rest)
symmetricRegistrationTraceCorrespondence nameEq renaming
  (QueueRightGeneratedRegistration transition rightRest sameAction surviving
    rest) =
      QueueLeftGeneratedRegistration transition rightRest sameAction surviving
        (symmetricRegistrationTraceCorrespondence nameEq renaming rest)
symmetricRegistrationTraceCorrespondence nameEq renaming
  (MatchLeftWithPendingRight {child} {parent} {component} transition leftRest
    sameAction surviving rightPrefix rightEvent rightSuffix matched rest) =
      MatchRightWithPendingLeft transition leftRest sameAction surviving
        rightPrefix rightEvent rightSuffix
        (inverseRegistrationEventMatch renaming
          (registrationEventAt leftOrdinal leftIndex child parent component)
          rightEvent matched)
        (symmetricRegistrationTraceCorrespondence nameEq renaming rest)
symmetricRegistrationTraceCorrespondence nameEq renaming
  (MatchRightWithPendingLeft {child} {parent} {component} transition rightRest
    sameAction surviving leftPrefix leftEvent leftSuffix matched rest) =
      MatchLeftWithPendingRight transition rightRest sameAction surviving
        leftPrefix leftEvent leftSuffix
        (inverseRegistrationEventMatch renaming leftEvent
          (registrationEventAt rightOrdinal rightIndex child parent component)
          matched)
        (symmetricRegistrationTraceCorrespondence nameEq renaming rest)

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
deletedClassificationForcesRightScannerDiscardSpike nameEq renaming
  leftFinalIndex rightFinalIndex correspondence generation classification =
    deletedClassificationForcesLeftScannerDiscardSpike nameEq
      (inverseRegistrationGenerationBijection renaming) rightFinalIndex
      leftFinalIndex
      (symmetricRegistrationTraceCorrespondence nameEq renaming correspondence)
      generation classification

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

||| Prefix one source transition to a located occurrence in its tail.  Keeping
||| this structural operation separate avoids reconstructing occurrences from
||| raw action equality during the subsequence fold.
0 prependGenerationSubsequenceLocatedActionOccurrence :
  {sourceFirst, tailFirst, finalState :
    SystemState name key value world error} ->
  (head : Transition sourceFirst tailFirst) ->
  {tail : Transitions tailFirst finalState} ->
  LocatedActionOccurrence action tail ->
  LocatedActionOccurrence action (MoreTransitions head tail)
prependGenerationSubsequenceLocatedActionOccurrence head
  (MkLocatedActionOccurrence before afterState beforeTrace transition later
    actionShape decomposition) =
  MkLocatedActionOccurrence before afterState
    (MoreTransitions head beforeTrace) transition later actionShape
    (cong (MoreTransitions head) decomposition)

||| Every survivor occurrence has a producer-owned source occurrence.  The
||| proof follows the exact dependent prefix rather than searching by action
||| value, so equal registrations at different births remain distinct.
0 generationSubsequenceLocatedActionOrigin :
  (subsequence : GenerationActionSubsequence nameEq deletable ordinal live
    source survivor) ->
  LocatedActionOccurrence action survivor ->
  LocatedActionOccurrence action source
generationSubsequenceLocatedActionOrigin GenerationActionSubsequenceEnd
  (MkLocatedActionOccurrence before afterState beforeTrace transition later
    actionShape decomposition) =
  case beforeTrace of
    NoTransitions => case decomposition of Refl impossible
    MoreTransitions prefixHead prefixRest =>
      case decomposition of Refl impossible
generationSubsequenceLocatedActionOrigin
  (KeepGenerationAction originalTransition originalRest survivingTransition
    survivingRest kept sameAction tail)
  (MkLocatedActionOccurrence before afterState NoTransitions transition later
    actionShape decomposition) =
  case decomposition of
    Refl => MkLocatedActionOccurrence _ _ NoTransitions originalTransition
      originalRest (trans sameAction actionShape) Refl
generationSubsequenceLocatedActionOrigin
  (KeepGenerationAction originalTransition originalRest survivingTransition
    survivingRest kept sameAction tail)
  (MkLocatedActionOccurrence before afterState
    (MoreTransitions prefixHead prefixRest) transition later actionShape
      decomposition) =
  case decomposition of
    Refl => prependGenerationSubsequenceLocatedActionOccurrence originalTransition
      (generationSubsequenceLocatedActionOrigin tail
        (MkLocatedActionOccurrence _ _ prefixRest transition later actionShape
          Refl))
generationSubsequenceLocatedActionOrigin
  (DeleteGenerationAction originalTransition originalRest deleted tail)
  occurrence =
    prependGenerationSubsequenceLocatedActionOccurrence originalTransition
      (generationSubsequenceLocatedActionOrigin tail occurrence)

||| Producer-owned classification of one exact occurrence across an append
||| boundary.  Every index in the append telescope is constructor-owned.
public export
data DeletionLocatedAppendClassification :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (first, middle, finalState : SystemState name key value world error) ->
  (action : Action name key value world error) ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  (wholeOccurrence : LocatedActionOccurrence action
    (appendTransitions left right)) -> Type where
  DeletionLocatedInLeft :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, middle, finalState :
      SystemState name key value world error} ->
    {action : Action name key value world error} ->
    {left : Transitions first middle} ->
    {right : Transitions middle finalState} ->
    {wholeOccurrence : LocatedActionOccurrence action
      (appendTransitions left right)} ->
    (0 localOccurrence : LocatedActionOccurrence action left) ->
    (0 exactOrdinal : locatedActionOrdinal wholeOccurrence =
      locatedActionOrdinal localOccurrence) ->
    DeletionLocatedAppendClassification name key world error value first middle
      finalState action left right wholeOccurrence
  DeletionLocatedInRight :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, middle, finalState :
      SystemState name key value world error} ->
    {action : Action name key value world error} ->
    {left : Transitions first middle} ->
    {right : Transitions middle finalState} ->
    {wholeOccurrence : LocatedActionOccurrence action
      (appendTransitions left right)} ->
    (0 localOccurrence : LocatedActionOccurrence action right) ->
    (0 exactOrdinal : locatedActionOrdinal wholeOccurrence =
      transitionCount left + locatedActionOrdinal localOccurrence) ->
    DeletionLocatedAppendClassification name key world error value first middle
      finalState action left right wholeOccurrence

||| A one-step producer view for an exact located occurrence.  The tail
||| occurrence and ordinal equation are emitted by the producer, never inferred
||| by a consumer.
data DeletionLocatedHeadView :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (first, middle, finalState : SystemState name key value world error) ->
  (action : Action name key value world error) ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (wholeOccurrence : LocatedActionOccurrence action
    (MoreTransitions head rest)) -> Type where
  DeletionLocatedAtHead :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, middle, finalState :
      SystemState name key value world error} ->
    {action : Action name key value world error} ->
    {head : Transition first middle} ->
    {rest : Transitions middle finalState} ->
    {wholeOccurrence : LocatedActionOccurrence action
      (MoreTransitions head rest)} ->
    (0 actionShape : transitionAction head = action) ->
    (0 exactOrdinal : locatedActionOrdinal wholeOccurrence = Z) ->
    DeletionLocatedHeadView name key world error value first middle finalState
      action head rest wholeOccurrence
  DeletionLocatedInTail :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, middle, finalState :
      SystemState name key value world error} ->
    {action : Action name key value world error} ->
    {head : Transition first middle} ->
    {rest : Transitions middle finalState} ->
    {wholeOccurrence : LocatedActionOccurrence action
      (MoreTransitions head rest)} ->
    (0 tailOccurrence : LocatedActionOccurrence action rest) ->
    (0 exactOrdinal : locatedActionOrdinal wholeOccurrence =
      S (locatedActionOrdinal tailOccurrence)) ->
    DeletionLocatedHeadView name key world error value first middle finalState
      action head rest wholeOccurrence

0 deletionLocatedAtHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, afterState, finalState :
    SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (transition : Transition first afterState) ->
  (later : Transitions afterState finalState) ->
  (0 actionShape : transitionAction transition = action) ->
  (0 decomposition : MoreTransitions transition later =
    MoreTransitions head rest) ->
  DeletionLocatedHeadView name key world error value first middle finalState action
    head rest
    (MkLocatedActionOccurrence first afterState NoTransitions transition later
      actionShape decomposition)
deletionLocatedAtHead action head rest transition later actionShape decomposition =
  case decomposition of
    Refl => DeletionLocatedAtHead actionShape Refl

0 deletionLocatedInTail :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, prefixMiddle, before, afterState, finalState :
    SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (prefixHead : Transition first prefixMiddle) ->
  (prefixRest : Transitions prefixMiddle before) ->
  (transition : Transition before afterState) ->
  (later : Transitions afterState finalState) ->
  (0 actionShape : transitionAction transition = action) ->
  (0 decomposition : MoreTransitions prefixHead
    (appendTransitions prefixRest (MoreTransitions transition later)) =
    MoreTransitions head rest) ->
  DeletionLocatedHeadView name key world error value first middle finalState action
    head rest
    (MkLocatedActionOccurrence before afterState
      (MoreTransitions prefixHead prefixRest) transition later actionShape
      decomposition)
deletionLocatedInTail action head rest prefixHead prefixRest transition later
  actionShape decomposition =
    case decomposition of
      Refl => DeletionLocatedInTail
        (MkLocatedActionOccurrence _ _ prefixRest transition later actionShape
          Refl)
        Refl

0 deletionLocatedHeadParts :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, before, afterState, finalState :
    SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (beforeTrace : Transitions first before) ->
  (transition : Transition before afterState) ->
  (later : Transitions afterState finalState) ->
  (0 actionShape : transitionAction transition = action) ->
  (0 decomposition : appendTransitions beforeTrace
    (MoreTransitions transition later) = MoreTransitions head rest) ->
  DeletionLocatedHeadView name key world error value first middle finalState action
    head rest
    (MkLocatedActionOccurrence before afterState beforeTrace transition later
      actionShape decomposition)
deletionLocatedHeadParts action head rest NoTransitions transition later actionShape
  decomposition =
    deletionLocatedAtHead action head rest transition later actionShape decomposition
deletionLocatedHeadParts action head rest
  (MoreTransitions prefixHead prefixRest) transition later actionShape
  decomposition =
    deletionLocatedInTail action head rest prefixHead prefixRest transition later
      actionShape decomposition

0 deletionLocatedHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (wholeOccurrence : LocatedActionOccurrence action
    (MoreTransitions head rest)) ->
  DeletionLocatedHeadView name key world error value first middle finalState action
    head rest wholeOccurrence
deletionLocatedHead action head rest wholeOccurrence =
  case wholeOccurrence of
    MkLocatedActionOccurrence before afterState beforeTrace transition later
      actionShape decomposition =>
        deletionLocatedHeadParts action head rest beforeTrace transition later
          actionShape decomposition

data DeletionPrependedOccurrence :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (first, middle, finalState : SystemState name key value world error) ->
  (action : Action name key value world error) ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (localOccurrence : LocatedActionOccurrence action rest) -> Type where
  MkDeletionPrependedOccurrence :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, middle, finalState :
      SystemState name key value world error} ->
    {action : Action name key value world error} ->
    {head : Transition first middle} ->
    {rest : Transitions middle finalState} ->
    {localOccurrence : LocatedActionOccurrence action rest} ->
    (0 prefixedOccurrence : LocatedActionOccurrence action
      (MoreTransitions head rest)) ->
    (0 exactOrdinal : locatedActionOrdinal prefixedOccurrence =
      S (locatedActionOrdinal localOccurrence)) ->
    DeletionPrependedOccurrence name key world error value first middle finalState
      action head rest localOccurrence

0 deletionPrependLocalOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {action : Action name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (localOccurrence : LocatedActionOccurrence action rest) ->
  DeletionPrependedOccurrence name key world error value first middle finalState
    action head rest localOccurrence
deletionPrependLocalOccurrence head rest
  (MkLocatedActionOccurrence before afterState beforeTrace transition later
    actionShape decomposition) =
      MkDeletionPrependedOccurrence
        (MkLocatedActionOccurrence before afterState
          (MoreTransitions head beforeTrace) transition later actionShape
          (cong (MoreTransitions head) decomposition))
        Refl

mutual
  public export
  0 deletionLocatedAppendClassification :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, middle, finalState :
      SystemState name key value world error} ->
    {action : Action name key value world error} ->
    (before : Transitions first middle) ->
    (episode : Transitions middle finalState) ->
    (wholeOccurrence : LocatedActionOccurrence action
      (appendTransitions before episode)) ->
    DeletionLocatedAppendClassification name key world error value first middle
      finalState action before episode wholeOccurrence
  deletionLocatedAppendClassification NoTransitions episode wholeOccurrence =
    DeletionLocatedInRight wholeOccurrence Refl
  deletionLocatedAppendClassification (MoreTransitions head rest) episode
    wholeOccurrence =
      deletionLocatedAppendCons head rest episode wholeOccurrence
        (deletionLocatedHead action head (appendTransitions rest episode)
          wholeOccurrence)

  0 deletionLocatedAppendCons :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, middle, nextState, finalState :
      SystemState name key value world error} ->
    {action : Action name key value world error} ->
    (head : Transition first nextState) ->
    (rest : Transitions nextState middle) ->
    (episode : Transitions middle finalState) ->
    (wholeOccurrence : LocatedActionOccurrence action
      (MoreTransitions head (appendTransitions rest episode))) ->
    DeletionLocatedHeadView name key world error value first nextState finalState
      action head (appendTransitions rest episode) wholeOccurrence ->
    DeletionLocatedAppendClassification name key world error value first middle
      finalState action (MoreTransitions head rest) episode wholeOccurrence
  deletionLocatedAppendCons head rest episode wholeOccurrence
    (DeletionLocatedAtHead actionShape exactOrdinal) =
      DeletionLocatedInLeft
        (MkLocatedActionOccurrence _ _ NoTransitions head rest actionShape Refl)
        exactOrdinal
  deletionLocatedAppendCons head rest episode wholeOccurrence
    (DeletionLocatedInTail tailOccurrence exactOrdinal) =
      deletionLocatedAppendLift head rest episode wholeOccurrence tailOccurrence
        exactOrdinal
        (deletionLocatedAppendClassification rest episode tailOccurrence)

  0 deletionLocatedAppendLift :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, middle, nextState, finalState :
      SystemState name key value world error} ->
    {action : Action name key value world error} ->
    (head : Transition first nextState) ->
    (rest : Transitions nextState middle) ->
    (episode : Transitions middle finalState) ->
    (wholeOccurrence : LocatedActionOccurrence action
      (MoreTransitions head (appendTransitions rest episode))) ->
    (tailOccurrence : LocatedActionOccurrence action
      (appendTransitions rest episode)) ->
    (0 wholeOrdinal : locatedActionOrdinal wholeOccurrence =
      S (locatedActionOrdinal tailOccurrence)) ->
    DeletionLocatedAppendClassification name key world error value nextState middle
      finalState action rest episode tailOccurrence ->
    DeletionLocatedAppendClassification name key world error value first middle
      finalState action (MoreTransitions head rest) episode wholeOccurrence
  deletionLocatedAppendLift head rest episode wholeOccurrence tailOccurrence
    wholeOrdinal (DeletionLocatedInLeft localOccurrence exactOrdinal) =
      deletionLocatedAppendLeftLift head rest episode wholeOccurrence tailOccurrence
        localOccurrence wholeOrdinal exactOrdinal
        (deletionPrependLocalOccurrence head rest localOccurrence)
  deletionLocatedAppendLift head rest episode wholeOccurrence tailOccurrence
    wholeOrdinal (DeletionLocatedInRight localOccurrence exactOrdinal) =
      DeletionLocatedInRight localOccurrence
        (trans wholeOrdinal (cong S exactOrdinal))

  0 deletionLocatedAppendLeftLift :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, middle, nextState, finalState :
      SystemState name key value world error} ->
    {action : Action name key value world error} ->
    (head : Transition first nextState) ->
    (rest : Transitions nextState middle) ->
    (episode : Transitions middle finalState) ->
    (wholeOccurrence : LocatedActionOccurrence action
      (MoreTransitions head (appendTransitions rest episode))) ->
    (tailOccurrence : LocatedActionOccurrence action
      (appendTransitions rest episode)) ->
    (localOccurrence : LocatedActionOccurrence action rest) ->
    (0 wholeOrdinal : locatedActionOrdinal wholeOccurrence =
      S (locatedActionOrdinal tailOccurrence)) ->
    (0 exactOrdinal : locatedActionOrdinal tailOccurrence =
      locatedActionOrdinal localOccurrence) ->
    DeletionPrependedOccurrence name key world error value first nextState middle
      action head rest localOccurrence ->
    DeletionLocatedAppendClassification name key world error value first middle
      finalState action (MoreTransitions head rest) episode wholeOccurrence
  deletionLocatedAppendLeftLift head rest episode wholeOccurrence tailOccurrence
    localOccurrence wholeOrdinal exactOrdinal
    (MkDeletionPrependedOccurrence prefixedOccurrence prefixedOrdinal) =
      DeletionLocatedInLeft prefixedOccurrence
        (trans wholeOrdinal
          (trans (cong S exactOrdinal) (sym prefixedOrdinal)))

||| Producer-owned three-segment occurrence view for the exact surviving-trace
||| association used by `survivingTrace`.
public export
data DeletionWholeTraceOccurrenceClassification :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (first, beforeEnd, episodeEnd, finalState :
    SystemState name key value world error) ->
  (action : Action name key value world error) ->
  (before : Transitions first beforeEnd) ->
  (episode : Transitions beforeEnd episodeEnd) ->
  (after : Transitions episodeEnd finalState) ->
  (wholeOccurrence : LocatedActionOccurrence action
    (appendTransitions before (appendTransitions episode after))) -> Type where
  DeletionWholeBefore :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, beforeEnd, episodeEnd, finalState :
      SystemState name key value world error} ->
    {action : Action name key value world error} ->
    {before : Transitions first beforeEnd} ->
    {episode : Transitions beforeEnd episodeEnd} ->
    {after : Transitions episodeEnd finalState} ->
    {wholeOccurrence : LocatedActionOccurrence action
      (appendTransitions before (appendTransitions episode after))} ->
    (0 localOccurrence : LocatedActionOccurrence action before) ->
    (0 exactOrdinal : locatedActionOrdinal wholeOccurrence =
      locatedActionOrdinal localOccurrence) ->
    DeletionWholeTraceOccurrenceClassification name key world error value first
      beforeEnd episodeEnd finalState action before episode after
      wholeOccurrence
  DeletionWholeEpisode :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, beforeEnd, episodeEnd, finalState :
      SystemState name key value world error} ->
    {action : Action name key value world error} ->
    {before : Transitions first beforeEnd} ->
    {episode : Transitions beforeEnd episodeEnd} ->
    {after : Transitions episodeEnd finalState} ->
    {wholeOccurrence : LocatedActionOccurrence action
      (appendTransitions before (appendTransitions episode after))} ->
    (0 localOccurrence : LocatedActionOccurrence action episode) ->
    (0 exactOrdinal : locatedActionOrdinal wholeOccurrence =
      transitionCount before + locatedActionOrdinal localOccurrence) ->
    DeletionWholeTraceOccurrenceClassification name key world error value first
      beforeEnd episodeEnd finalState action before episode after
      wholeOccurrence
  DeletionWholeAfter :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, beforeEnd, episodeEnd, finalState :
      SystemState name key value world error} ->
    {action : Action name key value world error} ->
    {before : Transitions first beforeEnd} ->
    {episode : Transitions beforeEnd episodeEnd} ->
    {after : Transitions episodeEnd finalState} ->
    {wholeOccurrence : LocatedActionOccurrence action
      (appendTransitions before (appendTransitions episode after))} ->
    (0 localOccurrence : LocatedActionOccurrence action after) ->
    (0 exactOrdinal : locatedActionOrdinal wholeOccurrence =
      ((transitionCount before + transitionCount episode) +
        locatedActionOrdinal localOccurrence)) ->
    DeletionWholeTraceOccurrenceClassification name key world error value first
      beforeEnd episodeEnd finalState action before episode after
      wholeOccurrence

0 deletionWholeTraceRight :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, beforeEnd, episodeEnd, finalState :
    SystemState name key value world error} ->
  {action : Action name key value world error} ->
  (before : Transitions first beforeEnd) ->
  (episode : Transitions beforeEnd episodeEnd) ->
  (after : Transitions episodeEnd finalState) ->
  (wholeOccurrence : LocatedActionOccurrence action
    (appendTransitions before (appendTransitions episode after))) ->
  (tailOccurrence : LocatedActionOccurrence action
    (appendTransitions episode after)) ->
  (0 wholeOrdinal : locatedActionOrdinal wholeOccurrence =
    transitionCount before + locatedActionOrdinal tailOccurrence) ->
  DeletionLocatedAppendClassification name key world error value beforeEnd episodeEnd
    finalState action episode after tailOccurrence ->
  DeletionWholeTraceOccurrenceClassification name key world error value first
    beforeEnd episodeEnd finalState action before episode after wholeOccurrence
deletionWholeTraceRight before episode after wholeOccurrence tailOccurrence
  wholeOrdinal (DeletionLocatedInLeft localOccurrence exactOrdinal) =
    DeletionWholeEpisode localOccurrence
      (trans wholeOrdinal
        (cong ((+) (transitionCount before)) exactOrdinal))
deletionWholeTraceRight before episode after wholeOccurrence tailOccurrence
  wholeOrdinal (DeletionLocatedInRight localOccurrence exactOrdinal) =
    DeletionWholeAfter localOccurrence
      (trans wholeOrdinal
        (trans (cong ((+) (transitionCount before)) exactOrdinal)
          (plusAssociative (transitionCount before)
            (transitionCount episode)
            (locatedActionOrdinal localOccurrence))))

0 deletionWholeTraceFirst :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, beforeEnd, episodeEnd, finalState :
    SystemState name key value world error} ->
  {action : Action name key value world error} ->
  (before : Transitions first beforeEnd) ->
  (episode : Transitions beforeEnd episodeEnd) ->
  (after : Transitions episodeEnd finalState) ->
  (wholeOccurrence : LocatedActionOccurrence action
    (appendTransitions before (appendTransitions episode after))) ->
  DeletionLocatedAppendClassification name key world error value first beforeEnd
    finalState action before (appendTransitions episode after) wholeOccurrence ->
  DeletionWholeTraceOccurrenceClassification name key world error value first
    beforeEnd episodeEnd finalState action before episode after wholeOccurrence
deletionWholeTraceFirst before episode after wholeOccurrence
  (DeletionLocatedInLeft localOccurrence exactOrdinal) =
    DeletionWholeBefore localOccurrence exactOrdinal
deletionWholeTraceFirst before episode after wholeOccurrence
  (DeletionLocatedInRight tailOccurrence exactOrdinal) =
    deletionWholeTraceRight before episode after wholeOccurrence tailOccurrence
      exactOrdinal
      (deletionLocatedAppendClassification episode after tailOccurrence)

||| The complete surviving-trace recomposition.  It first eliminates the
||| before seam, then the episode seam in a separate top-level helper.
public export
0 deletionWholeTraceOccurrenceClassification :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, beforeEnd, episodeEnd, finalState :
    SystemState name key value world error} ->
  {action : Action name key value world error} ->
  (before : Transitions first beforeEnd) ->
  (episode : Transitions beforeEnd episodeEnd) ->
  (after : Transitions episodeEnd finalState) ->
  (wholeOccurrence : LocatedActionOccurrence action
    (appendTransitions before (appendTransitions episode after))) ->
  DeletionWholeTraceOccurrenceClassification name key world error value first
    beforeEnd episodeEnd finalState action before episode after wholeOccurrence
deletionWholeTraceOccurrenceClassification before episode after wholeOccurrence =
  deletionWholeTraceFirst before episode after wholeOccurrence
    (deletionLocatedAppendClassification before (appendTransitions episode after)
      wholeOccurrence)

||| Producer-owned RuleTag retention for one generation-aware deletion
||| subsequence.  A kept constructor binds the exact source/survivor tag
||| equation beside the same-action witness that `GenerationActionSubsequence`
||| already carries; deleted constructors merely thread the tail certificate.
public export
data GenerationSubsequenceRuleTagsPreserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {originalFirst, originalFinal, survivingFirst, survivingFinal :
    SystemState name key value world error} ->
  {nameEq : DecEq name} ->
  {deletable : Nat -> GenerationEnvironment name ->
    Action name key value world error -> Type} ->
  {ordinal : Nat} -> {live : GenerationEnvironment name} ->
  {original : Transitions originalFirst originalFinal} ->
  {surviving : Transitions survivingFirst survivingFinal} ->
  GenerationActionSubsequence nameEq deletable ordinal live original surviving ->
  Type where
  GenerationSubsequenceTagsEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {originalState, survivingState :
      SystemState name key value world error} ->
    {nameEq : DecEq name} ->
    {deletable : Nat -> GenerationEnvironment name ->
      Action name key value world error -> Type} ->
    {ordinal : Nat} -> {live : GenerationEnvironment name} ->
    GenerationSubsequenceRuleTagsPreserved
      {nameEq = nameEq} {deletable = deletable} {ordinal = ordinal}
      {live = live} {original = NoTransitions {state = originalState}}
      {surviving = NoTransitions {state = survivingState}}
      GenerationActionSubsequenceEnd
  GenerationSubsequenceTagsKeep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {originalFirst, originalMiddle, originalFinal,
      survivingFirst, survivingMiddle, survivingFinal :
      SystemState name key value world error} ->
    {nameEq : DecEq name} ->
    {deletable : Nat -> GenerationEnvironment name ->
      Action name key value world error -> Type} ->
    {ordinal : Nat} -> {live : GenerationEnvironment name} ->
    {originalTransition : Transition originalFirst originalMiddle} ->
    {originalRest : Transitions originalMiddle originalFinal} ->
    {survivingTransition : Transition survivingFirst survivingMiddle} ->
    {survivingRest : Transitions survivingMiddle survivingFinal} ->
    {kept : Not
      (deletable ordinal live (transitionAction originalTransition))} ->
    {sameAction : transitionAction originalTransition =
      transitionAction survivingTransition} ->
    {tail : GenerationActionSubsequence nameEq deletable (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction originalTransition) live)
      originalRest survivingRest} ->
    (0 sameTag : transitionTag originalTransition =
      transitionTag survivingTransition) ->
    (0 tailTags : GenerationSubsequenceRuleTagsPreserved tail) ->
    GenerationSubsequenceRuleTagsPreserved
      (KeepGenerationAction originalTransition originalRest survivingTransition
        survivingRest kept sameAction tail)
  GenerationSubsequenceTagsDelete :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {originalFirst, originalMiddle, originalFinal,
      survivingFirst, survivingFinal :
      SystemState name key value world error} ->
    {nameEq : DecEq name} ->
    {deletable : Nat -> GenerationEnvironment name ->
      Action name key value world error -> Type} ->
    {ordinal : Nat} -> {live : GenerationEnvironment name} ->
    {originalTransition : Transition originalFirst originalMiddle} ->
    {originalRest : Transitions originalMiddle originalFinal} ->
    {surviving : Transitions survivingFirst survivingFinal} ->
    {deleted : deletable ordinal live
      (transitionAction originalTransition)} ->
    {tail : GenerationActionSubsequence nameEq deletable (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction originalTransition) live)
      originalRest surviving} ->
    (0 tailTags : GenerationSubsequenceRuleTagsPreserved tail) ->
    GenerationSubsequenceRuleTagsPreserved
      (DeleteGenerationAction originalTransition originalRest deleted tail)

||| Exact source occurrence and source-ordinal equation for one generation-aware
||| subsequence.  The equation is emitted beside the producer-owned occurrence,
||| avoiding reduction through an opaque occurrence projection.
public export
record GenerationSubsequenceLocatedOrigin
  (name, key, world, error : Type) (value : key -> Type)
  {nameEq : DecEq name}
  {deletable : Nat -> GenerationEnvironment name ->
    Action name key value world error -> Type}
  {ordinal : Nat} {live : GenerationEnvironment name}
  {sourceFirst, sourceFinal, survivorFirst, survivorFinal :
    SystemState name key value world error}
  (source : Transitions sourceFirst sourceFinal)
  (survivor : Transitions survivorFirst survivorFinal)
  (subsequence : GenerationActionSubsequence nameEq deletable ordinal live
    source survivor)
  (action : Action name key value world error)
  (survivorOccurrence : LocatedActionOccurrence action survivor) where
  constructor MkGenerationSubsequenceLocatedOrigin
  segmentSourceOccurrence : LocatedActionOccurrence action source
  0 segmentSourceOrdinalExact :
    generationSubsequenceSourceOrdinal subsequence
      (locatedActionOrdinal survivorOccurrence) =
    Just (locatedActionOrdinal segmentSourceOccurrence)

0 deletionLocatedOccurrenceInEmptyImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {state : SystemState name key value world error} ->
  {action : Action name key value world error} ->
  LocatedActionOccurrence action (NoTransitions {state = state}) -> Void
deletionLocatedOccurrenceInEmptyImpossible
  (MkLocatedActionOccurrence before afterState beforeTrace transition later
    actionShape decomposition) =
      case beforeTrace of
        NoTransitions => case decomposition of Refl impossible
        MoreTransitions prefixHead prefixRest =>
          case decomposition of Refl impossible

mutual
  0 generationSubsequenceLocatedOriginExact :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} ->
    {deletable : Nat -> GenerationEnvironment name ->
      Action name key value world error -> Type} ->
    {ordinal : Nat} -> {live : GenerationEnvironment name} ->
    {sourceFirst, sourceFinal, survivorFirst, survivorFinal :
      SystemState name key value world error} ->
    {source : Transitions sourceFirst sourceFinal} ->
    {survivor : Transitions survivorFirst survivorFinal} ->
    (subsequence : GenerationActionSubsequence nameEq deletable ordinal live
      source survivor) ->
    {action : Action name key value world error} ->
    (survivorOccurrence : LocatedActionOccurrence action survivor) ->
    GenerationSubsequenceLocatedOrigin name key world error value source survivor
      subsequence action survivorOccurrence
  generationSubsequenceLocatedOriginExact GenerationActionSubsequenceEnd
    survivorOccurrence =
      void (deletionLocatedOccurrenceInEmptyImpossible survivorOccurrence)
  generationSubsequenceLocatedOriginExact
    (KeepGenerationAction sourceHead sourceRest survivorHead survivorRest kept
      sameAction tail) survivorOccurrence =
        generationSubsequenceLocatedKeepView sourceHead sourceRest survivorHead
          survivorRest kept sameAction tail survivorOccurrence
          (deletionLocatedHead action survivorHead survivorRest
            survivorOccurrence)
  generationSubsequenceLocatedOriginExact
    (DeleteGenerationAction sourceHead sourceRest deleted tail)
    survivorOccurrence =
      generationSubsequenceLocatedDeleteTail sourceHead sourceRest deleted tail
        survivorOccurrence
        (generationSubsequenceLocatedOriginExact tail survivorOccurrence)

  0 generationSubsequenceLocatedKeepView :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} ->
    {deletable : Nat -> GenerationEnvironment name ->
      Action name key value world error -> Type} ->
    {ordinal : Nat} -> {live : GenerationEnvironment name} ->
    {sourceFirst, sourceMiddle, sourceFinal,
      survivorFirst, survivorMiddle, survivorFinal :
      SystemState name key value world error} ->
    (sourceHead : Transition sourceFirst sourceMiddle) ->
    (sourceRest : Transitions sourceMiddle sourceFinal) ->
    (survivorHead : Transition survivorFirst survivorMiddle) ->
    (survivorRest : Transitions survivorMiddle survivorFinal) ->
    {action : Action name key value world error} ->
    (0 kept : Not
      (deletable ordinal live (transitionAction sourceHead))) ->
    (0 sameAction : transitionAction sourceHead =
      transitionAction survivorHead) ->
    (tail : GenerationActionSubsequence nameEq deletable (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction sourceHead) live) sourceRest survivorRest) ->
    (survivorOccurrence : LocatedActionOccurrence action
      (MoreTransitions survivorHead survivorRest)) ->
    DeletionLocatedHeadView name key world error value survivorFirst
      survivorMiddle survivorFinal action survivorHead survivorRest
      survivorOccurrence ->
    GenerationSubsequenceLocatedOrigin name key world error value
      (MoreTransitions sourceHead sourceRest)
      (MoreTransitions survivorHead survivorRest)
      (KeepGenerationAction sourceHead sourceRest survivorHead survivorRest
        kept sameAction tail)
      action survivorOccurrence
  generationSubsequenceLocatedKeepView sourceHead sourceRest survivorHead
    survivorRest kept sameAction tail survivorOccurrence
    (DeletionLocatedAtHead actionShape exactOrdinal) =
      MkGenerationSubsequenceLocatedOrigin
        (MkLocatedActionOccurrence _ _ NoTransitions sourceHead sourceRest
          (trans sameAction actionShape) Refl)
        (rewrite exactOrdinal in Refl)
  generationSubsequenceLocatedKeepView sourceHead sourceRest survivorHead
    survivorRest kept sameAction tail survivorOccurrence
    (DeletionLocatedInTail tailOccurrence exactOrdinal) =
      generationSubsequenceLocatedKeepTail sourceHead sourceRest survivorHead
        survivorRest kept sameAction tail survivorOccurrence tailOccurrence
        exactOrdinal
        (generationSubsequenceLocatedOriginExact tail tailOccurrence)

  0 generationSubsequenceLocatedKeepTail :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} ->
    {deletable : Nat -> GenerationEnvironment name ->
      Action name key value world error -> Type} ->
    {ordinal : Nat} -> {live : GenerationEnvironment name} ->
    {sourceFirst, sourceMiddle, sourceFinal,
      survivorFirst, survivorMiddle, survivorFinal :
      SystemState name key value world error} ->
    (sourceHead : Transition sourceFirst sourceMiddle) ->
    (sourceRest : Transitions sourceMiddle sourceFinal) ->
    (survivorHead : Transition survivorFirst survivorMiddle) ->
    (survivorRest : Transitions survivorMiddle survivorFinal) ->
    {action : Action name key value world error} ->
    (0 kept : Not
      (deletable ordinal live (transitionAction sourceHead))) ->
    (0 sameAction : transitionAction sourceHead =
      transitionAction survivorHead) ->
    (tail : GenerationActionSubsequence nameEq deletable (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction sourceHead) live) sourceRest survivorRest) ->
    (survivorOccurrence : LocatedActionOccurrence action
      (MoreTransitions survivorHead survivorRest)) ->
    (tailOccurrence : LocatedActionOccurrence action survivorRest) ->
    (0 wholeOrdinal : locatedActionOrdinal survivorOccurrence =
      S (locatedActionOrdinal tailOccurrence)) ->
    GenerationSubsequenceLocatedOrigin name key world error value sourceRest
      survivorRest tail action tailOccurrence ->
    GenerationSubsequenceLocatedOrigin name key world error value
      (MoreTransitions sourceHead sourceRest)
      (MoreTransitions survivorHead survivorRest)
      (KeepGenerationAction sourceHead sourceRest survivorHead survivorRest
        kept sameAction tail)
      action survivorOccurrence
  generationSubsequenceLocatedKeepTail sourceHead sourceRest survivorHead
    survivorRest kept sameAction tail survivorOccurrence tailOccurrence wholeOrdinal
    (MkGenerationSubsequenceLocatedOrigin sourceOccurrence sourceOrdinal) =
      generationSubsequenceLocatedKeepPrefix sourceHead sourceRest survivorHead
        survivorRest kept sameAction tail survivorOccurrence tailOccurrence
        wholeOrdinal sourceOccurrence sourceOrdinal
        (deletionPrependLocalOccurrence sourceHead sourceRest sourceOccurrence)

  0 generationSubsequenceLocatedKeepPrefix :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} ->
    {deletable : Nat -> GenerationEnvironment name ->
      Action name key value world error -> Type} ->
    {ordinal : Nat} -> {live : GenerationEnvironment name} ->
    {sourceFirst, sourceMiddle, sourceFinal,
      survivorFirst, survivorMiddle, survivorFinal :
      SystemState name key value world error} ->
    (sourceHead : Transition sourceFirst sourceMiddle) ->
    (sourceRest : Transitions sourceMiddle sourceFinal) ->
    (survivorHead : Transition survivorFirst survivorMiddle) ->
    (survivorRest : Transitions survivorMiddle survivorFinal) ->
    {action : Action name key value world error} ->
    (0 kept : Not
      (deletable ordinal live (transitionAction sourceHead))) ->
    (0 sameAction : transitionAction sourceHead =
      transitionAction survivorHead) ->
    (tail : GenerationActionSubsequence nameEq deletable (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction sourceHead) live) sourceRest survivorRest) ->
    (survivorOccurrence : LocatedActionOccurrence action
      (MoreTransitions survivorHead survivorRest)) ->
    (tailOccurrence : LocatedActionOccurrence action survivorRest) ->
    (0 wholeOrdinal : locatedActionOrdinal survivorOccurrence =
      S (locatedActionOrdinal tailOccurrence)) ->
    (sourceOccurrence : LocatedActionOccurrence action sourceRest) ->
    (0 sourceOrdinal : generationSubsequenceSourceOrdinal tail
      (locatedActionOrdinal tailOccurrence) =
      Just (locatedActionOrdinal sourceOccurrence)) ->
    DeletionPrependedOccurrence name key world error value sourceFirst
      sourceMiddle sourceFinal action sourceHead sourceRest sourceOccurrence ->
    GenerationSubsequenceLocatedOrigin name key world error value
      (MoreTransitions sourceHead sourceRest)
      (MoreTransitions survivorHead survivorRest)
      (KeepGenerationAction sourceHead sourceRest survivorHead survivorRest
        kept sameAction tail)
      action survivorOccurrence
  generationSubsequenceLocatedKeepPrefix sourceHead sourceRest survivorHead
    survivorRest kept sameAction tail survivorOccurrence tailOccurrence wholeOrdinal
    sourceOccurrence sourceOrdinal
    (MkDeletionPrependedOccurrence prefixedOccurrence prefixedOrdinal) =
      MkGenerationSubsequenceLocatedOrigin prefixedOccurrence
        (rewrite wholeOrdinal in
          trans (cong (map S) sourceOrdinal)
            (cong Just (sym prefixedOrdinal)))

  0 generationSubsequenceLocatedDeleteTail :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} ->
    {deletable : Nat -> GenerationEnvironment name ->
      Action name key value world error -> Type} ->
    {ordinal : Nat} -> {live : GenerationEnvironment name} ->
    {sourceFirst, sourceMiddle, sourceFinal, survivorFirst, survivorFinal :
      SystemState name key value world error} ->
    (sourceHead : Transition sourceFirst sourceMiddle) ->
    (sourceRest : Transitions sourceMiddle sourceFinal) ->
    {survivor : Transitions survivorFirst survivorFinal} ->
    {action : Action name key value world error} ->
    (0 deleted : deletable ordinal live (transitionAction sourceHead)) ->
    (tail : GenerationActionSubsequence nameEq deletable (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction sourceHead) live) sourceRest survivor) ->
    (survivorOccurrence : LocatedActionOccurrence action survivor) ->
    GenerationSubsequenceLocatedOrigin name key world error value sourceRest
      survivor tail action survivorOccurrence ->
    GenerationSubsequenceLocatedOrigin name key world error value
      (MoreTransitions sourceHead sourceRest) survivor
      (DeleteGenerationAction sourceHead sourceRest deleted tail)
      action survivorOccurrence
  generationSubsequenceLocatedDeleteTail sourceHead sourceRest deleted tail
    survivorOccurrence
    (MkGenerationSubsequenceLocatedOrigin sourceOccurrence sourceOrdinal) =
      generationSubsequenceLocatedDeletePrefix sourceHead sourceRest deleted tail
        survivorOccurrence sourceOccurrence sourceOrdinal
        (deletionPrependLocalOccurrence sourceHead sourceRest sourceOccurrence)

  0 generationSubsequenceLocatedDeletePrefix :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} ->
    {deletable : Nat -> GenerationEnvironment name ->
      Action name key value world error -> Type} ->
    {ordinal : Nat} -> {live : GenerationEnvironment name} ->
    {sourceFirst, sourceMiddle, sourceFinal, survivorFirst, survivorFinal :
      SystemState name key value world error} ->
    (sourceHead : Transition sourceFirst sourceMiddle) ->
    (sourceRest : Transitions sourceMiddle sourceFinal) ->
    {survivor : Transitions survivorFirst survivorFinal} ->
    {action : Action name key value world error} ->
    (0 deleted : deletable ordinal live (transitionAction sourceHead)) ->
    (tail : GenerationActionSubsequence nameEq deletable (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction sourceHead) live) sourceRest survivor) ->
    (survivorOccurrence : LocatedActionOccurrence action survivor) ->
    (sourceOccurrence : LocatedActionOccurrence action sourceRest) ->
    (0 sourceOrdinal : generationSubsequenceSourceOrdinal tail
      (locatedActionOrdinal survivorOccurrence) =
      Just (locatedActionOrdinal sourceOccurrence)) ->
    DeletionPrependedOccurrence name key world error value sourceFirst
      sourceMiddle sourceFinal action sourceHead sourceRest sourceOccurrence ->
    GenerationSubsequenceLocatedOrigin name key world error value
      (MoreTransitions sourceHead sourceRest) survivor
      (DeleteGenerationAction sourceHead sourceRest deleted tail)
      action survivorOccurrence
  generationSubsequenceLocatedDeletePrefix sourceHead sourceRest deleted tail
    survivorOccurrence sourceOccurrence sourceOrdinal
    (MkDeletionPrependedOccurrence prefixedOccurrence prefixedOrdinal) =
      MkGenerationSubsequenceLocatedOrigin prefixedOccurrence
        (trans (cong (map S) sourceOrdinal)
          (cong Just (sym prefixedOrdinal)))

||| One source occurrence embedded directly in the original global trace at an
||| explicit ordinal.  The package keeps the ordinal equation constructor-owned
||| across the final trace-equality transport.
record DeletionSourceOccurrenceAtOrdinal
  (name, key, world, error : Type) (value : key -> Type)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState)
  (action : Action name key value world error)
  (expectedOrdinal : Nat) where
  constructor MkDeletionSourceOccurrenceAtOrdinal
  deletionSourceOccurrence : LocatedActionOccurrence action trace
  0 deletionSourceOccurrenceOrdinal :
    locatedActionOrdinal deletionSourceOccurrence = expectedOrdinal

0 deletionTransitionCountAppend :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  (transitionCount (appendTransitions left right) =
    (transitionCount left + transitionCount right))
deletionTransitionCountAppend NoTransitions right = Refl
deletionTransitionCountAppend (MoreTransitions transition rest) right =
  cong S (deletionTransitionCountAppend rest right)

0 deletionEmbedBeforeSourceOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {initial, finalState : SystemState name key value world error} ->
  {trace : Transitions initial finalState} ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected trace) ->
  {action : Action name key value world error} ->
  (localOccurrence : LocatedActionOccurrence action
    (traceBeforeOpening episode)) ->
  DeletionSourceOccurrenceAtOrdinal name key world error value trace action
    (locatedActionOrdinal localOccurrence)
deletionEmbedBeforeSourceOccurrence episode
  (MkLocatedActionOccurrence before afterState beforeTrace transition later
    actionShape decomposition) =
      MkDeletionSourceOccurrenceAtOrdinal
        (MkLocatedActionOccurrence before afterState beforeTrace transition
          (appendTransitions later
            (appendTransitions
              (MoreTransitions
                (beginTransition (closedOpening (locatedEpisode episode)))
                (closedTransitions (locatedEpisode episode)))
              (traceAfterClosing episode)))
          actionShape
          (trans
            (sym (appendTransitionsAssociative beforeTrace
              (MoreTransitions transition later)
              (appendTransitions
                (MoreTransitions
                  (beginTransition (closedOpening (locatedEpisode episode)))
                  (closedTransitions (locatedEpisode episode)))
                (traceAfterClosing episode))))
            (trans
              (cong
                (\candidate => appendTransitions candidate
                  (appendTransitions
                    (MoreTransitions
                      (beginTransition
                        (closedOpening (locatedEpisode episode)))
                      (closedTransitions (locatedEpisode episode)))
                    (traceAfterClosing episode)))
                decomposition)
              (locatedDecomposition episode))))
        Refl

0 deletionEmbedEpisodeSourceOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {initial, finalState : SystemState name key value world error} ->
  {trace : Transitions initial finalState} ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected trace) ->
  {action : Action name key value world error} ->
  (localOccurrence : LocatedActionOccurrence action
    (MoreTransitions
      (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode)))) ->
  DeletionSourceOccurrenceAtOrdinal name key world error value trace action
    ((transitionCount (traceBeforeOpening episode)) +
      (locatedActionOrdinal localOccurrence))
deletionEmbedEpisodeSourceOccurrence episode
  (MkLocatedActionOccurrence before afterState beforeTrace transition later
    actionShape decomposition) =
      MkDeletionSourceOccurrenceAtOrdinal
        (MkLocatedActionOccurrence before afterState
          (appendTransitions (traceBeforeOpening episode) beforeTrace)
          transition (appendTransitions later (traceAfterClosing episode))
          actionShape
          (trans
            (appendTransitionsAssociative (traceBeforeOpening episode)
              beforeTrace
              (MoreTransitions transition
                (appendTransitions later (traceAfterClosing episode))))
            (trans
              (cong (appendTransitions (traceBeforeOpening episode))
                (trans
                  (sym (appendTransitionsAssociative beforeTrace
                    (MoreTransitions transition later)
                    (traceAfterClosing episode)))
                  (cong
                    (\candidate => appendTransitions candidate
                      (traceAfterClosing episode))
                    decomposition)))
              (locatedDecomposition episode))))
        (deletionTransitionCountAppend (traceBeforeOpening episode)
          beforeTrace)

0 deletionEmbedAfterSourceOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {initial, finalState : SystemState name key value world error} ->
  {trace : Transitions initial finalState} ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected trace) ->
  {action : Action name key value world error} ->
  (localOccurrence : LocatedActionOccurrence action
    (traceAfterClosing episode)) ->
  DeletionSourceOccurrenceAtOrdinal name key world error value trace action
    (((transitionCount (traceBeforeOpening episode)) +
      (transitionCount
        (MoreTransitions
          (beginTransition (closedOpening (locatedEpisode episode)))
          (closedTransitions (locatedEpisode episode))))) +
      (locatedActionOrdinal localOccurrence))
deletionEmbedAfterSourceOccurrence episode
  (MkLocatedActionOccurrence before afterState beforeTrace transition later
    actionShape decomposition) =
      MkDeletionSourceOccurrenceAtOrdinal
        (MkLocatedActionOccurrence before afterState
          (appendTransitions
            (appendTransitions (traceBeforeOpening episode)
              (MoreTransitions
                (beginTransition (closedOpening (locatedEpisode episode)))
                (closedTransitions (locatedEpisode episode))))
            beforeTrace)
          transition later actionShape
          (trans
            (appendTransitionsAssociative
              (appendTransitions (traceBeforeOpening episode)
                (MoreTransitions
                  (beginTransition (closedOpening (locatedEpisode episode)))
                  (closedTransitions (locatedEpisode episode))))
              beforeTrace (MoreTransitions transition later))
            (trans
              (cong
                (appendTransitions
                  (appendTransitions (traceBeforeOpening episode)
                    (MoreTransitions
                      (beginTransition
                        (closedOpening (locatedEpisode episode)))
                      (closedTransitions (locatedEpisode episode)))))
                decomposition)
              (trans
                (appendTransitionsAssociative (traceBeforeOpening episode)
                  (MoreTransitions
                    (beginTransition (closedOpening (locatedEpisode episode)))
                    (closedTransitions (locatedEpisode episode)))
                  (traceAfterClosing episode))
                (locatedDecomposition episode)))))
        (trans
          (deletionTransitionCountAppend
            (appendTransitions (traceBeforeOpening episode)
              (MoreTransitions
                (beginTransition (closedOpening (locatedEpisode episode)))
                (closedTransitions (locatedEpisode episode))))
            beforeTrace)
          (cong
            (\count => count + transitionCount beforeTrace)
            (deletionTransitionCountAppend (traceBeforeOpening episode)
              (MoreTransitions
                (beginTransition (closedOpening (locatedEpisode episode)))
                (closedTransitions (locatedEpisode episode))))))

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

||| The final gluing package correlates the chosen global source occurrence with
||| the exact before/episode/after ordinal constructor consumed by O9.
public export
record DeletionWholeOccurrenceOrigin
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (selected : name)
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected original)
  (registered : List (RegistrationGeneration name))
  (episodeStartOrdinal : Nat)
  (episodeStartLive : GenerationEnvironment name)
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered episodeStartOrdinal episodeStartLive)
  (action : Action name key value world error)
  (survivingOccurrence : LocatedActionOccurrence action
    (survivingTrace result)) where
  constructor MkDeletionWholeOccurrenceOrigin
  deletionWholeSourceOccurrence : LocatedActionOccurrence action original
  0 deletionWholeOrdinalEmbedding : DeletionSurvivingOrdinalEmbedding result
    (locatedActionOrdinal survivingOccurrence)
    (locatedActionOrdinal deletionWholeSourceOccurrence)

mutual
  0 deletionWholeOccurrenceOriginFromClassification :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) -> (keyEq : DecEq key) ->
    {initial, originalFinal : SystemState name key value world error} ->
    (original : Transitions initial originalFinal) ->
    (selected : name) ->
    (episode : LocatedClosedEpisode name key world error value nameEq keyEq
      selected original) ->
    (registered : List (RegistrationGeneration name)) ->
    (episodeStartOrdinal : Nat) ->
    (episodeStartLive : GenerationEnvironment name) ->
    (result : DeletionResult name key world error value nameEq keyEq original
      selected episode registered episodeStartOrdinal episodeStartLive) ->
    {action : Action name key value world error} ->
    (survivingOccurrence : LocatedActionOccurrence action
      (survivingTrace result)) ->
    DeletionWholeTraceOccurrenceClassification name key world error value initial
      (survivingBeforeEnd result) (survivingEpisodeEnd result)
      (survivingFinal result) action (survivingBefore result)
      (survivingEpisode result) (survivingAfter result) survivingOccurrence ->
    DeletionWholeOccurrenceOrigin name key world error value nameEq keyEq
      original selected episode registered episodeStartOrdinal episodeStartLive
      result action survivingOccurrence
  deletionWholeOccurrenceOriginFromClassification nameEq keyEq original selected
    episode registered episodeStartOrdinal episodeStartLive result
    survivingOccurrence (DeletionWholeBefore localOccurrence exactOrdinal) =
      deletionWholeBeforeOrigin nameEq keyEq original selected episode registered
        episodeStartOrdinal episodeStartLive result survivingOccurrence
        localOccurrence exactOrdinal
        (generationSubsequenceLocatedOriginExact (beforeDeletion result)
          localOccurrence)
  deletionWholeOccurrenceOriginFromClassification nameEq keyEq original selected
    episode registered episodeStartOrdinal episodeStartLive result
    survivingOccurrence (DeletionWholeEpisode localOccurrence exactOrdinal) =
      deletionWholeEpisodeOrigin nameEq keyEq original selected episode registered
        episodeStartOrdinal episodeStartLive result survivingOccurrence
        localOccurrence exactOrdinal
        (generationSubsequenceLocatedOriginExact (episodeDeletion result)
          localOccurrence)
  deletionWholeOccurrenceOriginFromClassification nameEq keyEq original selected
    episode registered episodeStartOrdinal episodeStartLive result
    survivingOccurrence (DeletionWholeAfter localOccurrence exactOrdinal) =
      deletionWholeAfterOrigin nameEq keyEq original selected episode registered
        episodeStartOrdinal episodeStartLive result survivingOccurrence
        localOccurrence exactOrdinal
        (generationSubsequenceLocatedOriginExact (afterDeletion result)
          localOccurrence)

  0 deletionWholeBeforeOrigin :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) -> (keyEq : DecEq key) ->
    {initial, originalFinal : SystemState name key value world error} ->
    (original : Transitions initial originalFinal) ->
    (selected : name) ->
    (episode : LocatedClosedEpisode name key world error value nameEq keyEq
      selected original) ->
    (registered : List (RegistrationGeneration name)) ->
    (episodeStartOrdinal : Nat) ->
    (episodeStartLive : GenerationEnvironment name) ->
    (result : DeletionResult name key world error value nameEq keyEq original
      selected episode registered episodeStartOrdinal episodeStartLive) ->
    {action : Action name key value world error} ->
    (survivingOccurrence : LocatedActionOccurrence action
      (survivingTrace result)) ->
    (localOccurrence : LocatedActionOccurrence action (survivingBefore result)) ->
    (0 exactOrdinal : locatedActionOrdinal survivingOccurrence =
      locatedActionOrdinal localOccurrence) ->
    GenerationSubsequenceLocatedOrigin name key world error value
      (traceBeforeOpening episode) (survivingBefore result)
      (beforeDeletion result) action localOccurrence ->
    DeletionWholeOccurrenceOrigin name key world error value nameEq keyEq
      original selected episode registered episodeStartOrdinal episodeStartLive
      result action survivingOccurrence
  deletionWholeBeforeOrigin nameEq keyEq original selected episode registered
    episodeStartOrdinal episodeStartLive result survivingOccurrence
    localOccurrence exactOrdinal
    (MkGenerationSubsequenceLocatedOrigin sourceOccurrence sourceOrdinal) =
      deletionWholeBeforeEmbedded nameEq keyEq original selected episode
        registered episodeStartOrdinal episodeStartLive result
        survivingOccurrence localOccurrence exactOrdinal sourceOccurrence
        sourceOrdinal
        (deletionEmbedBeforeSourceOccurrence episode sourceOccurrence)

  0 deletionWholeBeforeEmbedded :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) -> (keyEq : DecEq key) ->
    {initial, originalFinal : SystemState name key value world error} ->
    (original : Transitions initial originalFinal) ->
    (selected : name) ->
    (episode : LocatedClosedEpisode name key world error value nameEq keyEq
      selected original) ->
    (registered : List (RegistrationGeneration name)) ->
    (episodeStartOrdinal : Nat) ->
    (episodeStartLive : GenerationEnvironment name) ->
    (result : DeletionResult name key world error value nameEq keyEq original
      selected episode registered episodeStartOrdinal episodeStartLive) ->
    {action : Action name key value world error} ->
    (survivingOccurrence : LocatedActionOccurrence action
      (survivingTrace result)) ->
    (localOccurrence : LocatedActionOccurrence action (survivingBefore result)) ->
    (0 exactOrdinal : locatedActionOrdinal survivingOccurrence =
      locatedActionOrdinal localOccurrence) ->
    (sourceOccurrence : LocatedActionOccurrence action
      (traceBeforeOpening episode)) ->
    (0 sourceOrdinal : generationSubsequenceSourceOrdinal
      (beforeDeletion result) (locatedActionOrdinal localOccurrence) =
      Just (locatedActionOrdinal sourceOccurrence)) ->
    DeletionSourceOccurrenceAtOrdinal name key world error value original action
      (locatedActionOrdinal sourceOccurrence) ->
    DeletionWholeOccurrenceOrigin name key world error value nameEq keyEq
      original selected episode registered episodeStartOrdinal episodeStartLive
      result action survivingOccurrence
  deletionWholeBeforeEmbedded nameEq keyEq original selected episode registered
    episodeStartOrdinal episodeStartLive result survivingOccurrence
    localOccurrence exactOrdinal sourceOccurrence sourceOrdinal
    (MkDeletionSourceOccurrenceAtOrdinal globalSource globalOrdinal) =
      MkDeletionWholeOccurrenceOrigin globalSource
        (replace
          {p = \sourceIndex => DeletionSurvivingOrdinalEmbedding result
            (locatedActionOrdinal survivingOccurrence) sourceIndex}
          (sym globalOrdinal)
          (replace
            {p = \survivorIndex => DeletionSurvivingOrdinalEmbedding result
              survivorIndex (locatedActionOrdinal sourceOccurrence)}
            (sym exactOrdinal)
            (DeletionBeforeEmbedding sourceOrdinal)))

  0 deletionWholeEpisodeOrigin :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) -> (keyEq : DecEq key) ->
    {initial, originalFinal : SystemState name key value world error} ->
    (original : Transitions initial originalFinal) ->
    (selected : name) ->
    (episode : LocatedClosedEpisode name key world error value nameEq keyEq
      selected original) ->
    (registered : List (RegistrationGeneration name)) ->
    (episodeStartOrdinal : Nat) ->
    (episodeStartLive : GenerationEnvironment name) ->
    (result : DeletionResult name key world error value nameEq keyEq original
      selected episode registered episodeStartOrdinal episodeStartLive) ->
    {action : Action name key value world error} ->
    (survivingOccurrence : LocatedActionOccurrence action
      (survivingTrace result)) ->
    (localOccurrence : LocatedActionOccurrence action (survivingEpisode result)) ->
    (0 exactOrdinal : locatedActionOrdinal survivingOccurrence =
      ((transitionCount (survivingBefore result)) +
        (locatedActionOrdinal localOccurrence))) ->
    GenerationSubsequenceLocatedOrigin name key world error value
      (MoreTransitions
        (beginTransition (closedOpening (locatedEpisode episode)))
        (closedTransitions (locatedEpisode episode)))
      (survivingEpisode result) (episodeDeletion result) action localOccurrence ->
    DeletionWholeOccurrenceOrigin name key world error value nameEq keyEq
      original selected episode registered episodeStartOrdinal episodeStartLive
      result action survivingOccurrence
  deletionWholeEpisodeOrigin nameEq keyEq original selected episode registered
    episodeStartOrdinal episodeStartLive result survivingOccurrence
    localOccurrence exactOrdinal
    (MkGenerationSubsequenceLocatedOrigin sourceOccurrence sourceOrdinal) =
      deletionWholeEpisodeEmbedded nameEq keyEq original selected episode
        registered episodeStartOrdinal episodeStartLive result
        survivingOccurrence localOccurrence exactOrdinal sourceOccurrence
        sourceOrdinal
        (deletionEmbedEpisodeSourceOccurrence episode sourceOccurrence)

  0 deletionWholeEpisodeEmbedded :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) -> (keyEq : DecEq key) ->
    {initial, originalFinal : SystemState name key value world error} ->
    (original : Transitions initial originalFinal) ->
    (selected : name) ->
    (episode : LocatedClosedEpisode name key world error value nameEq keyEq
      selected original) ->
    (registered : List (RegistrationGeneration name)) ->
    (episodeStartOrdinal : Nat) ->
    (episodeStartLive : GenerationEnvironment name) ->
    (result : DeletionResult name key world error value nameEq keyEq original
      selected episode registered episodeStartOrdinal episodeStartLive) ->
    {action : Action name key value world error} ->
    (survivingOccurrence : LocatedActionOccurrence action
      (survivingTrace result)) ->
    (localOccurrence : LocatedActionOccurrence action (survivingEpisode result)) ->
    (0 exactOrdinal : locatedActionOrdinal survivingOccurrence =
      ((transitionCount (survivingBefore result)) +
        (locatedActionOrdinal localOccurrence))) ->
    (sourceOccurrence : LocatedActionOccurrence action
      (MoreTransitions
        (beginTransition (closedOpening (locatedEpisode episode)))
        (closedTransitions (locatedEpisode episode)))) ->
    (0 sourceOrdinal : generationSubsequenceSourceOrdinal
      (episodeDeletion result) (locatedActionOrdinal localOccurrence) =
      Just (locatedActionOrdinal sourceOccurrence)) ->
    DeletionSourceOccurrenceAtOrdinal name key world error value original action
      ((transitionCount (traceBeforeOpening episode)) +
        (locatedActionOrdinal sourceOccurrence)) ->
    DeletionWholeOccurrenceOrigin name key world error value nameEq keyEq
      original selected episode registered episodeStartOrdinal episodeStartLive
      result action survivingOccurrence
  deletionWholeEpisodeEmbedded nameEq keyEq original selected episode registered
    episodeStartOrdinal episodeStartLive result survivingOccurrence
    localOccurrence exactOrdinal sourceOccurrence sourceOrdinal
    (MkDeletionSourceOccurrenceAtOrdinal globalSource globalOrdinal) =
      MkDeletionWholeOccurrenceOrigin globalSource
        (replace
          {p = \sourceIndex => DeletionSurvivingOrdinalEmbedding result
            (locatedActionOrdinal survivingOccurrence) sourceIndex}
          (sym globalOrdinal)
          (replace
            {p = \survivorIndex => DeletionSurvivingOrdinalEmbedding result
              survivorIndex
              ((transitionCount (traceBeforeOpening episode)) +
                (locatedActionOrdinal sourceOccurrence))}
            (sym exactOrdinal)
            (DeletionEpisodeEmbedding sourceOrdinal)))

  0 deletionWholeAfterOrigin :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) -> (keyEq : DecEq key) ->
    {initial, originalFinal : SystemState name key value world error} ->
    (original : Transitions initial originalFinal) ->
    (selected : name) ->
    (episode : LocatedClosedEpisode name key world error value nameEq keyEq
      selected original) ->
    (registered : List (RegistrationGeneration name)) ->
    (episodeStartOrdinal : Nat) ->
    (episodeStartLive : GenerationEnvironment name) ->
    (result : DeletionResult name key world error value nameEq keyEq original
      selected episode registered episodeStartOrdinal episodeStartLive) ->
    {action : Action name key value world error} ->
    (survivingOccurrence : LocatedActionOccurrence action
      (survivingTrace result)) ->
    (localOccurrence : LocatedActionOccurrence action (survivingAfter result)) ->
    (0 exactOrdinal : locatedActionOrdinal survivingOccurrence =
      (((transitionCount (survivingBefore result)) +
        (transitionCount (survivingEpisode result))) +
        (locatedActionOrdinal localOccurrence))) ->
    GenerationSubsequenceLocatedOrigin name key world error value
      (traceAfterClosing episode) (survivingAfter result)
      (afterDeletion result) action localOccurrence ->
    DeletionWholeOccurrenceOrigin name key world error value nameEq keyEq
      original selected episode registered episodeStartOrdinal episodeStartLive
      result action survivingOccurrence
  deletionWholeAfterOrigin nameEq keyEq original selected episode registered
    episodeStartOrdinal episodeStartLive result survivingOccurrence
    localOccurrence exactOrdinal
    (MkGenerationSubsequenceLocatedOrigin sourceOccurrence sourceOrdinal) =
      deletionWholeAfterEmbedded nameEq keyEq original selected episode registered
        episodeStartOrdinal episodeStartLive result survivingOccurrence
        localOccurrence exactOrdinal sourceOccurrence sourceOrdinal
        (deletionEmbedAfterSourceOccurrence episode sourceOccurrence)

  0 deletionWholeAfterEmbedded :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) -> (keyEq : DecEq key) ->
    {initial, originalFinal : SystemState name key value world error} ->
    (original : Transitions initial originalFinal) ->
    (selected : name) ->
    (episode : LocatedClosedEpisode name key world error value nameEq keyEq
      selected original) ->
    (registered : List (RegistrationGeneration name)) ->
    (episodeStartOrdinal : Nat) ->
    (episodeStartLive : GenerationEnvironment name) ->
    (result : DeletionResult name key world error value nameEq keyEq original
      selected episode registered episodeStartOrdinal episodeStartLive) ->
    {action : Action name key value world error} ->
    (survivingOccurrence : LocatedActionOccurrence action
      (survivingTrace result)) ->
    (localOccurrence : LocatedActionOccurrence action (survivingAfter result)) ->
    (0 exactOrdinal : locatedActionOrdinal survivingOccurrence =
      (((transitionCount (survivingBefore result)) +
        (transitionCount (survivingEpisode result))) +
        (locatedActionOrdinal localOccurrence))) ->
    (sourceOccurrence : LocatedActionOccurrence action
      (traceAfterClosing episode)) ->
    (0 sourceOrdinal : generationSubsequenceSourceOrdinal
      (afterDeletion result) (locatedActionOrdinal localOccurrence) =
      Just (locatedActionOrdinal sourceOccurrence)) ->
    DeletionSourceOccurrenceAtOrdinal name key world error value original action
      (((transitionCount (traceBeforeOpening episode)) +
        (transitionCount
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode episode)))
            (closedTransitions (locatedEpisode episode))))) +
        (locatedActionOrdinal sourceOccurrence)) ->
    DeletionWholeOccurrenceOrigin name key world error value nameEq keyEq
      original selected episode registered episodeStartOrdinal episodeStartLive
      result action survivingOccurrence
  deletionWholeAfterEmbedded nameEq keyEq original selected episode registered
    episodeStartOrdinal episodeStartLive result survivingOccurrence
    localOccurrence exactOrdinal sourceOccurrence sourceOrdinal
    (MkDeletionSourceOccurrenceAtOrdinal globalSource globalOrdinal) =
      MkDeletionWholeOccurrenceOrigin globalSource
        (replace
          {p = \sourceIndex => DeletionSurvivingOrdinalEmbedding result
            (locatedActionOrdinal survivingOccurrence) sourceIndex}
          (sym globalOrdinal)
          (replace
            {p = \survivorIndex => DeletionSurvivingOrdinalEmbedding result
              survivorIndex
              (((transitionCount (traceBeforeOpening episode)) +
                (transitionCount
                  (MoreTransitions
                    (beginTransition
                      (closedOpening (locatedEpisode episode)))
                    (closedTransitions (locatedEpisode episode))))) +
                (locatedActionOrdinal sourceOccurrence))}
            (sym exactOrdinal)
            (DeletionAfterEmbedding sourceOrdinal)))

||| Final three-way source-occurrence gluing lemma.
public export
0 deletionWholeOccurrenceOrigin :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected original) ->
  (registered : List (RegistrationGeneration name)) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered episodeStartOrdinal episodeStartLive) ->
  {action : Action name key value world error} ->
  (survivingOccurrence : LocatedActionOccurrence action
    (survivingTrace result)) ->
  DeletionWholeOccurrenceOrigin name key world error value nameEq keyEq original
    selected episode registered episodeStartOrdinal episodeStartLive result action
    survivingOccurrence
deletionWholeOccurrenceOrigin nameEq keyEq original selected episode registered
  episodeStartOrdinal episodeStartLive result survivingOccurrence =
    deletionWholeOccurrenceOriginFromClassification nameEq keyEq original
      selected episode registered episodeStartOrdinal episodeStartLive result
      survivingOccurrence
      (deletionWholeTraceOccurrenceClassification (survivingBefore result)
        (survivingEpisode result) (survivingAfter result) survivingOccurrence)

||| Convert the all-action occurrence selected by the deletion source producer
||| into the specialized generated-registration occurrence used by the global
||| registration-generation law.
0 deletionActionOccurrenceToGenerated :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, finalState : SystemState name key value world error} ->
  {trace : Transitions initial finalState} ->
  {child, parent : name} ->
  {component : Component key value world error} ->
  LocatedActionOccurrence (OInsert child (ChildOf parent) component) trace ->
  LocatedGeneratedRegistration child parent component trace
deletionActionOccurrenceToGenerated
  (MkLocatedActionOccurrence before afterState beforeTrace transition later
    actionShape decomposition) =
      MkLocatedGeneratedRegistration before afterState beforeTrace transition
        later actionShape decomposition

0 deletionActionOccurrenceToGeneratedCoherent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, finalState : SystemState name key value world error} ->
  {trace : Transitions initial finalState} ->
  {child, parent : name} ->
  {component : Component key value world error} ->
  (occurrence : LocatedActionOccurrence
    (OInsert child (ChildOf parent) component) trace) ->
  generatedRegistrationActionOccurrence
      (deletionActionOccurrenceToGenerated occurrence) = occurrence
deletionActionOccurrenceToGeneratedCoherent
  (MkLocatedActionOccurrence before afterState beforeTrace transition later
    actionShape decomposition) = Refl

||| Research-side exact-equation capital emitted together with one concrete
||| deletion result.  The public CP3 `DeletionResult` deliberately remains
||| frozen; this package retains the three concrete CP4 readiness derivations,
||| constructor-by-constructor kept-tag equations, and the one global finite
||| generation permutation required by the operational occurrence consumer.
public export
record DeletionProducerOperationalCapital
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
  constructor MkDeletionProducerOperationalCapital
  0 deletionBeforeReplayReady : GenerationReplayReady nameEq keyEq
    (GenerationOwnedActor nameEq registered) 0 []
    (traceBeforeOpening episode) initial
  0 deletionBeforeReplayEnds : ReplayReadyEndsAt deletionBeforeReplayReady
    (survivingBeforeEnd result)
  0 deletionEpisodeReplayReady : GenerationReplayReady nameEq keyEq
    (EpisodeGenerationDeletedActor nameEq selected registered)
    episodeStartOrdinal episodeStartLive
    (MoreTransitions
      (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode)))
    (survivingBeforeEnd result)
  0 deletionEpisodeReplayEnds : ReplayReadyEndsAt deletionEpisodeReplayReady
    (survivingEpisodeEnd result)
  0 deletionAfterReplayReady : GenerationReplayReady nameEq keyEq
    (GenerationOwnedActor nameEq registered)
    (episodeEndOrdinal result) (episodeEndLive result)
    (traceAfterClosing episode) (survivingEpisodeEnd result)
  0 deletionAfterReplayEnds : ReplayReadyEndsAt deletionAfterReplayReady
    (survivingFinal result)
  0 deletionBeforeTagsPreserved : GenerationSubsequenceRuleTagsPreserved
    (beforeDeletion result)
  0 deletionEpisodeTagsPreserved : GenerationSubsequenceRuleTagsPreserved
    (episodeDeletion result)
  0 deletionAfterTagsPreserved : GenerationSubsequenceRuleTagsPreserved
    (afterDeletion result)
  deletionProducerGenerationRenaming : RegistrationGenerationBijection name
  0 deletionProducerWholeTagPreserved :
    {action : Action name key value world error} ->
    (occurrence : LocatedActionOccurrence action (survivingTrace result)) ->
    transitionTag
      (locatedTransition
        (deletionWholeSourceOccurrence
          (deletionWholeOccurrenceOrigin nameEq keyEq original selected episode
            registered episodeStartOrdinal episodeStartLive result occurrence))) =
      transitionTag (locatedTransition occurrence)
  0 deletionProducerGeneratedOrdinalPreserved :
    {child, parent : name} ->
    {component : Component key value world error} ->
    (occurrence : LocatedGeneratedRegistration child parent component
      (survivingTrace result)) ->
    generationForward deletionProducerGenerationRenaming
      (registrationGeneration
        (deletionActionOccurrenceToGenerated
          (deletionWholeSourceOccurrence
            (deletionWholeOccurrenceOrigin nameEq keyEq original selected episode
              registered episodeStartOrdinal episodeStartLive result
              (generatedRegistrationActionOccurrence occurrence))))) =
      registrationGeneration occurrence

0 deletionProducerActionOrigin :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq selected
    original) ->
  (registered : List (RegistrationGeneration name)) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered episodeStartOrdinal episodeStartLive) ->
  (capital : DeletionProducerOperationalCapital name key world error value nameEq
    keyEq original selected episode registered episodeStartOrdinal
    episodeStartLive result) ->
  {action : Action name key value world error} ->
  LocatedActionOccurrence action (survivingTrace result) ->
  LocatedActionOccurrence action original
deletionProducerActionOrigin nameEq keyEq original selected episode registered
  episodeStartOrdinal episodeStartLive result capital occurrence =
    deletionWholeSourceOccurrence
      (deletionWholeOccurrenceOrigin nameEq keyEq original selected episode
        registered episodeStartOrdinal episodeStartLive result occurrence)

0 deletionProducerGeneratedOrigin :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq selected
    original) ->
  (registered : List (RegistrationGeneration name)) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered episodeStartOrdinal episodeStartLive) ->
  (capital : DeletionProducerOperationalCapital name key world error value nameEq
    keyEq original selected episode registered episodeStartOrdinal
    episodeStartLive result) ->
  {child, parent : name} ->
  {component : Component key value world error} ->
  LocatedGeneratedRegistration child parent component (survivingTrace result) ->
  LocatedGeneratedRegistration child parent component original
deletionProducerGeneratedOrigin nameEq keyEq original selected episode registered
  episodeStartOrdinal episodeStartLive result capital occurrence =
    deletionActionOccurrenceToGenerated
      (deletionProducerActionOrigin nameEq keyEq original selected episode
        registered episodeStartOrdinal episodeStartLive result capital
        (generatedRegistrationActionOccurrence occurrence))

0 deletionProducerGeneratedOriginCoherent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq selected
    original) ->
  (registered : List (RegistrationGeneration name)) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered episodeStartOrdinal episodeStartLive) ->
  (capital : DeletionProducerOperationalCapital name key world error value nameEq
    keyEq original selected episode registered episodeStartOrdinal
    episodeStartLive result) ->
  {child, parent : name} ->
  {component : Component key value world error} ->
  (occurrence : LocatedGeneratedRegistration child parent component
    (survivingTrace result)) ->
  generatedRegistrationActionOccurrence
      (deletionProducerGeneratedOrigin nameEq keyEq original selected episode
        registered episodeStartOrdinal episodeStartLive result capital
        occurrence) =
    deletionProducerActionOrigin nameEq keyEq original selected episode
      registered episodeStartOrdinal episodeStartLive result capital
      (generatedRegistrationActionOccurrence occurrence)
deletionProducerGeneratedOriginCoherent nameEq keyEq original selected episode
  registered episodeStartOrdinal episodeStartLive result capital occurrence =
    deletionActionOccurrenceToGeneratedCoherent
      (deletionProducerActionOrigin nameEq keyEq original selected episode
        registered episodeStartOrdinal episodeStartLive result capital
        (generatedRegistrationActionOccurrence occurrence))

0 deletionProducerOccurrenceEmbedding :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq selected
    original) ->
  (registered : List (RegistrationGeneration name)) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered episodeStartOrdinal episodeStartLive) ->
  (capital : DeletionProducerOperationalCapital name key world error value nameEq
    keyEq original selected episode registered episodeStartOrdinal
    episodeStartLive result) ->
  {action : Action name key value world error} ->
  (occurrence : LocatedActionOccurrence action (survivingTrace result)) ->
  DeletionSurvivingOrdinalEmbedding result (locatedActionOrdinal occurrence)
    (locatedActionOrdinal
      (deletionProducerActionOrigin nameEq keyEq original selected episode
        registered episodeStartOrdinal episodeStartLive result capital occurrence))
deletionProducerOccurrenceEmbedding nameEq keyEq original selected episode
  registered episodeStartOrdinal episodeStartLive result capital occurrence =
    deletionWholeOrdinalEmbedding
      (deletionWholeOccurrenceOrigin nameEq keyEq original selected episode
        registered episodeStartOrdinal episodeStartLive result occurrence)

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
  (capital : DeletionProducerOperationalCapital name key world error value nameEq
    keyEq trace (selectedActor candidate) (selectedEpisode candidate)
    (selectedRegistrations candidate) (selectedStartOrdinal candidate)
    (selectedStartLive candidate) result) ->
  DeletionOperationalOccurrenceCertificate name key world error value nameEq
    keyEq trace (selectedActor candidate) (selectedEpisode candidate)
    (selectedRegistrations candidate) (selectedStartOrdinal candidate)
    (selectedStartLive candidate) result
deletionStepOperationalOccurrenceFoldSpike nameEq keyEq protocol trace premises
  candidate result capital =
    MkDeletionOperationalOccurrenceCertificate
      (MkActionRegistrationReplayCorrespondence
        (deletionProducerGenerationRenaming capital)
        (deletionProducerActionOrigin nameEq keyEq trace
          (selectedActor candidate) (selectedEpisode candidate)
          (selectedRegistrations candidate) (selectedStartOrdinal candidate)
          (selectedStartLive candidate) result capital)
        (deletionProducerWholeTagPreserved capital)
        (deletionProducerGeneratedOrigin nameEq keyEq trace
          (selectedActor candidate) (selectedEpisode candidate)
          (selectedRegistrations candidate) (selectedStartOrdinal candidate)
          (selectedStartLive candidate) result capital)
        (deletionProducerGeneratedOriginCoherent nameEq keyEq trace
          (selectedActor candidate) (selectedEpisode candidate)
          (selectedRegistrations candidate) (selectedStartOrdinal candidate)
          (selectedStartLive candidate) result capital)
        (deletionProducerGeneratedOrdinalPreserved capital))
      (deletionProducerOccurrenceEmbedding nameEq keyEq trace
        (selectedActor candidate) (selectedEpisode candidate)
        (selectedRegistrations candidate) (selectedStartOrdinal candidate)
        (selectedStartLive candidate) result capital)

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
  deletionProducerCapital : DeletionProducerOperationalCapital name key world
    error value nameEq keyEq trace (selectedActor candidate)
    (selectedEpisode candidate) (selectedRegistrations candidate)
    (selectedStartOrdinal candidate) (selectedStartLive candidate) deletionResult
  deletionReplayCorrespondence : RelationalReplayCorrespondence name key world
    error value trace (survivingTrace deletionResult)
  deletionOccurrenceCorrespondence : ActionRegistrationReplayCorrespondence name
    key world error value trace (survivingTrace deletionResult)
  0 deletionOccurrenceCorrespondenceExact :
    deletionOccurrenceCorrespondence = deletionOperationalCorrespondence
      (deletionStepOperationalOccurrenceFoldSpike nameEq keyEq protocol trace
        premises candidate deletionResult deletionProducerCapital)
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
  ClosingFree :
    (0 closingFree : NoClosingEpisodes name key world error value nameEq keyEq
      trace) ->
    ClosingStepChoice name key world error value protocol nameEq keyEq trace
      premises
  HasClosingStep :
    (0 candidate : DeletableClosingEpisode name key world error value nameEq keyEq
      trace) ->
    (0 step : DeletionChainStep name key world error value protocol nameEq keyEq
      trace premises candidate) ->
    ClosingStepChoice name key world error value protocol nameEq keyEq trace
      premises

||| Fully erased inspection keeps the computed value and its exact equation in
||| one constructor, avoiding an uncorrelated inferred local view.
data ErasedInspection : (observed : item) -> Type where
  MkErasedInspection : {item : Type} -> {observed : item} ->
    (0 result : item) -> (0 exact : observed = result) ->
    ErasedInspection observed

0 inspectErased : (observed : item) -> ErasedInspection observed
inspectErased observed = MkErasedInspection observed Refl

||| Producer-owned exact lookup equation.  Endpoint consumers eliminate this
||| canonized family instead of independently re-running `lookupFiber`.
data ParentEndpointLookupEquation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) -> Type where
  ParentEndpointLookupMissing :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {state : SystemState name key value world error} ->
    (0 missing : lookupFiber @{nameEq} {key = key} {value = value}
      {world = world} {error = error} selected (registry state) = Nothing) ->
    (0 missingReloadingEndpoint :
      reloadingEndpoint @{nameEq} selected state = False) ->
    (0 missingActiveEndpoint :
      activeEndpoint @{nameEq} selected state = False) ->
    ParentEndpointLookupEquation name key world error value nameEq selected state
  ParentEndpointLookupFound :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {state : SystemState name key value world error} ->
    (0 fiber : Fiber name key value world error) ->
    (0 found : lookupFiber @{nameEq} {key = key} {value = value}
      {world = world} {error = error} selected (registry state) = Just fiber) ->
    (0 foundReloadingEndpoint : reloadingEndpoint @{nameEq} selected state =
      (case fiberLifecycle fiber of
        Reloading remaining accumulator dependencyView => True
        _ => False)) ->
    (0 foundActiveEndpoint : activeEndpoint @{nameEq} selected state =
      isActive (fiberLifecycle fiber)) ->
    ParentEndpointLookupEquation name key world error value nameEq selected state

0 parentEndpointLookupEquation :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  ParentEndpointLookupEquation name key world error value nameEq selected state
parentEndpointLookupEquation nameEq selected state =
  case inspectErased (lookupFiber @{nameEq} selected (registry state)) of
    MkErasedInspection Nothing exact =>
      ParentEndpointLookupMissing exact (rewrite exact in Refl)
        (rewrite exact in Refl)
    MkErasedInspection (Just fiber) exact =>
      ParentEndpointLookupFound fiber exact (rewrite exact in Refl)
        (rewrite exact in Refl)

||| Canonized producer-owned endpoint view.  Each constructor binds the exact
||| fiber lookup, lifecycle equation, and public endpoint equation together.
data ParentOpenEquationView :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) -> Type where
  ParentReloadingEndpointEquation :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {state : SystemState name key value world error} ->
    (0 fiber : Fiber name key value world error) ->
    (0 remaining : List (StepEffect key value world error
      (dependencies (componentDependencies (fiberComponent fiber)))
      (componentProvisions (fiberComponent fiber)))) ->
    (0 accumulator : LocalState key value world
        (componentProvisions (fiberComponent fiber)) ->
      LocalState key value world
        (componentProvisions (fiberComponent fiber))) ->
    (0 view : View name
      (dependencies (componentDependencies (fiberComponent fiber)))) ->
    (0 found : lookupFiber @{nameEq} {key = key} {value = value}
      {world = world} {error = error} selected (registry state) = Just fiber) ->
    (0 lifecycle : fiberLifecycle fiber =
      Reloading remaining accumulator view) ->
    (0 endpoint : reloadingEndpoint @{nameEq} selected state = True) ->
    ParentOpenEquationView name key world error value nameEq selected state
  ParentActiveEndpointEquation :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {state : SystemState name key value world error} ->
    (0 fiber : Fiber name key value world error) ->
    (0 accumulator : LocalState key value world
        (componentProvisions (fiberComponent fiber)) ->
      LocalState key value world
        (componentProvisions (fiberComponent fiber))) ->
    (0 view : View name
      (dependencies (componentDependencies (fiberComponent fiber)))) ->
    (0 found : lookupFiber @{nameEq} {key = key} {value = value}
      {world = world} {error = error} selected (registry state) = Just fiber) ->
    (0 lifecycle : fiberLifecycle fiber = Active accumulator view) ->
    (0 endpoint : activeEndpoint @{nameEq} selected state = True) ->
    ParentOpenEquationView name key world error value nameEq selected state

0 parentOpenFromEquationView :
  (view : ParentOpenEquationView name key world error value nameEq selected
    state) ->
  ParentOpenAt nameEq selected state
parentOpenFromEquationView
  (ParentReloadingEndpointEquation fiber remaining accumulator dependencyView
    found lifecycle endpoint) =
      MkParentOpenAt fiber found
        (replace {p = LifecycleOpen} (sym lifecycle) OpenReloading)
parentOpenFromEquationView
  (ParentActiveEndpointEquation fiber accumulator dependencyView found lifecycle
    endpoint) =
      MkParentOpenAt fiber found
        (replace {p = LifecycleOpen} (sym lifecycle) OpenActive)

0 reloadingLifecycleEquationView :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  (0 found : lookupFiber @{nameEq} selected (registry state) = Just fiber) ->
  (0 lifecycleTrue :
    (case fiberLifecycle fiber of
      Reloading remaining accumulator dependencyView => True
      _ => False) = True) ->
  (0 endpoint : reloadingEndpoint @{nameEq} selected state = True) ->
  ParentOpenEquationView name key world error value nameEq selected state
reloadingLifecycleEquationView nameEq selected state
  (MkFiber component parent retiredFlag table (Inactive outcome)) found
  lifecycleTrue endpoint = void (falseNotTrueO7 lifecycleTrue)
reloadingLifecycleEquationView nameEq selected state
  (MkFiber component parent retiredFlag table
    (Reloading remaining accumulator dependencyView)) found lifecycleTrue
  endpoint =
    ParentReloadingEndpointEquation
      (MkFiber component parent retiredFlag table
        (Reloading remaining accumulator dependencyView))
      remaining accumulator dependencyView found Refl endpoint
reloadingLifecycleEquationView nameEq selected state
  (MkFiber component parent retiredFlag table
    (Active accumulator dependencyView)) found lifecycleTrue endpoint =
      void (falseNotTrueO7 lifecycleTrue)
reloadingLifecycleEquationView nameEq selected state
  (MkFiber component parent retiredFlag table
    (Unloading accumulator dependencyView outcome)) found lifecycleTrue endpoint =
      void (falseNotTrueO7 lifecycleTrue)

0 reloadingEndpointEquationView :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  (0 endpoint : reloadingEndpoint @{nameEq} selected state = True) ->
  ParentOpenEquationView name key world error value nameEq selected state
reloadingEndpointEquationView nameEq selected state endpoint =
  case parentEndpointLookupEquation nameEq selected state of
    ParentEndpointLookupMissing missing missingReloading missingActive =>
      void (falseNotTrueO7 (trans (sym missingReloading) endpoint))
    ParentEndpointLookupFound fiber found foundReloading foundActive =>
      reloadingLifecycleEquationView nameEq selected state fiber found
        (trans (sym foundReloading) endpoint) endpoint

0 activeLifecycleEquationView :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  (0 found : lookupFiber @{nameEq} selected (registry state) = Just fiber) ->
  (0 lifecycleTrue : isActive (fiberLifecycle fiber) = True) ->
  (0 endpoint : activeEndpoint @{nameEq} selected state = True) ->
  ParentOpenEquationView name key world error value nameEq selected state
activeLifecycleEquationView nameEq selected state
  (MkFiber component parent retiredFlag table (Inactive outcome)) found
  lifecycleTrue endpoint = void (falseNotTrueO7 lifecycleTrue)
activeLifecycleEquationView nameEq selected state
  (MkFiber component parent retiredFlag table
    (Reloading remaining accumulator dependencyView)) found lifecycleTrue
  endpoint = void (falseNotTrueO7 lifecycleTrue)
activeLifecycleEquationView nameEq selected state
  (MkFiber component parent retiredFlag table
    (Active accumulator dependencyView)) found lifecycleTrue endpoint =
      ParentActiveEndpointEquation
        (MkFiber component parent retiredFlag table
          (Active accumulator dependencyView))
        accumulator dependencyView found Refl endpoint
activeLifecycleEquationView nameEq selected state
  (MkFiber component parent retiredFlag table
    (Unloading accumulator dependencyView outcome)) found lifecycleTrue endpoint =
      void (falseNotTrueO7 lifecycleTrue)

0 activeEndpointEquationView :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  (0 endpoint : activeEndpoint @{nameEq} selected state = True) ->
  ParentOpenEquationView name key world error value nameEq selected state
activeEndpointEquationView nameEq selected state endpoint =
  case parentEndpointLookupEquation nameEq selected state of
    ParentEndpointLookupMissing missing missingReloading missingActive =>
      void (falseNotTrueO7 (trans (sym missingActive) endpoint))
    ParentEndpointLookupFound fiber found foundReloading foundActive =>
      activeLifecycleEquationView nameEq selected state fiber found
        (trans (sym foundActive) endpoint) endpoint

0 parentOpenFromForeignLookupFrame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (0 frame :
    lookupFiber @{nameEq} {key = key} {value = value} {world = world}
      {error = error} selected (registry afterState) =
    lookupFiber @{nameEq} {key = key} {value = value} {world = world}
      {error = error} selected (registry before)) ->
  ParentOpenAt nameEq selected before ->
  ParentOpenAt nameEq selected afterState
parentOpenFromForeignLookupFrame nameEq selected before afterState frame
  (MkParentOpenAt fiber found opened) =
    MkParentOpenAt fiber (trans frame found) opened

0 parentOpenForeignSpike :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (action : Action name key value world error) ->
  (0 distinct : Not (selected = actionOwner action)) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  ParentOpenAt nameEq selected before ->
  ParentOpenAt nameEq selected afterState
parentOpenForeignSpike nameEq keyEq selected action distinct before afterState
  tag checked opened =
    parentOpenFromForeignLookupFrame nameEq selected before afterState
      (systemLocalUpdateForeign nameEq selected (actionOwner action) distinct
        before afterState
        (applyActionLocalUpdate nameEq keyEq action before afterState tag
          (checkedActionProjects nameEq keyEq action before afterState tag
            checked)))
      opened

0 retireActionAtFoundSpike :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (fiber : Fiber name key value world error) ->
  (0 found : lookupFiber @{nameEq} selected fibers = Just fiber) ->
  applyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} (ORetire selected)
    (MkSystemState ambient fibers) =
  Just (ORetireTag, MkSystemState ambient
    (replaceBinding @{nameEq} {key = name}
      {value = FiberAt name key value world error}
      selected (retireFiber fiber) fibers))
retireActionAtFoundSpike nameEq keyEq selected ambient fibers fiber found =
  rewrite found in Refl

0 reloadingRetiredEndpointView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) -> (ambient : world) ->
  (fibers : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (dependencyView : View name
    (dependencies (componentDependencies component))) ->
  (0 found : lookupFiber @{nameEq} selected fibers =
    Just (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator dependencyView))) ->
  ParentOpenEquationView name key world error value nameEq selected
    (MkSystemState ambient (replaceBinding @{nameEq} selected
      (retireFiber (MkFiber component parent retiredFlag table
        (Reloading remaining accumulator dependencyView))) fibers))
reloadingRetiredEndpointView nameEq selected ambient fibers component parent
  retiredFlag table remaining accumulator dependencyView found =
    ParentReloadingEndpointEquation
      (retireFiber (MkFiber component parent retiredFlag table
        (Reloading remaining accumulator dependencyView)))
      remaining accumulator dependencyView
      (lookupReplacedFiber selected
        (MkFiber component parent retiredFlag table
          (Reloading remaining accumulator dependencyView))
        (retireFiber (MkFiber component parent retiredFlag table
          (Reloading remaining accumulator dependencyView))) fibers found)
      Refl
      (rewrite lookupReplacedFiber selected
        (MkFiber component parent retiredFlag table
          (Reloading remaining accumulator dependencyView))
        (retireFiber (MkFiber component parent retiredFlag table
          (Reloading remaining accumulator dependencyView))) fibers found in Refl)

0 activeRetiredEndpointView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) -> (ambient : world) ->
  (fibers : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (dependencyView : View name
    (dependencies (componentDependencies component))) ->
  (0 found : lookupFiber @{nameEq} selected fibers =
    Just (MkFiber component parent retiredFlag table
      (Active accumulator dependencyView))) ->
  ParentOpenEquationView name key world error value nameEq selected
    (MkSystemState ambient (replaceBinding @{nameEq} selected
      (retireFiber (MkFiber component parent retiredFlag table
        (Active accumulator dependencyView))) fibers))
activeRetiredEndpointView nameEq selected ambient fibers component parent
  retiredFlag table accumulator dependencyView found =
    ParentActiveEndpointEquation
      (retireFiber (MkFiber component parent retiredFlag table
        (Active accumulator dependencyView)))
      accumulator dependencyView
      (lookupReplacedFiber selected
        (MkFiber component parent retiredFlag table
          (Active accumulator dependencyView))
        (retireFiber (MkFiber component parent retiredFlag table
          (Active accumulator dependencyView))) fibers found)
      Refl
      (rewrite lookupReplacedFiber selected
        (MkFiber component parent retiredFlag table
          (Active accumulator dependencyView))
        (retireFiber (MkFiber component parent retiredFlag table
          (Active accumulator dependencyView))) fibers found in Refl)

0 parentOpenRetireFiberView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) -> (ambient : world) ->
  (fibers : Registry name key value world error) ->
  (fiber : Fiber name key value world error) ->
  (0 found : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} selected fibers = Just fiber) ->
  LifecycleOpen {key = key} {value = value} {world = world}
    {error = error} {name = name}
    {deps = dependencies (componentDependencies (fiberComponent fiber))}
    {provision = componentProvisions (fiberComponent fiber)}
    (fiberLifecycle fiber) ->
  ParentOpenEquationView name key world error value nameEq selected
    (MkSystemState ambient (replaceBinding @{nameEq} {key = name}
      {value = FiberAt name key value world error} selected
      (retireFiber fiber) fibers))
parentOpenRetireFiberView nameEq selected ambient fibers
  (MkFiber component parent retiredFlag table (Inactive outcome)) found
  OpenReloading impossible
parentOpenRetireFiberView nameEq selected ambient fibers
  (MkFiber component parent retiredFlag table (Inactive outcome)) found
  OpenActive impossible
parentOpenRetireFiberView nameEq selected ambient fibers
  (MkFiber component parent retiredFlag table
    (Reloading remaining accumulator dependencyView)) found OpenReloading =
      reloadingRetiredEndpointView nameEq selected ambient fibers component
        parent retiredFlag table remaining accumulator dependencyView found
parentOpenRetireFiberView nameEq selected ambient fibers
  (MkFiber component parent retiredFlag table
    (Reloading remaining accumulator dependencyView)) found OpenActive impossible
parentOpenRetireFiberView nameEq selected ambient fibers
  (MkFiber component parent retiredFlag table
    (Active accumulator dependencyView)) found OpenReloading impossible
parentOpenRetireFiberView nameEq selected ambient fibers
  (MkFiber component parent retiredFlag table
    (Active accumulator dependencyView)) found OpenActive =
      activeRetiredEndpointView nameEq selected ambient fibers component parent
        retiredFlag table accumulator dependencyView found
parentOpenRetireFiberView nameEq selected ambient fibers
  (MkFiber component parent retiredFlag table
    (Unloading accumulator dependencyView outcome)) found OpenReloading impossible
parentOpenRetireFiberView nameEq selected ambient fibers
  (MkFiber component parent retiredFlag table
    (Unloading accumulator dependencyView outcome)) found OpenActive impossible

0 parentOpenRetireSourceView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) -> (ambient : world) ->
  (fibers : Registry name key value world error) ->
  (opened : ParentOpenAt {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq selected
    (MkSystemState ambient fibers)) ->
  ParentOpenEquationView name key world error value nameEq selected
    (MkSystemState ambient (replaceBinding @{nameEq} {key = name}
      {value = FiberAt name key value world error} selected
      (retireFiber (openParentFiber opened)) fibers))
parentOpenRetireSourceView nameEq selected ambient fibers opened =
  case opened of
    MkParentOpenAt fiber found lifecycle =>
      parentOpenRetireFiberView nameEq selected ambient fibers fiber found
        lifecycle

0 parentOpenFromActionResultView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (expectedTag, observedTag : RuleTag) ->
  (expectedState, observedState : SystemState name key value world error) ->
  (0 sameResult : (expectedTag, expectedState) =
    (observedTag, observedState)) ->
  ParentOpenEquationView name key world error value nameEq selected
    expectedState ->
  ParentOpenAt nameEq selected observedState
parentOpenFromActionResultView nameEq selected expectedTag observedTag
  expectedState observedState sameResult view =
    case sameResult of
      Refl => parentOpenFromEquationView view

0 parentOpenRetireSpike :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (ORetire selected)
    before = Just (tag, afterState)) ->
  ParentOpenAt nameEq selected before ->
  ParentOpenAt nameEq selected afterState
parentOpenRetireSpike nameEq keyEq selected
  (MkSystemState ambient fibers) afterState tag checked opened =
    parentOpenFromActionResultView nameEq selected ORetireTag tag
      (MkSystemState ambient (replaceBinding @{nameEq} selected
        (retireFiber (openParentFiber opened)) fibers))
      afterState
      (justInjective (trans
        (sym (retireActionAtFoundSpike nameEq keyEq selected ambient fibers
          (openParentFiber opened) (openParentFound opened)))
        (checkedActionProjects nameEq keyEq (ORetire selected)
          (MkSystemState ambient fibers) afterState tag checked)))
      (parentOpenRetireSourceView nameEq selected ambient fibers opened)

0 parentOpenAdvanceStructureSpike :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance selected)
    before = Just (tag, afterState)) ->
  (0 noRecovery : ParentRecoveryStep selected
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq (LAdvance selected) tag checked) -> Void) ->
  AdvanceStructure name key world error value nameEq keyEq selected tag before
    afterState ->
  ParentOpenAt nameEq selected afterState
parentOpenAdvanceStructureSpike nameEq keyEq selected _ before afterState
  checked noRecovery (IterAdvance fiber found witness reloading) =
    parentOpenFromEquationView
      (reloadingEndpointEquationView nameEq selected afterState reloading)
parentOpenAdvanceStructureSpike nameEq keyEq selected _ before afterState
  checked noRecovery (FinishAdvance fiber found witness active) =
    parentOpenFromEquationView
      (activeEndpointEquationView nameEq selected afterState active)
parentOpenAdvanceStructureSpike nameEq keyEq selected _ before afterState
  checked noRecovery (DivertAdvance unloading) =
    void (noRecovery (ParentDivertsAfter Refl Refl))
parentOpenAdvanceStructureSpike nameEq keyEq selected _ before afterState
  checked noRecovery (RaiseAdvance unloading) =
    void (noRecovery (ParentRaises Refl Refl))

0 installedInsertOwnerImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert selected parent component) before = Just (tag, afterState)) ->
  (0 sourceInstalled : installedAt @{nameEq} selected before = True) -> Void
installedInsertOwnerImpossible nameEq keyEq selected parent component tag before
  afterState checked sourceInstalled =
    case installationEvolutionStep nameEq keyEq selected
      (OInsert selected parent component) tag before afterState checked of
      RemainedUninstalled sourceUninstalled targetUninstalled =>
        void (falseNotTrueO7 (trans (sym sourceUninstalled) sourceInstalled))

0 installedRemoveOwnerImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (ORemove selected)
    before = Just (tag, afterState)) ->
  (0 sourceInstalled : installedAt @{nameEq} selected before = True) -> Void
installedRemoveOwnerImpossible nameEq keyEq selected tag before afterState checked
  sourceInstalled =
    case installationEvolutionStep nameEq keyEq selected (ORemove selected) tag
      before afterState checked of
      RemainedUninstalled sourceUninstalled targetUninstalled =>
        void (falseNotTrueO7 (trans (sym sourceUninstalled) sourceInstalled))

0 installedBeginOwnerImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (LBegin selected)
    before = Just (tag, afterState)) ->
  (0 sourceInstalled : installedAt @{nameEq} selected before = True) -> Void
installedBeginOwnerImpossible nameEq keyEq selected tag before afterState checked
  sourceInstalled =
    case lBeginBoundary nameEq keyEq selected before afterState tag checked of
      (tagShape, sourceUninstalled, targetInstalled) =>
        void (falseNotTrueO7
          (trans (sym sourceUninstalled) sourceInstalled))

0 installedUnloadOwnerImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (LUnload selected)
    before = Just (tag, afterState)) ->
  (0 targetInstalled : installedAt @{nameEq} selected afterState = True) -> Void
installedUnloadOwnerImpossible nameEq keyEq selected tag before afterState checked
  targetInstalled =
    case lUnloadBoundary nameEq keyEq selected before afterState tag
      (checkedActionProjects nameEq keyEq (LUnload selected) before afterState
        tag checked) of
      (tagShape, sourceInstalled, targetUninstalled) =>
        void (falseNotTrueO7
          (trans (sym targetUninstalled) targetInstalled))

0 parentOpenOwnerStepSpike :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (0 sourceInstalled : installedAt @{nameEq} (actionOwner action) before =
    True) ->
  (0 targetInstalled : installedAt @{nameEq} (actionOwner action) afterState =
    True) ->
  ParentOpenAt nameEq (actionOwner action) before ->
  (0 noRecovery : ParentRecoveryStep (actionOwner action)
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) -> Void) ->
  ParentOpenAt nameEq (actionOwner action) afterState
parentOpenOwnerStepSpike nameEq keyEq
  (OInsert selected parent component) tag before afterState checked
  sourceInstalled targetInstalled opened noRecovery =
    void (installedInsertOwnerImpossible nameEq keyEq selected parent component
      tag before afterState checked sourceInstalled)
parentOpenOwnerStepSpike nameEq keyEq (ORetire selected) tag before afterState
  checked sourceInstalled targetInstalled opened noRecovery =
    parentOpenRetireSpike nameEq keyEq selected before afterState tag checked
      opened
parentOpenOwnerStepSpike nameEq keyEq (ORemove selected) tag before afterState
  checked sourceInstalled targetInstalled opened noRecovery =
    void (installedRemoveOwnerImpossible nameEq keyEq selected tag before
      afterState checked sourceInstalled)
parentOpenOwnerStepSpike nameEq keyEq (LBegin selected) tag before afterState
  checked sourceInstalled targetInstalled opened noRecovery =
    void (installedBeginOwnerImpossible nameEq keyEq selected tag before
      afterState checked sourceInstalled)
parentOpenOwnerStepSpike nameEq keyEq (LAdvance selected) tag before afterState
  checked sourceInstalled targetInstalled opened noRecovery =
    parentOpenAdvanceStructureSpike nameEq keyEq selected tag before afterState
      checked noRecovery
      (advanceStructureTheorem nameEq keyEq selected before afterState tag
        (checkedActionProjects nameEq keyEq (LAdvance selected) before afterState
          tag checked))
parentOpenOwnerStepSpike nameEq keyEq (LDivert selected) tag before afterState
  checked sourceInstalled targetInstalled opened noRecovery =
    void (noRecovery (ParentDivertsBefore Refl))
parentOpenOwnerStepSpike nameEq keyEq (LLeave selected) tag before afterState
  checked sourceInstalled targetInstalled opened noRecovery =
    void (noRecovery (ParentLeaves Refl))
parentOpenOwnerStepSpike nameEq keyEq (LUnload selected) tag before afterState
  checked sourceInstalled targetInstalled opened noRecovery =
    void (installedUnloadOwnerImpossible nameEq keyEq selected tag before
      afterState checked targetInstalled)

0 parentOpenInstalledStepSpike :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (0 sourceInstalled : installedAt @{nameEq} selected before = True) ->
  (0 targetInstalled : installedAt @{nameEq} selected afterState = True) ->
  ParentOpenAt nameEq selected before ->
  (0 noRecovery : ParentRecoveryStep selected
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) -> Void) ->
  ParentOpenAt nameEq selected afterState
parentOpenInstalledStepSpike nameEq keyEq selected action tag before afterState
  checked sourceInstalled targetInstalled opened noRecovery =
    case decEq @{nameEq} selected (actionOwner action) of
      No distinct => parentOpenForeignSpike nameEq keyEq selected action distinct
        before afterState tag checked opened
      Yes Refl => parentOpenOwnerStepSpike nameEq keyEq action tag before
        afterState checked sourceInstalled targetInstalled opened noRecovery

record NoParentRecoveryConsView
  (name, key, world, error : Type) (value : key -> Type)
  {first, middle, finalState : SystemState name key value world error}
  (parent : name) (transition : Transition first middle)
  (rest : Transitions middle finalState) where
  constructor MkNoParentRecoveryConsView
  0 noParentRecoveryAtHead : ParentRecoveryStep parent transition -> Void
  0 noParentRecoveryInTail : NoParentRecovery parent rest

0 noParentRecoveryConsView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (parent : name) -> (transition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  NoParentRecovery parent (MoreTransitions transition rest) ->
  NoParentRecoveryConsView name key world error value parent transition rest
noParentRecoveryConsView parent _ _
  (NoParentRecoveryStep transition rest noRecovery tail) =
    MkNoParentRecoveryConsView noRecovery tail

0 parentOpenNoRecoveryInstalledSpike :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  InstalledTrace name key world error value nameEq keyEq selected trace ->
  NoParentRecovery selected trace ->
  ParentOpenAt nameEq selected first ->
  ParentOpenAt nameEq selected finalState
parentOpenNoRecoveryInstalledSpike nameEq keyEq selected _
  (InstalledEnd installed) noRecovery opened = opened
parentOpenNoRecoveryInstalledSpike nameEq keyEq selected _
  (InstalledStep action tag checked rest sourceInstalled tailInstalled)
  noRecovery opened =
    parentOpenNoRecoveryInstalledSpike nameEq keyEq selected rest tailInstalled
      (noParentRecoveryInTail
        (noParentRecoveryConsView selected
          (Fired nameEq keyEq action tag checked) rest noRecovery))
      (parentOpenInstalledStepSpike nameEq keyEq selected action tag _ _ checked
        sourceInstalled (installedTraceStart tailInstalled) opened
        (noParentRecoveryAtHead
          (noParentRecoveryConsView selected
            (Fired nameEq keyEq action tag checked) rest noRecovery)))

0 unloadActionOpenNothingSpike :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (fiber : Fiber name key value world error) ->
  (0 found : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} selected fibers = Just fiber) ->
  LifecycleOpen {key = key} {value = value} {world = world}
    {error = error} {name = name}
    {deps = dependencies (componentDependencies (fiberComponent fiber))}
    {provision = componentProvisions (fiberComponent fiber)}
    (fiberLifecycle fiber) ->
  applyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} (LUnload selected)
    (MkSystemState ambient fibers) = Nothing
unloadActionOpenNothingSpike nameEq keyEq selected ambient fibers
  (MkFiber component parent retiredFlag table (Inactive outcome)) found
  OpenReloading impossible
unloadActionOpenNothingSpike nameEq keyEq selected ambient fibers
  (MkFiber component parent retiredFlag table (Inactive outcome)) found
  OpenActive impossible
unloadActionOpenNothingSpike nameEq keyEq selected ambient fibers
  (MkFiber component parent retiredFlag table
    (Reloading remaining accumulator dependencyView)) found OpenReloading =
      rewrite found in Refl
unloadActionOpenNothingSpike nameEq keyEq selected ambient fibers
  (MkFiber component parent retiredFlag table
    (Reloading remaining accumulator dependencyView)) found OpenActive impossible
unloadActionOpenNothingSpike nameEq keyEq selected ambient fibers
  (MkFiber component parent retiredFlag table
    (Active accumulator dependencyView)) found OpenReloading impossible
unloadActionOpenNothingSpike nameEq keyEq selected ambient fibers
  (MkFiber component parent retiredFlag table
    (Active accumulator dependencyView)) found OpenActive =
      rewrite found in Refl
unloadActionOpenNothingSpike nameEq keyEq selected ambient fibers
  (MkFiber component parent retiredFlag table
    (Unloading accumulator dependencyView outcome)) found OpenReloading impossible
unloadActionOpenNothingSpike nameEq keyEq selected ambient fibers
  (MkFiber component parent retiredFlag table
    (Unloading accumulator dependencyView outcome)) found OpenActive impossible

0 unloadOpenAtImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  UnloadStep nameEq keyEq selected before afterState ->
  ParentOpenAt nameEq selected before -> Void
unloadOpenAtImpossible nameEq keyEq selected (MkSystemState ambient fibers)
  afterState closing opened =
    nothingIsNotJust (trans
      (sym (unloadActionOpenNothingSpike nameEq keyEq selected ambient fibers
        (openParentFiber opened) (openParentFound opened)
        (openParentLifecycle opened)))
      (checkedActionProjects nameEq keyEq (LUnload selected)
        (MkSystemState ambient fibers) afterState LUnloadTag
        (unloadEquation closing)))

record NoParentRecoveryAppendView
  (name, key, world, error : Type) (value : key -> Type)
  {first, middle, finalState : SystemState name key value world error}
  (parent : name) (left : Transitions first middle)
  (right : Transitions middle finalState) where
  constructor MkNoParentRecoveryAppendView
  0 noRecoveryAppendLeft : NoParentRecovery parent left
  0 noRecoveryAppendRight : NoParentRecovery parent right

0 splitNoParentRecoveryAppend :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (parent : name) -> (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  NoParentRecovery parent (appendTransitions left right) ->
  NoParentRecoveryAppendView name key world error value parent left right
splitNoParentRecoveryAppend parent NoTransitions right noRecovery =
  MkNoParentRecoveryAppendView NoParentRecoveryEnd noRecovery
splitNoParentRecoveryAppend parent
  (MoreTransitions transition rest) right noRecovery =
    MkNoParentRecoveryAppendView
      (NoParentRecoveryStep transition rest
        (noParentRecoveryAtHead
          (noParentRecoveryConsView parent transition
            (appendTransitions rest right) noRecovery))
        (noRecoveryAppendLeft
          (splitNoParentRecoveryAppend parent rest right
            (noParentRecoveryInTail
              (noParentRecoveryConsView parent transition
                (appendTransitions rest right) noRecovery)))))
      (noRecoveryAppendRight
        (splitNoParentRecoveryAppend parent rest right
          (noParentRecoveryInTail
            (noParentRecoveryConsView parent transition
              (appendTransitions rest right) noRecovery))))

0 noParentRecoveryAtClosingSplit :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  (closing : FirstClosingResult name key world error value nameEq keyEq selected
    trace) ->
  NoParentRecovery selected trace ->
  NoParentRecovery selected
    (appendTransitions (traceBeforeFirstClosing closing)
      (MoreTransitions (unloadTransition (firstClosingStep closing))
        (traceAfterFirstClosing closing)))
noParentRecoveryAtClosingSplit nameEq keyEq selected trace closing noRecovery =
  replace {p = \candidate => NoParentRecovery selected candidate}
    (sym (closingSplit closing)) noRecovery

0 noRecoveryClosingImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  (closing : FirstClosingResult name key world error value nameEq keyEq selected
    trace) ->
  ParentOpenAt nameEq selected first ->
  NoParentRecovery selected trace -> Void
noRecoveryClosingImpossible nameEq keyEq selected trace closing opened noRecovery =
  unloadOpenAtImpossible nameEq keyEq selected (closingBefore closing)
    (closingAfter closing) (firstClosingStep closing)
    (parentOpenNoRecoveryInstalledSpike nameEq keyEq selected
      (traceBeforeFirstClosing closing) (beforeClosingInstalled closing)
      (noRecoveryAppendLeft
        (splitNoParentRecoveryAppend selected
          (traceBeforeFirstClosing closing)
          (MoreTransitions (unloadTransition (firstClosingStep closing))
            (traceAfterFirstClosing closing))
          (noParentRecoveryAtClosingSplit nameEq keyEq selected trace closing
            noRecovery)))
      opened)

0 childRetirementOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (parent, child : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  ChildRetiresBeforeRecovery parent child trace ->
  ActionOccurs (ORetire child) trace
childRetirementOccurrence parent child _
  (ChildRetiresNow transition rest retires) =
    ActionOccursHere transition rest retires
childRetirementOccurrence parent child _
  (ChildRetiresLater transition rest noRecovery tail) =
    ActionOccursLater transition rest
      (childRetirementOccurrence parent child rest tail)

0 retirementProvenanceClosingOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (parent, child : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  ChildRetirementProvenance parent child trace ->
  FirstClosingResult name key world error value nameEq keyEq parent trace ->
  ParentOpenAt nameEq parent first ->
  ActionOccurs (ORetire child) trace
retirementProvenanceClosingOccurrence nameEq keyEq parent child trace
  (ParentDoesNotRecover noRecovery) closing opened =
    void (noRecoveryClosingImpossible nameEq keyEq parent trace closing opened
      noRecovery)
retirementProvenanceClosingOccurrence nameEq keyEq parent child trace
  (ChildRetiredBeforeParent retirement) closing opened =
    childRetirementOccurrence parent child trace retirement

0 lifecycleOpenInstalledSpike :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  (life : Lifecycle key value world error name deps provision) ->
  LifecycleOpen life -> installed life = True
lifecycleOpenInstalledSpike (Inactive outcome) OpenReloading impossible
lifecycleOpenInstalledSpike (Inactive outcome) OpenActive impossible
lifecycleOpenInstalledSpike
  (Reloading remaining accumulator dependencyView) OpenReloading = Refl
lifecycleOpenInstalledSpike
  (Reloading remaining accumulator dependencyView) OpenActive impossible
lifecycleOpenInstalledSpike (Active accumulator dependencyView) OpenReloading
  impossible
lifecycleOpenInstalledSpike (Active accumulator dependencyView) OpenActive = Refl
lifecycleOpenInstalledSpike
  (Unloading accumulator dependencyView outcome) OpenReloading impossible
lifecycleOpenInstalledSpike
  (Unloading accumulator dependencyView outcome) OpenActive impossible

0 parentOpenInstalledSpike :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  ParentOpenAt nameEq selected state ->
  installedAt @{nameEq} selected state = True
parentOpenInstalledSpike nameEq selected state
  (MkParentOpenAt fiber found opened) =
    trans (installedAtFound nameEq selected state fiber found)
      (lifecycleOpenInstalledSpike (fiberLifecycle fiber) opened)

0 unloadOpenTagTransportImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (LUnload selected)
    before = Just (tag, afterState)) ->
  ParentOpenAt nameEq selected before ->
  (0 tagShape : tag = LUnloadTag) -> Void
unloadOpenTagTransportImpossible nameEq keyEq selected tag before afterState
  checked opened tagShape =
    case tagShape of
      Refl => unloadOpenAtImpossible nameEq keyEq selected before afterState
        (MkUnloadStep checked) opened

0 unloadCheckedOpenImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (LUnload selected)
    before = Just (tag, afterState)) ->
  ParentOpenAt nameEq selected before -> Void
unloadCheckedOpenImpossible nameEq keyEq selected tag before afterState checked
  opened =
    unloadOpenTagTransportImpossible nameEq keyEq selected tag before afterState
      checked opened
      (fst (lUnloadBoundary nameEq keyEq selected before afterState tag
        (checkedActionProjects nameEq keyEq (LUnload selected) before afterState
          tag checked)))

0 parentOpenOwnerNoRecoveryStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  ParentOpenAt nameEq (actionOwner action) before ->
  (0 noRecovery : ParentRecoveryStep (actionOwner action)
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) -> Void) ->
  ParentOpenAt nameEq (actionOwner action) afterState
parentOpenOwnerNoRecoveryStep nameEq keyEq
  (OInsert selected parent component) tag before afterState checked opened
  noRecovery =
    void (installedInsertOwnerImpossible nameEq keyEq selected parent component
      tag before afterState checked
      (parentOpenInstalledSpike nameEq selected before opened))
parentOpenOwnerNoRecoveryStep nameEq keyEq (ORetire selected) tag before
  afterState checked opened noRecovery =
    parentOpenRetireSpike nameEq keyEq selected before afterState tag checked
      opened
parentOpenOwnerNoRecoveryStep nameEq keyEq (ORemove selected) tag before
  afterState checked opened noRecovery =
    void (installedRemoveOwnerImpossible nameEq keyEq selected tag before
      afterState checked (parentOpenInstalledSpike nameEq selected before opened))
parentOpenOwnerNoRecoveryStep nameEq keyEq (LBegin selected) tag before afterState
  checked opened noRecovery =
    void (installedBeginOwnerImpossible nameEq keyEq selected tag before
      afterState checked (parentOpenInstalledSpike nameEq selected before opened))
parentOpenOwnerNoRecoveryStep nameEq keyEq (LAdvance selected) tag before
  afterState checked opened noRecovery =
    parentOpenAdvanceStructureSpike nameEq keyEq selected tag before afterState
      checked noRecovery
      (advanceStructureTheorem nameEq keyEq selected before afterState tag
        (checkedActionProjects nameEq keyEq (LAdvance selected) before afterState
          tag checked))
parentOpenOwnerNoRecoveryStep nameEq keyEq (LDivert selected) tag before afterState
  checked opened noRecovery =
    void (noRecovery (ParentDivertsBefore Refl))
parentOpenOwnerNoRecoveryStep nameEq keyEq (LLeave selected) tag before afterState
  checked opened noRecovery =
    void (noRecovery (ParentLeaves Refl))
parentOpenOwnerNoRecoveryStep nameEq keyEq (LUnload selected) tag before afterState
  checked opened noRecovery =
    void (unloadCheckedOpenImpossible nameEq keyEq selected tag before afterState
      checked opened)

0 parentOpenNoRecoveryStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  ParentOpenAt nameEq selected before ->
  (0 noRecovery : ParentRecoveryStep selected
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) -> Void) ->
  ParentOpenAt nameEq selected afterState
parentOpenNoRecoveryStep nameEq keyEq selected action tag before afterState
  checked opened noRecovery =
    case decEq @{nameEq} selected (actionOwner action) of
      No distinct => parentOpenForeignSpike nameEq keyEq selected action distinct
        before afterState tag checked opened
      Yes Refl => parentOpenOwnerNoRecoveryStep nameEq keyEq action tag before
        afterState checked opened noRecovery

0 unloadActionEqualityOpenImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  ParentOpenAt nameEq selected before ->
  (0 unloadAction : action = LUnload selected) -> Void
unloadActionEqualityOpenImpossible nameEq keyEq selected action tag before
  afterState checked opened unloadAction =
    case unloadAction of
      Refl => unloadCheckedOpenImpossible nameEq keyEq selected tag before
        afterState checked opened

0 alignedTransitionTail :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (transition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions transition rest) ->
  AlignedTransitions name key world error value nameEq keyEq rest
alignedTransitionTail nameEq keyEq _ _
  (AlignedStep action tag checked rest alignedTail) = alignedTail

0 alignedNoRecoveryHeadOpen :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (transition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions transition rest) ->
  ParentOpenAt nameEq selected first ->
  (0 noRecovery : ParentRecoveryStep selected transition -> Void) ->
  ParentOpenAt nameEq selected middle
alignedNoRecoveryHeadOpen nameEq keyEq selected _ _
  (AlignedStep action tag checked rest alignedTail) opened noRecovery =
    parentOpenNoRecoveryStep nameEq keyEq selected action tag _ _ checked opened
      noRecovery

0 alignedUnloadHeadOpenImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (transition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions transition rest) ->
  ParentOpenAt nameEq selected first ->
  (0 unloadAction : transitionAction transition = LUnload selected) -> Void
alignedUnloadHeadOpenImpossible nameEq keyEq selected _ _
  (AlignedStep action tag checked rest alignedTail) opened unloadAction =
    unloadActionEqualityOpenImpossible nameEq keyEq selected action tag _ _
      checked opened unloadAction

0 noRecoveryUnloadOccurrenceImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  ActionOccurs (LUnload selected) trace ->
  NoParentRecovery selected trace ->
  ParentOpenAt nameEq selected first -> Void
noRecoveryUnloadOccurrenceImpossible nameEq keyEq selected _ aligned
  (ActionOccursHere transition rest unloadAction) noRecovery opened =
    alignedUnloadHeadOpenImpossible nameEq keyEq selected transition rest aligned
      opened unloadAction
noRecoveryUnloadOccurrenceImpossible nameEq keyEq selected _ aligned
  (ActionOccursLater transition rest later) noRecovery opened =
    noRecoveryUnloadOccurrenceImpossible nameEq keyEq selected rest
      (alignedTransitionTail nameEq keyEq transition rest aligned) later
      (noParentRecoveryInTail
        (noParentRecoveryConsView selected transition rest noRecovery))
      (alignedNoRecoveryHeadOpen nameEq keyEq selected transition rest aligned
        opened
        (noParentRecoveryAtHead
          (noParentRecoveryConsView selected transition rest noRecovery)))

0 retirementProvenanceUnloadOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (parent, child : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  ChildRetirementProvenance parent child trace ->
  ActionOccurs (LUnload parent) trace ->
  ParentOpenAt nameEq parent first ->
  ActionOccurs (ORetire child) trace
retirementProvenanceUnloadOccurrence nameEq keyEq parent child trace aligned
  (ParentDoesNotRecover noRecovery) unload opened =
    void (noRecoveryUnloadOccurrenceImpossible nameEq keyEq parent trace aligned
      unload noRecovery opened)
retirementProvenanceUnloadOccurrence nameEq keyEq parent child trace aligned
  (ChildRetiredBeforeParent retirement) unload opened =
    childRetirementOccurrence parent child trace retirement

0 alignedAfterGeneratedRegistration :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (child, parent : name) ->
  (component : Component key value world error) ->
  (occurrence : LocatedGeneratedRegistration child parent component global) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  AlignedTransitions name key world error value nameEq keyEq
    (afterRegistration occurrence)
alignedAfterGeneratedRegistration nameEq keyEq global child parent component
  occurrence aligned =
    alignedTransitionTail nameEq keyEq (registrationTransition occurrence)
      (afterRegistration occurrence)
      (snd (alignedAppendSplit (beforeRegistration occurrence)
        (MoreTransitions (registrationTransition occurrence)
          (afterRegistration occurrence))
        (replace
          {p = AlignedTransitions name key world error value nameEq keyEq}
          (sym (registrationDecomposition occurrence)) aligned)))

0 registrationDisciplineAppendRight :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  RegistrationDiscipline protocol nameEq (appendTransitions left right) ->
  RegistrationDiscipline protocol nameEq right
registrationDisciplineAppendRight protocol nameEq NoTransitions right
  discipline = discipline
registrationDisciplineAppendRight protocol nameEq
  (MoreTransitions transition rest) right
  (RegistrationDisciplineStep _ _ step tail) =
    registrationDisciplineAppendRight protocol nameEq rest right tail

0 registrationDisciplineHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (transition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  RegistrationDiscipline protocol nameEq
    (MoreTransitions transition rest) ->
  RegistrationStepDiscipline protocol nameEq (transitionAction transition)
    first rest
registrationDisciplineHead protocol nameEq _ _
  (RegistrationDisciplineStep transition rest step tail) = step

0 registrationDisciplineAtGenerated :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (child, parent : name) ->
  (component : Component key value world error) ->
  (occurrence : LocatedGeneratedRegistration child parent component global) ->
  RegistrationDiscipline protocol nameEq global ->
  RegistrationStepDiscipline protocol nameEq
    (OInsert child (ChildOf parent) component)
    (registrationBefore occurrence) (afterRegistration occurrence)
registrationDisciplineAtGenerated protocol nameEq global child parent component
  occurrence discipline =
    replace
      {p = \action => RegistrationStepDiscipline protocol nameEq action
        (registrationBefore occurrence) (afterRegistration occurrence)}
      (registrationAction occurrence)
      (registrationDisciplineHead protocol nameEq
        (registrationTransition occurrence) (afterRegistration occurrence)
        (registrationDisciplineAppendRight protocol nameEq
          (beforeRegistration occurrence)
          (MoreTransitions (registrationTransition occurrence)
            (afterRegistration occurrence))
          (replace {p = RegistrationDiscipline protocol nameEq}
            (sym (registrationDecomposition occurrence)) discipline)))

0 childInsertParentDistinct :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (child, parent : name) -> (component : Component key value world error) ->
  (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert child (ChildOf parent) component) before = Just (tag, afterState)) ->
  ParentOpenAt nameEq parent before -> Not (parent = child)
childInsertParentDistinct nameEq keyEq child parent component tag before
  afterState checked opened same =
    case same of
      Refl => installedInsertOwnerImpossible nameEq keyEq child
        (ChildOf child) component tag before afterState checked
        (parentOpenInstalledSpike nameEq child before opened)

0 parentOpenAtRegistrationYield :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (parent : name) ->
  (component : Component key value world error) ->
  (state : SystemState name key value world error) ->
  ParentRegistrationYield protocol nameEq parent component state ->
  ParentOpenAt nameEq parent state
parentOpenAtRegistrationYield protocol nameEq parent component state yielded =
  MkParentOpenAt (parentFiberAtYield yielded) (parentFoundAtYield yielded)
    (replace {p = LifecycleOpen} (sym (parentAtYield yielded)) OpenReloading)

0 parentOpenAfterChildInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (child, parent : name) -> (component : Component key value world error) ->
  (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert child (ChildOf parent) component) before = Just (tag, afterState)) ->
  ParentRegistrationYield protocol nameEq parent component before ->
  ParentOpenAt nameEq parent afterState
parentOpenAfterChildInsert protocol nameEq keyEq child parent component tag before
  afterState checked yielded =
    parentOpenForeignSpike nameEq keyEq parent
      (OInsert child (ChildOf parent) component)
      (childInsertParentDistinct nameEq keyEq child parent component tag before
        afterState checked
        (parentOpenAtRegistrationYield protocol nameEq parent component before
          yielded))
      before afterState tag checked
      (parentOpenAtRegistrationYield protocol nameEq parent component before
        yielded)

record AlignedChildInsertStep
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (child, parent : name) (component : Component key value world error)
  (before, afterState : SystemState name key value world error)
  {finalState : SystemState name key value world error}
  (rest : Transitions afterState finalState) where
  constructor MkAlignedChildInsertStep
  childInsertTag : RuleTag
  0 childInsertChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert child (ChildOf parent) component) before =
    Just (childInsertTag, afterState)
  0 childInsertTailAligned : AlignedTransitions name key world error value
    nameEq keyEq rest

0 alignedChildInsertActionTransport :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (child, parent : name) -> (component : Component key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  {finalState : SystemState name key value world error} ->
  (rest : Transitions afterState finalState) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  AlignedTransitions name key world error value nameEq keyEq rest ->
  (0 actionShape : action = OInsert child (ChildOf parent) component) ->
  AlignedChildInsertStep name key world error value nameEq keyEq child parent
    component before afterState rest
alignedChildInsertActionTransport nameEq keyEq child parent component action tag
  before afterState rest checked aligned actionShape =
    case actionShape of
      Refl => MkAlignedChildInsertStep tag checked aligned

0 alignedGeneratedRegistrationParts :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (child, parent : name) ->
  (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (beforeTrace : Transitions initial before) ->
  (transition : Transition before afterState) ->
  (rest : Transitions afterState finalState) ->
  (0 actionShape : transitionAction transition =
    OInsert child (ChildOf parent) component) ->
  (0 decomposition : appendTransitions beforeTrace
    (MoreTransitions transition rest) = global) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  AlignedChildInsertStep name key world error value nameEq keyEq child parent
    component before afterState rest
alignedGeneratedRegistrationParts nameEq keyEq global child parent component
  before afterState beforeTrace transition rest actionShape decomposition aligned =
    case snd (alignedAppendSplit beforeTrace (MoreTransitions transition rest)
      (replace {p = AlignedTransitions name key world error value nameEq keyEq}
        (sym decomposition) aligned)) of
      AlignedStep action tag checked _ alignedTail =>
        alignedChildInsertActionTransport nameEq keyEq child parent component
          action tag before afterState rest checked alignedTail actionShape

0 childRetirementFromGeneratedCapital :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (child, parent : name) -> (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  {finalState : SystemState name key value world error} ->
  (rest : Transitions afterState finalState) ->
  (alignedStep : AlignedChildInsertStep name key world error value nameEq keyEq
    child parent component before afterState rest) ->
  RegistrationStepDiscipline protocol nameEq
    (OInsert child (ChildOf parent) component) before rest ->
  ActionOccurs (LUnload parent) rest ->
  ActionOccurs (ORetire child) rest
childRetirementFromGeneratedCapital protocol nameEq keyEq child parent component
  before afterState rest alignedStep discipline unload =
    retirementProvenanceUnloadOccurrence nameEq keyEq parent child rest
      (childInsertTailAligned alignedStep) (snd discipline) unload
      (parentOpenAfterChildInsert protocol nameEq keyEq child parent component
        (childInsertTag alignedStep) before afterState
        (childInsertChecked alignedStep) (fst discipline))

0 childRetirementAtGeneratedParts :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (child, parent : name) ->
  (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (beforeTrace : Transitions initial before) ->
  (transition : Transition before afterState) ->
  (rest : Transitions afterState finalState) ->
  (0 actionShape : transitionAction transition =
    OInsert child (ChildOf parent) component) ->
  (0 decomposition : appendTransitions beforeTrace
    (MoreTransitions transition rest) = global) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  RegistrationDiscipline protocol nameEq global ->
  ActionOccurs (LUnload parent) rest ->
  ActionOccurs (ORetire child) rest
childRetirementAtGeneratedParts protocol nameEq keyEq global child parent
  component before afterState beforeTrace transition rest actionShape
  decomposition aligned discipline unload =
    childRetirementFromGeneratedCapital protocol nameEq keyEq child parent
      component before afterState rest
      (alignedGeneratedRegistrationParts nameEq keyEq global child parent
        component before afterState beforeTrace transition rest actionShape
        decomposition aligned)
      (registrationDisciplineAtGenerated protocol nameEq global child parent
        component
        (MkLocatedGeneratedRegistration before afterState beforeTrace transition
          rest actionShape decomposition)
        discipline)
      unload

0 childRetirementAtGeneratedOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (child, parent : name) ->
  (component : Component key value world error) ->
  (occurrence : LocatedGeneratedRegistration child parent component global) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  RegistrationDiscipline protocol nameEq global ->
  ActionOccurs (LUnload parent) (afterRegistration occurrence) ->
  ActionOccurs (ORetire child) (afterRegistration occurrence)
childRetirementAtGeneratedOccurrence protocol nameEq keyEq global child parent
  component occurrence aligned discipline unload =
    case occurrence of
      MkLocatedGeneratedRegistration before afterState beforeTrace transition rest
        actionShape decomposition =>
          childRetirementAtGeneratedParts protocol nameEq keyEq global child
            parent component before afterState beforeTrace transition rest
            actionShape decomposition aligned discipline unload

record ChildRetirementHeadView
  (name, key, world, error : Type) (value : key -> Type)
  (parent, child : name)
  {first, middle, finalState : SystemState name key value world error}
  (transition : Transition first middle)
  (rest : Transitions middle finalState) where
  constructor MkChildRetirementHeadView
  0 childRetiresAtHead : Either
    (transitionAction transition = ORetire child)
    ((ParentRecoveryStep parent transition -> Void),
     ChildRetiresBeforeRecovery parent child rest)

0 childRetirementHeadView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (parent, child : name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (transition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  ChildRetiresBeforeRecovery parent child
    (MoreTransitions transition rest) ->
  ChildRetirementHeadView name key world error value parent child transition rest
childRetirementHeadView parent child _ _
  (ChildRetiresNow transition rest retires) =
    MkChildRetirementHeadView (Left retires)
childRetirementHeadView parent child _ _
  (ChildRetiresLater transition rest noRecovery tail) =
    MkChildRetirementHeadView (Right (noRecovery, tail))

record ActionOccurrenceHeadView
  (name, key, world, error : Type) (value : key -> Type)
  (action : Action name key value world error)
  {first, middle, finalState : SystemState name key value world error}
  (transition : Transition first middle)
  (rest : Transitions middle finalState) where
  constructor MkActionOccurrenceHeadView
  0 actionOccursAtHead : Either
    (transitionAction transition = action)
    (ActionOccurs action rest)

0 actionOccurrenceHeadView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (action : Action name key value world error) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (transition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  ActionOccurs action (MoreTransitions transition rest) ->
  ActionOccurrenceHeadView name key world error value action transition rest
actionOccurrenceHeadView action _ _
  (ActionOccursHere transition rest actionShape) =
    MkActionOccurrenceHeadView (Left actionShape)
actionOccurrenceHeadView action _ _
  (ActionOccursLater transition rest later) =
    MkActionOccurrenceHeadView (Right later)

mutual
  0 childRetirementBeforeUnload :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) -> (keyEq : DecEq key) ->
    (parent, child : name) ->
    {first, finalState : SystemState name key value world error} ->
    (trace : Transitions first finalState) ->
    AlignedTransitions name key world error value nameEq keyEq trace ->
    ChildRetiresBeforeRecovery parent child trace ->
    ActionOccurs (LUnload parent) trace ->
    ParentOpenAt nameEq parent first ->
    ActionBefore (ORetire child) (LUnload parent) trace
  childRetirementBeforeUnload nameEq keyEq parent child _ aligned retirement
    (ActionOccursHere transition rest unloadAction) opened =
      void (alignedUnloadHeadOpenImpossible nameEq keyEq parent transition rest
        aligned opened unloadAction)
  childRetirementBeforeUnload nameEq keyEq parent child _ aligned retirement
    (ActionOccursLater transition rest laterUnload) opened =
      childRetirementBeforeLaterUnload nameEq keyEq parent child transition rest
        aligned retirement laterUnload opened

  0 childRetirementBeforeLaterUnload :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) -> (keyEq : DecEq key) ->
    (parent, child : name) ->
    {first, middle, finalState : SystemState name key value world error} ->
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    AlignedTransitions name key world error value nameEq keyEq
      (MoreTransitions transition rest) ->
    ChildRetiresBeforeRecovery parent child
      (MoreTransitions transition rest) ->
    ActionOccurs (LUnload parent) rest ->
    ParentOpenAt nameEq parent first ->
    ActionBefore (ORetire child) (LUnload parent)
      (MoreTransitions transition rest)
  childRetirementBeforeLaterUnload nameEq keyEq parent child _ _ aligned
    (ChildRetiresNow transition rest retires) laterUnload opened =
      ActionBeforeHere transition rest retires laterUnload
  childRetirementBeforeLaterUnload nameEq keyEq parent child _ _ aligned
    (ChildRetiresLater transition rest noRecovery tailRetirement) laterUnload
    opened =
      ActionBeforeLater transition rest
        (childRetirementBeforeUnload nameEq keyEq parent child rest
          (alignedTransitionTail nameEq keyEq transition rest aligned)
          tailRetirement laterUnload
          (alignedNoRecoveryHeadOpen nameEq keyEq parent transition rest aligned
            opened noRecovery))

0 retirementProvenanceBeforeUnload :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (parent, child : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  ChildRetirementProvenance parent child trace ->
  ActionOccurs (LUnload parent) trace ->
  ParentOpenAt nameEq parent first ->
  ActionBefore (ORetire child) (LUnload parent) trace
retirementProvenanceBeforeUnload nameEq keyEq parent child trace aligned
  (ParentDoesNotRecover noRecovery) unload opened =
    void (noRecoveryUnloadOccurrenceImpossible nameEq keyEq parent trace aligned
      unload noRecovery opened)
retirementProvenanceBeforeUnload nameEq keyEq parent child trace aligned
  (ChildRetiredBeforeParent retirement) unload opened =
    childRetirementBeforeUnload nameEq keyEq parent child trace aligned retirement
      unload opened

mutual
  0 childRetirementBeforePrefixUnload :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) -> (keyEq : DecEq key) ->
    (parent, child : name) ->
    {first, middle, finalState : SystemState name key value world error} ->
    (left : Transitions first middle) ->
    (right : Transitions middle finalState) ->
    AlignedTransitions name key world error value nameEq keyEq
      (appendTransitions left right) ->
    ChildRetiresBeforeRecovery parent child (appendTransitions left right) ->
    ActionOccurs (LUnload parent) left ->
    ParentOpenAt nameEq parent first ->
    ActionOccurs (ORetire child) left
  childRetirementBeforePrefixUnload nameEq keyEq parent child _ right aligned
    retirement (ActionOccursHere transition rest unloadAction) opened =
      void (alignedUnloadHeadOpenImpossible nameEq keyEq parent transition
        (appendTransitions rest right) aligned opened unloadAction)
  childRetirementBeforePrefixUnload nameEq keyEq parent child _ right aligned
    retirement (ActionOccursLater transition rest laterUnload) opened =
      childRetirementBeforePrefixLaterUnload nameEq keyEq parent child transition
        rest right aligned retirement laterUnload opened

  0 childRetirementBeforePrefixLaterUnload :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) -> (keyEq : DecEq key) ->
    (parent, child : name) ->
    {first, middle, later, finalState : SystemState name key value world error} ->
    (transition : Transition first middle) ->
    (leftRest : Transitions middle later) ->
    (right : Transitions later finalState) ->
    AlignedTransitions name key world error value nameEq keyEq
      (MoreTransitions transition (appendTransitions leftRest right)) ->
    ChildRetiresBeforeRecovery parent child
      (MoreTransitions transition (appendTransitions leftRest right)) ->
    ActionOccurs (LUnload parent) leftRest ->
    ParentOpenAt nameEq parent first ->
    ActionOccurs (ORetire child) (MoreTransitions transition leftRest)
  childRetirementBeforePrefixLaterUnload nameEq keyEq parent child _ leftRest right
    aligned (ChildRetiresNow transition _ retires) laterUnload opened =
      ActionOccursHere transition _ retires
  childRetirementBeforePrefixLaterUnload nameEq keyEq parent child _ leftRest right
    aligned
    (ChildRetiresLater transition _ noRecovery tailRetirement) laterUnload
    opened =
      ActionOccursLater transition _
        (childRetirementBeforePrefixUnload nameEq keyEq parent child _ right
          (alignedTransitionTail nameEq keyEq transition
            (appendTransitions leftRest right) aligned)
          tailRetirement laterUnload
          (alignedNoRecoveryHeadOpen nameEq keyEq parent transition
            (appendTransitions leftRest right) aligned opened noRecovery))

0 retirementProvenanceBeforePrefixUnload :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (parent, child : name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  AlignedTransitions name key world error value nameEq keyEq
    (appendTransitions left right) ->
  ChildRetirementProvenance parent child (appendTransitions left right) ->
  ActionOccurs (LUnload parent) left ->
  ParentOpenAt nameEq parent first ->
  ActionOccurs (ORetire child) left
retirementProvenanceBeforePrefixUnload nameEq keyEq parent child left right aligned
  (ParentDoesNotRecover noRecovery) unload opened =
    void (noRecoveryUnloadOccurrenceImpossible nameEq keyEq parent left
      (fst (alignedAppendSplit left right aligned)) unload
      (noRecoveryAppendLeft
        (splitNoParentRecoveryAppend parent left right noRecovery)) opened)
retirementProvenanceBeforePrefixUnload nameEq keyEq parent child left right aligned
  (ChildRetiredBeforeParent retirement) unload opened =
    childRetirementBeforePrefixUnload nameEq keyEq parent child left right aligned
      retirement unload opened

0 locatedEpisodeChildRegistration :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (selected, child : name) ->
  (component : Component key value world error) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  (birth : LocatedActionOccurrence
    (OInsert child (ChildOf selected) component)
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode)))) ->
  LocatedGeneratedRegistration child selected component global
locatedEpisodeChildRegistration nameEq keyEq global selected child component
  episode
  (MkLocatedActionOccurrence before afterState beforeTrace transition rest
    actionShape decomposition) =
      MkLocatedGeneratedRegistration before afterState
        (appendTransitions (traceBeforeOpening episode) beforeTrace) transition
        (appendTransitions rest (traceAfterClosing episode)) actionShape
        (rewrite appendTransitionsAssociative (traceBeforeOpening episode)
          beforeTrace
          (MoreTransitions transition
            (appendTransitions rest (traceAfterClosing episode))) in
         rewrite sym (appendTransitionsAssociative beforeTrace
          (MoreTransitions transition rest) (traceAfterClosing episode)) in
         rewrite decomposition in locatedDecomposition episode)

0 childRetirementFromGeneratedPrefixCapital :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (child, parent : name) -> (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  {middle, finalState : SystemState name key value world error} ->
  (left : Transitions afterState middle) ->
  (right : Transitions middle finalState) ->
  (alignedStep : AlignedChildInsertStep name key world error value nameEq keyEq
    child parent component before afterState (appendTransitions left right)) ->
  RegistrationStepDiscipline protocol nameEq
    (OInsert child (ChildOf parent) component) before
    (appendTransitions left right) ->
  ActionOccurs (LUnload parent) left ->
  ActionOccurs (ORetire child) left
childRetirementFromGeneratedPrefixCapital protocol nameEq keyEq child parent
  component before afterState left right alignedStep discipline unload =
    retirementProvenanceBeforePrefixUnload nameEq keyEq parent child left right
      (childInsertTailAligned alignedStep) (snd discipline) unload
      (parentOpenAfterChildInsert protocol nameEq keyEq child parent component
        (childInsertTag alignedStep) before afterState
        (childInsertChecked alignedStep) (fst discipline))

||| Finite maximum witness used by O8. Both the chosen element and its proofs
||| are erased because O7's occurrence inventory is erased.
record MaximumBy
  (measure : item -> Nat) (items : List item) where
  constructor MkMaximumBy
  0 maximumItem : item
  0 maximumMember : Elem maximumItem items
  0 maximumUpperBound : (other : item) -> Elem other items ->
    LTE (measure other) (measure maximumItem)

0 chooseMaximumBy :
  (measure : item -> Nat) -> (head : item) -> (tail : List item) ->
  MaximumBy measure (head :: tail)
chooseMaximumBy measure head [] =
  MkMaximumBy head Here
    (\other, member => case member of
      Here => reflexive
      There later => case later of {})
chooseMaximumBy measure head (next :: later) =
  case chooseMaximumBy measure next later of
    MkMaximumBy tailMaximum tailMember tailUpper =>
      case isLTE (measure head) (measure tailMaximum) of
        Yes headBelow =>
          MkMaximumBy tailMaximum (There tailMember)
            (\other, member => case member of
              Here => headBelow
              There inTail => tailUpper other inTail)
        No headNotBelow =>
          MkMaximumBy head Here
            (\other, member => case member of
              Here => reflexive
              There inTail => transitive (tailUpper other inTail)
                (lteSuccLeft (notLTEImpliesGT headNotBelow)))

0 elemMapPreimage :
  {element : b} -> {items : List a} -> (project : a -> b) ->
  Elem element (map project items) ->
  (item : a ** (Elem item items, project item = element))
elemMapPreimage project {items = head :: tail} Here =
  (head ** (Here, Refl))
elemMapPreimage project {items = head :: tail} (There later) =
  case elemMapPreimage project later of
    (item ** (member, shape)) => (item ** (There member, shape))

0 maximalClosingOrdinalBound :
  {trace : Transitions initial finalState} ->
  (scan : ClosingEpisodeScan name key world error value nameEq keyEq trace) ->
  (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected trace) ->
  ((other : ClosingEpisodeOccurrence name key world error value nameEq keyEq
      trace) ->
    Elem other (scannedClosingOccurrences scan) ->
    LTE (scannedClosingOrdinal other)
      (transitionCount (traceBeforeOpening episode))) ->
  (consumer : name) ->
  (consumerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    consumer trace) ->
  LTE (transitionCount (traceBeforeOpening consumerEpisode))
    (transitionCount (traceBeforeOpening episode))
maximalClosingOrdinalBound scan selected episode upper consumer consumerEpisode =
  case elemMapPreimage scannedClosingOrdinal
    (everyClosingOccurrenceScanned scan consumer consumerEpisode) of
    (other ** (member, shape)) =>
      replace {p = \ordinal => LTE ordinal
        (transitionCount (traceBeforeOpening episode))}
        shape (upper other member)

0 startStrictlyBeforeLocalSuccessor :
  (start, local : Nat) -> LTE (S start) (start + S local)
startStrictlyBeforeLocalSuccessor Z local = LTESucc LTEZero
startStrictlyBeforeLocalSuccessor (S start) local =
  LTESucc (startStrictlyBeforeLocalSuccessor start local)

0 maximalClosingHasNoScopedDependent :
  {trace : Transitions initial finalState} ->
  (scan : ClosingEpisodeScan name key world error value nameEq keyEq trace) ->
  (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected trace) ->
  ((other : ClosingEpisodeOccurrence name key world error value nameEq keyEq
      trace) ->
    Elem other (scannedClosingOccurrences scan) ->
    LTE (scannedClosingOrdinal other)
      (transitionCount (traceBeforeOpening episode))) ->
  (startOrdinal : Nat) -> (startLive : GenerationEnvironment name) ->
  NoDependentClosingEpisodeForGeneration selected startOrdinal startLive episode
maximalClosingHasNoScopedDependent scan selected episode upper startOrdinal
  startLive consumer consumerEpisode scoped edge =
    LTEImpliesNotGT
      (maximalClosingOrdinalBound scan selected episode upper consumer
        consumerEpisode)
      (rewrite scopedSelectedOrdinal scoped in
       rewrite scopedConsumerOrdinal scoped in
         startStrictlyBeforeLocalSuccessor startOrdinal
           (locatedActionOrdinal (scopedConsumerOpening scoped)))

bumpGeneration : RegistrationGeneration name -> RegistrationGeneration name
bumpGeneration (MkRegistrationGeneration actor ordinal) =
  MkRegistrationGeneration actor (S ordinal)

0 prependLocatedActionOccurrence :
  (head : Transition first middle) -> (rest : Transitions middle finalState) ->
  LocatedActionOccurrence action rest ->
  LocatedActionOccurrence action (MoreTransitions head rest)
prependLocatedActionOccurrence head rest
  (MkLocatedActionOccurrence before after earlier transition later actionShape
    decomposition) =
      MkLocatedActionOccurrence before after (MoreTransitions head earlier)
        transition later actionShape (cong (MoreTransitions head) decomposition)

LocatedActionHeadView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (headTransition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  LocatedActionOccurrence action (MoreTransitions headTransition rest) -> Type
LocatedActionHeadView action headTransition rest occurrence =
  Either
    (transitionAction headTransition = action,
     locatedActionOrdinal occurrence = Z)
    (tailOccurrence : LocatedActionOccurrence action rest **
     locatedActionOrdinal occurrence = S (locatedActionOrdinal tailOccurrence))

data LocatedActionHeadExactView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (headTransition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (occurrence : LocatedActionOccurrence action
    (MoreTransitions headTransition rest)) -> Type where
  ExactLocatedActionAtHead :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, middle, finalState : SystemState name key value world error} ->
    {action : Action name key value world error} ->
    {headTransition : Transition first middle} ->
    {rest : Transitions middle finalState} ->
    {occurrence : LocatedActionOccurrence action
      (MoreTransitions headTransition rest)} ->
    (0 actionShape : transitionAction headTransition = action) ->
    (0 exactAfterState : actionAfterState occurrence = middle) ->
    (0 exactAfter : replace
      {p = \state => Transitions state finalState} exactAfterState
      (afterActionOccurrence occurrence) = rest) ->
    LocatedActionHeadExactView action headTransition rest occurrence
  ExactLocatedActionInTail :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, middle, finalState : SystemState name key value world error} ->
    {action : Action name key value world error} ->
    {headTransition : Transition first middle} ->
    {rest : Transitions middle finalState} ->
    {occurrence : LocatedActionOccurrence action
      (MoreTransitions headTransition rest)} ->
    (0 tailOccurrence : LocatedActionOccurrence action rest) ->
    (0 exactAfterState : actionAfterState occurrence =
      actionAfterState tailOccurrence) ->
    (0 exactAfter : replace
      {p = \state => Transitions state finalState} exactAfterState
      (afterActionOccurrence occurrence) =
      afterActionOccurrence tailOccurrence) ->
    LocatedActionHeadExactView action headTransition rest occurrence

0 exactLocatedActionAtHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (afterState : SystemState name key value world error) ->
  (transition : Transition first afterState) ->
  (later : Transitions afterState finalState) ->
  (0 actionShape : transitionAction transition = action) ->
  (0 decomposition : MoreTransitions transition later =
    MoreTransitions head rest) ->
  LocatedActionHeadExactView action head rest
    (MkLocatedActionOccurrence first afterState NoTransitions transition later
      actionShape decomposition)
exactLocatedActionAtHead action head rest afterState transition later
  actionShape decomposition =
    case decomposition of
      Refl => ExactLocatedActionAtHead actionShape Refl Refl

0 exactLocatedActionInTail :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, prefixMiddle, before, afterState, finalState :
    SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (prefixHead : Transition first prefixMiddle) ->
  (prefixRest : Transitions prefixMiddle before) ->
  (transition : Transition before afterState) ->
  (later : Transitions afterState finalState) ->
  (0 actionShape : transitionAction transition = action) ->
  (0 decomposition : MoreTransitions prefixHead
    (appendTransitions prefixRest (MoreTransitions transition later)) =
    MoreTransitions head rest) ->
  LocatedActionHeadExactView action head rest
    (MkLocatedActionOccurrence before afterState
      (MoreTransitions prefixHead prefixRest) transition later actionShape
      decomposition)
exactLocatedActionInTail action head rest prefixHead prefixRest transition later
  actionShape decomposition =
    case decomposition of
      Refl => ExactLocatedActionInTail
        (MkLocatedActionOccurrence _ _ prefixRest transition later actionShape
          Refl)
        Refl Refl

0 locatedActionHeadExactParts :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, before, afterState, finalState :
    SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (beforeTrace : Transitions first before) ->
  (transition : Transition before afterState) ->
  (later : Transitions afterState finalState) ->
  (0 actionShape : transitionAction transition = action) ->
  (0 decomposition : appendTransitions beforeTrace
    (MoreTransitions transition later) = MoreTransitions head rest) ->
  LocatedActionHeadExactView action head rest
    (MkLocatedActionOccurrence before afterState beforeTrace transition later
      actionShape decomposition)
locatedActionHeadExactParts action head rest NoTransitions transition later
  actionShape decomposition =
    exactLocatedActionAtHead action head rest _ transition later actionShape
      decomposition
locatedActionHeadExactParts action head rest
  (MoreTransitions prefixHead prefixRest) transition later actionShape
  decomposition =
    exactLocatedActionInTail action head rest prefixHead prefixRest transition
      later actionShape decomposition

0 locatedActionHeadExactView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (occurrence : LocatedActionOccurrence action
    (MoreTransitions head rest)) ->
  LocatedActionHeadExactView action head rest occurrence
locatedActionHeadExactView action head rest occurrence =
  case occurrence of
    MkLocatedActionOccurrence before afterState beforeTrace transition later
      actionShape decomposition =>
        locatedActionHeadExactParts action head rest beforeTrace transition later
          actionShape decomposition

0 actionOccursAtSingletonAppend :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, beforeClosing, finalState : SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (leading : Transitions first beforeClosing) ->
  (closingTransition : Transition beforeClosing finalState) ->
  (0 actionShape : transitionAction closingTransition = action) ->
  ActionOccurs action
    (appendTransitions leading
      (MoreTransitions closingTransition NoTransitions))
actionOccursAtSingletonAppend action NoTransitions closingTransition
  actionShape = ActionOccursHere closingTransition NoTransitions actionShape
actionOccursAtSingletonAppend action (MoreTransitions transition rest)
  closingTransition actionShape =
    ActionOccursLater transition _
      (actionOccursAtSingletonAppend action rest closingTransition actionShape)

0 actionOccursTraceEquality :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (left, right : Transitions first finalState) ->
  (0 exactTrace : left = right) ->
  ActionOccurs action right ->
  ActionOccurs action left
actionOccursTraceEquality action left right exactTrace occurrence =
  case exactTrace of
    Refl => occurrence

0 actionOccursAfterExact :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, finalState, targetState :
    SystemState name key value world error} ->
  {locatedAction : Action name key value world error} ->
  (action : Action name key value world error) ->
  {global : Transitions initial finalState} ->
  (occurrence : LocatedActionOccurrence locatedAction global) ->
  (targetTrace : Transitions targetState finalState) ->
  (0 exactAfterState : actionAfterState occurrence = targetState) ->
  (0 exactAfter : replace
    {p = \state => Transitions state finalState} exactAfterState
    (afterActionOccurrence occurrence) = targetTrace) ->
  ActionOccurs action targetTrace ->
  ActionOccurs action (afterActionOccurrence occurrence)
actionOccursAfterExact action occurrence targetTrace exactAfterState exactAfter
  actionOccurrence =
    case exactAfterState of
      Refl => actionOccursTraceEquality action (afterActionOccurrence occurrence)
        targetTrace exactAfter actionOccurrence

0 insertUnloadActionImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {child, selected : name} -> {scope : Parent name} ->
  {component : Component key value world error} ->
  OInsert child scope component = LUnload selected -> Void
insertUnloadActionImpossible Refl impossible

0 occurrenceAfterPrefixSpike :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {startState, actionBefore, actionAfter, finalState :
    SystemState name key value world error} ->
  (earlier : Transitions startState actionBefore) ->
  (transition : Transition actionBefore actionAfter) ->
  (later : Transitions actionAfter finalState) ->
  OccursIn transition
    (appendTransitions earlier (MoreTransitions transition later))
occurrenceAfterPrefixSpike NoTransitions transition later = OccursHere
occurrenceAfterPrefixSpike (MoreTransitions prefixHead prefixRest) transition later =
  OccursLater (occurrenceAfterPrefixSpike prefixRest transition later)

0 locatedActionImpossibleInEmpty :
  (occurrence : LocatedActionOccurrence action
    (NoTransitions {state = state})) -> Void
locatedActionImpossibleInEmpty
  (MkLocatedActionOccurrence before after earlier transition later actionShape
    decomposition) =
      noOccurrenceInEmpty
        (replace {p = \observed => OccursIn transition observed}
          decomposition (occurrenceAfterPrefixSpike earlier transition later))

mutual
  0 closingAfterLocatedInSnoc :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, beforeClosing, finalState :
      SystemState name key value world error} ->
    (locatedAction, closingAction : Action name key value world error) ->
    (leading : Transitions first beforeClosing) ->
    (closingTransition : Transition beforeClosing finalState) ->
    (0 closingShape : transitionAction closingTransition = closingAction) ->
    (0 distinct : locatedAction = closingAction -> Void) ->
    (occurrence : LocatedActionOccurrence locatedAction
      (appendTransitions leading
        (MoreTransitions closingTransition NoTransitions))) ->
    ActionOccurs closingAction (afterActionOccurrence occurrence)
  closingAfterLocatedInSnoc locatedAction closingAction NoTransitions
    closingTransition closingShape distinct occurrence =
      closingAfterLocatedSingletonView locatedAction closingAction
        closingTransition closingShape distinct occurrence
        (locatedActionHeadExactView locatedAction closingTransition NoTransitions
          occurrence)
  closingAfterLocatedInSnoc locatedAction closingAction
    (MoreTransitions leadingHead leadingRest) closingTransition closingShape
    distinct occurrence =
      closingAfterLocatedLeadingView locatedAction closingAction leadingHead
        leadingRest closingTransition closingShape distinct occurrence
        (locatedActionHeadExactView locatedAction leadingHead
          (appendTransitions leadingRest
            (MoreTransitions closingTransition NoTransitions)) occurrence)

  0 closingAfterLocatedSingletonView :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, finalState : SystemState name key value world error} ->
    (locatedAction, closingAction : Action name key value world error) ->
    (closingTransition : Transition first finalState) ->
    (0 closingShape : transitionAction closingTransition = closingAction) ->
    (0 distinct : locatedAction = closingAction -> Void) ->
    (occurrence : LocatedActionOccurrence locatedAction
      (MoreTransitions closingTransition NoTransitions)) ->
    LocatedActionHeadExactView locatedAction closingTransition NoTransitions
      occurrence ->
    ActionOccurs closingAction (afterActionOccurrence occurrence)
  closingAfterLocatedSingletonView locatedAction closingAction closingTransition
    closingShape distinct occurrence
    (ExactLocatedActionAtHead actionShape exactAfterState exactAfter) =
      void (distinct (trans (sym actionShape) closingShape))
  closingAfterLocatedSingletonView locatedAction closingAction closingTransition
    closingShape distinct occurrence
    (ExactLocatedActionInTail tailOccurrence exactAfterState exactAfter) =
      void (locatedActionImpossibleInEmpty tailOccurrence)

  0 closingAfterLocatedLeadingView :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, middle, beforeClosing, finalState :
      SystemState name key value world error} ->
    (locatedAction, closingAction : Action name key value world error) ->
    (leadingHead : Transition first middle) ->
    (leadingRest : Transitions middle beforeClosing) ->
    (closingTransition : Transition beforeClosing finalState) ->
    (0 closingShape : transitionAction closingTransition = closingAction) ->
    (0 distinct : locatedAction = closingAction -> Void) ->
    (occurrence : LocatedActionOccurrence locatedAction
      (MoreTransitions leadingHead
        (appendTransitions leadingRest
          (MoreTransitions closingTransition NoTransitions)))) ->
    LocatedActionHeadExactView locatedAction leadingHead
      (appendTransitions leadingRest
        (MoreTransitions closingTransition NoTransitions)) occurrence ->
    ActionOccurs closingAction (afterActionOccurrence occurrence)
  closingAfterLocatedLeadingView locatedAction closingAction leadingHead
    leadingRest closingTransition closingShape distinct occurrence
    (ExactLocatedActionAtHead actionShape exactAfterState exactAfter) =
      actionOccursAfterExact closingAction occurrence
        (appendTransitions leadingRest
          (MoreTransitions closingTransition NoTransitions))
        exactAfterState exactAfter
        (actionOccursAtSingletonAppend closingAction leadingRest
          closingTransition closingShape)
  closingAfterLocatedLeadingView locatedAction closingAction leadingHead
    leadingRest closingTransition closingShape distinct occurrence
    (ExactLocatedActionInTail tailOccurrence exactAfterState exactAfter) =
      actionOccursAfterExact closingAction occurrence
        (afterActionOccurrence tailOccurrence) exactAfterState exactAfter
        (closingAfterLocatedInSnoc locatedAction closingAction leadingRest
          closingTransition closingShape distinct tailOccurrence)

0 selectedClosingAfterChildBirth :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, child : name) ->
  (component : Component key value world error) ->
  {preStart, afterClose : SystemState name key value world error} ->
  (episode : ClosedEpisode name key world error value nameEq keyEq selected
    preStart afterClose) ->
  (birth : LocatedActionOccurrence
    (OInsert child (ChildOf selected) component)
    (MoreTransitions (beginTransition (closedOpening episode))
      (closedTransitions episode))) ->
  ActionOccurs (LUnload selected) (afterActionOccurrence birth)
selectedClosingAfterChildBirth nameEq keyEq selected child component episode
  birth =
    closingAfterLocatedInSnoc
      (OInsert child (ChildOf selected) component) (LUnload selected)
      (MoreTransitions (beginTransition (closedOpening episode))
        (closedInside episode))
      (unloadTransition (closing episode)) Refl insertUnloadActionImpossible birth

0 selectedChildRetirementAfterBirth :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (selected, child : name) ->
  (component : Component key value world error) ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  RegistrationDiscipline protocol nameEq global ->
  (birth : LocatedActionOccurrence
    (OInsert child (ChildOf selected) component)
    (MoreTransitions
      (beginTransition (closedOpening (locatedEpisode located)))
      (closedTransitions (locatedEpisode located)))) ->
  ActionOccurs (ORetire child) (afterActionOccurrence birth)
0 alignedChildInsertDistinct :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (child, parent : name) -> (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  {finalState : SystemState name key value world error} ->
  (rest : Transitions afterState finalState) ->
  (alignedStep : AlignedChildInsertStep name key world error value nameEq keyEq
    child parent component before afterState rest) ->
  RegistrationStepDiscipline protocol nameEq
    (OInsert child (ChildOf parent) component) before rest ->
  Not (parent = child)
alignedChildInsertDistinct protocol nameEq keyEq child parent component before
  afterState rest alignedStep discipline =
    childInsertParentDistinct nameEq keyEq child parent component
      (childInsertTag alignedStep) before afterState
      (childInsertChecked alignedStep)
      (parentOpenAtRegistrationYield protocol nameEq parent component before
        (fst discipline))

selectedChildRetirementAfterBirth protocol nameEq keyEq global selected child
  component located aligned discipline
  (MkLocatedActionOccurrence before afterState beforeTrace transition rest
    actionShape decomposition) =
      childRetirementFromGeneratedPrefixCapital protocol nameEq keyEq child
        selected component before afterState rest (traceAfterClosing located)
        (alignedGeneratedRegistrationParts nameEq keyEq global child selected
          component before afterState
          (appendTransitions (traceBeforeOpening located) beforeTrace)
          transition (appendTransitions rest (traceAfterClosing located))
          actionShape
          (registrationDecomposition
            (locatedEpisodeChildRegistration nameEq keyEq global selected child
              component located
              (MkLocatedActionOccurrence before afterState beforeTrace transition
                rest actionShape decomposition))) aligned)
        (registrationDisciplineAtGenerated protocol nameEq global child selected
          component
          (locatedEpisodeChildRegistration nameEq keyEq global selected child
            component located
            (MkLocatedActionOccurrence before afterState beforeTrace transition
              rest actionShape decomposition)) discipline)
        (selectedClosingAfterChildBirth nameEq keyEq selected child component
          (locatedEpisode located)
          (MkLocatedActionOccurrence before afterState beforeTrace transition rest
            actionShape decomposition))

0 selectedChildBirthDistinct :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (selected, child : name) ->
  (component : Component key value world error) ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  RegistrationDiscipline protocol nameEq global ->
  (birth : LocatedActionOccurrence
    (OInsert child (ChildOf selected) component)
    (MoreTransitions
      (beginTransition (closedOpening (locatedEpisode located)))
      (closedTransitions (locatedEpisode located)))) ->
  Not (selected = child)
selectedChildBirthDistinct protocol nameEq keyEq global selected child component
  located aligned discipline
  (MkLocatedActionOccurrence before afterState beforeTrace transition rest
    actionShape decomposition) =
      alignedChildInsertDistinct protocol nameEq keyEq child selected component
        before afterState (appendTransitions rest (traceAfterClosing located))
        (alignedGeneratedRegistrationParts nameEq keyEq global child selected
          component before afterState
          (appendTransitions (traceBeforeOpening located) beforeTrace)
          transition (appendTransitions rest (traceAfterClosing located))
          actionShape
          (registrationDecomposition
            (locatedEpisodeChildRegistration nameEq keyEq global selected child
              component located
              (MkLocatedActionOccurrence before afterState beforeTrace transition
                rest actionShape decomposition))) aligned)
        (registrationDisciplineAtGenerated protocol nameEq global child selected
          component
          (locatedEpisodeChildRegistration nameEq keyEq global selected child
            component located
            (MkLocatedActionOccurrence before afterState beforeTrace transition
              rest actionShape decomposition)) discipline)

0 locatedActionHeadView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {action : Action name key value world error} ->
  (head : Transition first middle) -> (rest : Transitions middle finalState) ->
  (occurrence : LocatedActionOccurrence action (MoreTransitions head rest)) ->
  LocatedActionHeadView action head rest occurrence
locatedActionHeadView head rest
  (MkLocatedActionOccurrence before after NoTransitions transition later
    actionShape decomposition) =
      case decomposition of Refl => Left (actionShape, Refl)
locatedActionHeadView head rest
  (MkLocatedActionOccurrence before after
    (MoreTransitions prefixHead prefixRest) transition later actionShape
      decomposition) =
        case decomposition of
          Refl => Right
            (MkLocatedActionOccurrence before after prefixRest transition later
              actionShape Refl ** Refl)

0 liftGenerationStamp :
  {child : name} -> {startOrdinal : Nat} -> {earlierCount : Nat} ->
  {generation : RegistrationGeneration name} ->
  generation = MkRegistrationGeneration child (startOrdinal + earlierCount) ->
  bumpGeneration generation =
    MkRegistrationGeneration child (startOrdinal + S earlierCount)
liftGenerationStamp stamp =
  trans (cong bumpGeneration stamp)
    (cong (MkRegistrationGeneration child)
      (plusSuccRightSucc startOrdinal earlierCount))

0 liftGeneratedDuring :
  (headTransition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (selected : name) -> (startOrdinal : Nat) ->
  {generation : RegistrationGeneration name} ->
  GeneratedDuring name key world error value selected startOrdinal rest generation ->
  GeneratedDuring name key world error value selected startOrdinal
    (MoreTransitions headTransition rest) (bumpGeneration generation)
liftGeneratedDuring headTransition rest selected startOrdinal
  (MkGeneratedDuring child component
    (MkLocatedActionOccurrence before after earlier transition later actionShape
      decomposition)
    stamp retiresLater) =
      MkGeneratedDuring child component
        (MkLocatedActionOccurrence before after
          (MoreTransitions headTransition earlier) transition later actionShape
          (cong (MoreTransitions headTransition) decomposition))
        (liftGenerationStamp stamp) retiresLater

record ChildGenerationInventory
  (name, key, world, error : Type) (value : key -> Type)
  (selected : name) (startOrdinal : Nat)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState) where
  constructor MkChildGenerationInventory
  selectedGenerations : List (RegistrationGeneration name)
  0 selectedGenerationSound :
    (generation : RegistrationGeneration name) ->
    Elem generation selectedGenerations ->
    GeneratedDuring name key world error value selected startOrdinal trace
      generation
  0 selectedGenerationComplete :
    (child : name) -> (component : Component key value world error) ->
    (birth : LocatedActionOccurrence
      (OInsert child (ChildOf selected) component) trace) ->
    Elem (MkRegistrationGeneration child
      (startOrdinal + locatedActionOrdinal birth)) selectedGenerations

0 registeredDuringFromInventory :
  (inventory : ChildGenerationInventory name key world error value selected
    startOrdinal trace) ->
  RegisteredGenerationsDuring selected startOrdinal
    (selectedGenerations inventory) trace
registeredDuringFromInventory inventory =
  (selectedGenerationSound inventory, selectedGenerationComplete inventory)

0 selectedInventoryOutside :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (selected : name) ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  RegistrationDiscipline protocol nameEq global ->
  (startOrdinal : Nat) ->
  (inventory : ChildGenerationInventory name key world error value selected
    startOrdinal
    (MoreTransitions
      (beginTransition (closedOpening (locatedEpisode located)))
      (closedTransitions (locatedEpisode located)))) ->
  (generation : RegistrationGeneration name) ->
  Elem generation (selectedGenerations inventory) ->
  Not (generationName generation = selected)
selectedInventoryOutside protocol nameEq keyEq global selected located aligned
  discipline startOrdinal inventory generation member same =
    case selectedGenerationSound inventory generation member of
      MkGeneratedDuring child component birth stamp retiresLater =>
        selectedChildBirthDistinct protocol nameEq keyEq global selected child
          component located aligned discipline birth
          (sym (trans (sym (cong generationName stamp)) same))

0 liftedInventorySound :
  (headTransition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (selected : name) -> (startOrdinal : Nat) ->
  (tailGenerations : List (RegistrationGeneration name)) ->
  ((generation : RegistrationGeneration name) ->
    Elem generation tailGenerations ->
    GeneratedDuring name key world error value selected startOrdinal rest
      generation) ->
  (generation : RegistrationGeneration name) ->
  Elem generation (map DGamma.CP5ConfluenceDeletionChainSpike.bumpGeneration tailGenerations) ->
  GeneratedDuring name key world error value selected startOrdinal
    (MoreTransitions headTransition rest) generation
liftedInventorySound headTransition rest selected startOrdinal tailGenerations
  tailSound generation member =
    case elemMapPreimage DGamma.CP5ConfluenceDeletionChainSpike.bumpGeneration member of
      (tailGeneration ** (tailMember, shape)) =>
        replace {p = \candidate => GeneratedDuring name key world error value
          selected startOrdinal (MoreTransitions headTransition rest) candidate}
          shape (liftGeneratedDuring headTransition rest selected startOrdinal
            (tailSound tailGeneration tailMember))

0 liftedInventoryComplete :
  (headTransition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (selected : name) -> (startOrdinal : Nat) ->
  ((child : name) -> (component : Component key value world error) ->
    transitionAction headTransition =
      OInsert child (ChildOf selected) component -> Void) ->
  (tailGenerations : List (RegistrationGeneration name)) ->
  ((child : name) -> (component : Component key value world error) ->
    (birth : LocatedActionOccurrence
      (OInsert child (ChildOf selected) component) rest) ->
    Elem (MkRegistrationGeneration child
      (startOrdinal + locatedActionOrdinal birth)) tailGenerations) ->
  (child : name) -> (component : Component key value world error) ->
  (birth : LocatedActionOccurrence
    (OInsert child (ChildOf selected) component)
    (MoreTransitions headTransition rest)) ->
  Elem (MkRegistrationGeneration child
    (startOrdinal + locatedActionOrdinal birth))
    (map DGamma.CP5ConfluenceDeletionChainSpike.bumpGeneration tailGenerations)
liftedInventoryComplete headTransition rest selected startOrdinal headImpossible
  tailGenerations tailComplete child component birth =
    case locatedActionHeadView headTransition rest birth of
      Left (actionShape, ordinalShape) =>
        void (headImpossible child component actionShape)
      Right (tailBirth ** ordinalShape) =>
        replace
          {p = \ordinal => Elem (MkRegistrationGeneration child
            (startOrdinal + ordinal)) (map DGamma.CP5ConfluenceDeletionChainSpike.bumpGeneration tailGenerations)}
          (sym ordinalShape)
          (replace
            {p = \ordinal => Elem (MkRegistrationGeneration child ordinal)
              (map DGamma.CP5ConfluenceDeletionChainSpike.bumpGeneration tailGenerations)}
            (plusSuccRightSucc startOrdinal
              (locatedActionOrdinal tailBirth))
            (elemMap DGamma.CP5ConfluenceDeletionChainSpike.bumpGeneration
              (tailComplete child component tailBirth)))

0 prependChildInventoryWithoutMatch :
  (headTransition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (selected : name) -> (startOrdinal : Nat) ->
  ((child : name) -> (component : Component key value world error) ->
    transitionAction headTransition =
      OInsert child (ChildOf selected) component -> Void) ->
  ChildGenerationInventory name key world error value selected startOrdinal rest ->
  ChildGenerationInventory name key world error value selected startOrdinal
    (MoreTransitions headTransition rest)
prependChildInventoryWithoutMatch headTransition rest selected startOrdinal
  headImpossible
  (MkChildGenerationInventory tailGenerations tailSound tailComplete) =
    MkChildGenerationInventory
      (map DGamma.CP5ConfluenceDeletionChainSpike.bumpGeneration tailGenerations)
      (liftedInventorySound headTransition rest selected startOrdinal
        tailGenerations tailSound)
      (liftedInventoryComplete headTransition rest selected startOrdinal
        headImpossible tailGenerations tailComplete)

0 headChildBirth :
  (headTransition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (selected, child : name) ->
  (component : Component key value world error) ->
  transitionAction headTransition =
    OInsert child (ChildOf selected) component ->
  LocatedActionOccurrence (OInsert child (ChildOf selected) component)
    (MoreTransitions headTransition rest)
headChildBirth headTransition rest selected child component actionShape =
  replace
    {p = \observedAction => LocatedActionOccurrence observedAction
      (MoreTransitions headTransition rest)}
    actionShape
    (occursInGivesLocatedAction headTransition
      (MoreTransitions headTransition rest) OccursHere)

0 headChildGenerated :
  (headTransition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (selected, child : name) ->
  (component : Component key value world error) ->
  (startOrdinal : Nat) ->
  (actionShape : transitionAction headTransition =
    OInsert child (ChildOf selected) component) ->
  ((registered : name) ->
    (registeredComponent : Component key value world error) ->
    (birth : LocatedActionOccurrence
      (OInsert registered (ChildOf selected) registeredComponent)
      (MoreTransitions headTransition rest)) ->
    ActionOccurs (ORetire registered) (afterActionOccurrence birth)) ->
  GeneratedDuring name key world error value selected startOrdinal
    (MoreTransitions headTransition rest)
    (MkRegistrationGeneration child startOrdinal)
headChildGenerated headTransition rest selected child component startOrdinal
  actionShape allRetire =
    MkGeneratedDuring child component
      (headChildBirth headTransition rest selected child component actionShape)
      (cong (MkRegistrationGeneration child)
        (sym (plusZeroRightNeutral startOrdinal)))
      (allRetire child component
        (headChildBirth headTransition rest selected child component actionShape))

0 matchingInventorySound :
  (headTransition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (selected, child : name) ->
  (component : Component key value world error) ->
  (startOrdinal : Nat) ->
  (actionShape : transitionAction headTransition =
    OInsert child (ChildOf selected) component) ->
  ((registered : name) ->
    (registeredComponent : Component key value world error) ->
    (birth : LocatedActionOccurrence
      (OInsert registered (ChildOf selected) registeredComponent)
      (MoreTransitions headTransition rest)) ->
    ActionOccurs (ORetire registered) (afterActionOccurrence birth)) ->
  (tailGenerations : List (RegistrationGeneration name)) ->
  ((generation : RegistrationGeneration name) ->
    Elem generation tailGenerations ->
    GeneratedDuring name key world error value selected startOrdinal rest
      generation) ->
  (generation : RegistrationGeneration name) ->
  Elem generation
    (MkRegistrationGeneration child startOrdinal ::
      map DGamma.CP5ConfluenceDeletionChainSpike.bumpGeneration
        tailGenerations) ->
  GeneratedDuring name key world error value selected startOrdinal
    (MoreTransitions headTransition rest) generation
matchingInventorySound headTransition rest selected child component startOrdinal
  actionShape allRetire tailGenerations tailSound _ Here =
    headChildGenerated headTransition rest selected child component startOrdinal
      actionShape allRetire
matchingInventorySound headTransition rest selected child component startOrdinal
  actionShape allRetire tailGenerations tailSound generation (There later) =
    liftedInventorySound headTransition rest selected startOrdinal
      tailGenerations tailSound generation later

0 matchingHeadComplete :
  {registered, child, selected : name} ->
  {registeredComponent, component : Component key value world error} ->
  {headOrdinal : Nat} -> {startOrdinal : Nat} ->
  {tailGenerations : List (RegistrationGeneration name)} ->
  OInsert child (ChildOf selected) component =
    OInsert registered (ChildOf selected) registeredComponent ->
  headOrdinal = Z ->
  Elem (MkRegistrationGeneration registered (startOrdinal + headOrdinal))
    (MkRegistrationGeneration child startOrdinal :: tailGenerations)
matchingHeadComplete actionShape ordinalShape =
  case actionShape of
    Refl => rewrite ordinalShape in
      rewrite plusZeroRightNeutral startOrdinal in Here

0 matchingInventoryComplete :
  (headTransition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (selected, child : name) ->
  (component : Component key value world error) ->
  (startOrdinal : Nat) ->
  (actionShape : transitionAction headTransition =
    OInsert child (ChildOf selected) component) ->
  (tailGenerations : List (RegistrationGeneration name)) ->
  ((registered : name) ->
    (registeredComponent : Component key value world error) ->
    (birth : LocatedActionOccurrence
      (OInsert registered (ChildOf selected) registeredComponent) rest) ->
    Elem (MkRegistrationGeneration registered
      (startOrdinal + locatedActionOrdinal birth)) tailGenerations) ->
  (registered : name) ->
  (registeredComponent : Component key value world error) ->
  (birth : LocatedActionOccurrence
    (OInsert registered (ChildOf selected) registeredComponent)
    (MoreTransitions headTransition rest)) ->
  Elem (MkRegistrationGeneration registered
    (startOrdinal + locatedActionOrdinal birth))
    (MkRegistrationGeneration child startOrdinal ::
      map DGamma.CP5ConfluenceDeletionChainSpike.bumpGeneration
        tailGenerations)
matchingInventoryComplete headTransition rest selected child component
  startOrdinal actionShape tailGenerations tailComplete registered
  registeredComponent birth =
    case locatedActionHeadView headTransition rest birth of
      Left (atHeadShape, ordinalShape) =>
        matchingHeadComplete (trans (sym actionShape) atHeadShape) ordinalShape
      Right (tailBirth ** ordinalShape) =>
        replace
          {p = \ordinal => Elem (MkRegistrationGeneration registered
            (startOrdinal + ordinal))
            (MkRegistrationGeneration child startOrdinal ::
              map DGamma.CP5ConfluenceDeletionChainSpike.bumpGeneration
                tailGenerations)}
          (sym ordinalShape)
          (There
            (replace
              {p = \ordinal => Elem (MkRegistrationGeneration registered ordinal)
                (map DGamma.CP5ConfluenceDeletionChainSpike.bumpGeneration
                  tailGenerations)}
              (plusSuccRightSucc startOrdinal
                (locatedActionOrdinal tailBirth))
              (elemMap DGamma.CP5ConfluenceDeletionChainSpike.bumpGeneration
                (tailComplete registered registeredComponent tailBirth))))

0 prependMatchingChildInventory :
  (headTransition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (selected, child : name) ->
  (component : Component key value world error) ->
  (startOrdinal : Nat) ->
  (actionShape : transitionAction headTransition =
    OInsert child (ChildOf selected) component) ->
  ((registered : name) ->
    (registeredComponent : Component key value world error) ->
    (birth : LocatedActionOccurrence
      (OInsert registered (ChildOf selected) registeredComponent)
      (MoreTransitions headTransition rest)) ->
    ActionOccurs (ORetire registered) (afterActionOccurrence birth)) ->
  ChildGenerationInventory name key world error value selected startOrdinal rest ->
  ChildGenerationInventory name key world error value selected startOrdinal
    (MoreTransitions headTransition rest)
prependMatchingChildInventory headTransition rest selected child component
  startOrdinal actionShape allRetire
  (MkChildGenerationInventory tailGenerations tailSound tailComplete) =
    MkChildGenerationInventory
      (MkRegistrationGeneration child startOrdinal ::
        map DGamma.CP5ConfluenceDeletionChainSpike.bumpGeneration
          tailGenerations)
      (matchingInventorySound headTransition rest selected child component
        startOrdinal actionShape allRetire tailGenerations tailSound)
      (matchingInventoryComplete headTransition rest selected child component
        startOrdinal actionShape tailGenerations tailComplete)

0 tailRetirementRequirement :
  (headTransition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  ((registered : name) ->
    (registeredComponent : Component key value world error) ->
    (birth : LocatedActionOccurrence
      (OInsert registered (ChildOf selected) registeredComponent)
      (MoreTransitions headTransition rest)) ->
    ActionOccurs (ORetire registered) (afterActionOccurrence birth)) ->
  (registered : name) ->
  (registeredComponent : Component key value world error) ->
  (tailBirth : LocatedActionOccurrence
    (OInsert registered (ChildOf selected) registeredComponent) rest) ->
  ActionOccurs (ORetire registered) (afterActionOccurrence tailBirth)
tailRetirementRequirement headTransition rest allRetire registered
  registeredComponent
  (MkLocatedActionOccurrence before after earlier transition later actionShape
    decomposition) =
      allRetire registered registeredComponent
        (MkLocatedActionOccurrence before after
          (MoreTransitions headTransition earlier) transition later actionShape
          (cong (MoreTransitions headTransition) decomposition))

public export
record ClosingTailWitnessSpike
  (name, key, world, error : Type) (value : key -> Type)
  (action : Action name key value world error)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState) where
  constructor MkClosingTailWitnessSpike
  endingStartSpike : SystemState name key value world error
  beforeEndingSpike : Transitions first endingStartSpike
  endingTransitionSpike : Transition endingStartSpike finalState
  0 endingActionSpike : transitionAction endingTransitionSpike = action
  0 endingDecompositionSpike : appendTransitions beforeEndingSpike
    (MoreTransitions endingTransitionSpike NoTransitions) = trace

public export
prependClosingTailWitnessSpike :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {action : Action name key value world error} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (leading : Transitions first middle) ->
  {suffix : Transitions middle finalState} ->
  ClosingTailWitnessSpike name key world error value action suffix ->
  ClosingTailWitnessSpike name key world error value action
    (appendTransitions leading suffix)
prependClosingTailWitnessSpike leading
  (MkClosingTailWitnessSpike endingStart beforeEnding endingTransition actionShape
    decomposition) =
      MkClosingTailWitnessSpike endingStart
        (appendTransitions leading beforeEnding) endingTransition actionShape
        (trans (appendTransitionsAssociative leading beforeEnding
          (MoreTransitions endingTransition NoTransitions))
          (cong (appendTransitions leading) decomposition))

0 childParentsFromInsertEquality :
  OInsert child (ChildOf parent) component =
    OInsert registered (ChildOf selected) registeredComponent ->
  parent = selected
childParentsFromInsertEquality Refl = Refl

0 nonMatchingChildHeadImpossible :
  (headTransition : Transition first middle) ->
  (child, parent : name) ->
  (component : Component key value world error) ->
  transitionAction headTransition =
    OInsert child (ChildOf parent) component ->
  (parent = selected -> Void) ->
  (registered : name) ->
  (registeredComponent : Component key value world error) ->
  transitionAction headTransition =
    OInsert registered (ChildOf selected) registeredComponent ->
  Void
nonMatchingChildHeadImpossible headTransition child parent component headAction
  distinct registered registeredComponent actionShape =
    distinct (childParentsFromInsertEquality
      (trans (sym headAction) actionShape))

0 buildChildGenerationInventory :
  (nameEq : DecEq name) -> (selected : name) -> (startOrdinal : Nat) ->
  (trace : Transitions first finalState) ->
  ((child : name) -> (component : Component key value world error) ->
    (birth : LocatedActionOccurrence
      (OInsert child (ChildOf selected) component) trace) ->
    ActionOccurs (ORetire child) (afterActionOccurrence birth)) ->
  ChildGenerationInventory name key world error value selected startOrdinal trace
buildChildGenerationInventory nameEq selected startOrdinal NoTransitions allRetire =
  MkChildGenerationInventory []
    (\generation, member => absurd member)
    (\child, component, birth => void (locatedActionImpossibleInEmpty birth))
buildChildGenerationInventory nameEq selected startOrdinal
  (MoreTransitions (Fired stepNameEq stepKeyEq
    (OInsert child Root component) tag checked) rest) allRetire =
      prependChildInventoryWithoutMatch
        (Fired stepNameEq stepKeyEq (OInsert child Root component) tag checked)
        rest selected startOrdinal
        (\registered, registeredComponent, actionShape =>
          case actionShape of Refl impossible)
        (buildChildGenerationInventory nameEq selected startOrdinal rest
          (tailRetirementRequirement
            (Fired stepNameEq stepKeyEq
              (OInsert child Root component) tag checked)
            rest allRetire))
buildChildGenerationInventory nameEq selected startOrdinal
  (MoreTransitions (Fired stepNameEq stepKeyEq
    (OInsert child (ChildOf parent) component) tag checked) rest) allRetire =
      case decEq @{nameEq} parent selected of
        Yes parentShape => case parentShape of
          Refl => prependMatchingChildInventory
            (Fired stepNameEq stepKeyEq
              (OInsert child (ChildOf selected) component) tag checked)
            rest selected child component startOrdinal Refl allRetire
            (buildChildGenerationInventory nameEq selected startOrdinal rest
              (tailRetirementRequirement
                (Fired stepNameEq stepKeyEq
                  (OInsert child (ChildOf selected) component) tag checked)
                rest allRetire))
        No distinct =>
          prependChildInventoryWithoutMatch
            (Fired stepNameEq stepKeyEq
              (OInsert child (ChildOf parent) component) tag checked)
            rest selected startOrdinal
            (nonMatchingChildHeadImpossible
              (Fired stepNameEq stepKeyEq
                (OInsert child (ChildOf parent) component) tag checked)
              child parent component Refl distinct)
            (buildChildGenerationInventory nameEq selected startOrdinal rest
              (tailRetirementRequirement
                (Fired stepNameEq stepKeyEq
                  (OInsert child (ChildOf parent) component) tag checked)
                rest allRetire))
buildChildGenerationInventory nameEq selected startOrdinal
  (MoreTransitions (Fired stepNameEq stepKeyEq
    (ORetire actor) tag checked) rest) allRetire =
    prependChildInventoryWithoutMatch
      (Fired stepNameEq stepKeyEq (ORetire actor) tag checked) rest selected
      startOrdinal
      (\child, component, shape => case shape of Refl impossible)
      (buildChildGenerationInventory nameEq selected startOrdinal rest
        (tailRetirementRequirement
          (Fired stepNameEq stepKeyEq (ORetire actor) tag checked) rest
          allRetire))
buildChildGenerationInventory nameEq selected startOrdinal
  (MoreTransitions (Fired stepNameEq stepKeyEq
    (ORemove actor) tag checked) rest) allRetire =
    prependChildInventoryWithoutMatch
      (Fired stepNameEq stepKeyEq (ORemove actor) tag checked) rest selected
      startOrdinal
      (\child, component, shape => case shape of Refl impossible)
      (buildChildGenerationInventory nameEq selected startOrdinal rest
        (tailRetirementRequirement
          (Fired stepNameEq stepKeyEq (ORemove actor) tag checked) rest
          allRetire))
buildChildGenerationInventory nameEq selected startOrdinal
  (MoreTransitions (Fired stepNameEq stepKeyEq
    (LBegin actor) tag checked) rest) allRetire =
    prependChildInventoryWithoutMatch
      (Fired stepNameEq stepKeyEq (LBegin actor) tag checked) rest selected
      startOrdinal
      (\child, component, shape => case shape of Refl impossible)
      (buildChildGenerationInventory nameEq selected startOrdinal rest
        (tailRetirementRequirement
          (Fired stepNameEq stepKeyEq (LBegin actor) tag checked) rest
          allRetire))
buildChildGenerationInventory nameEq selected startOrdinal
  (MoreTransitions (Fired stepNameEq stepKeyEq
    (LAdvance actor) tag checked) rest) allRetire =
    prependChildInventoryWithoutMatch
      (Fired stepNameEq stepKeyEq (LAdvance actor) tag checked) rest selected
      startOrdinal
      (\child, component, shape => case shape of Refl impossible)
      (buildChildGenerationInventory nameEq selected startOrdinal rest
        (tailRetirementRequirement
          (Fired stepNameEq stepKeyEq (LAdvance actor) tag checked) rest
          allRetire))
buildChildGenerationInventory nameEq selected startOrdinal
  (MoreTransitions (Fired stepNameEq stepKeyEq
    (LDivert actor) tag checked) rest) allRetire =
    prependChildInventoryWithoutMatch
      (Fired stepNameEq stepKeyEq (LDivert actor) tag checked) rest selected
      startOrdinal
      (\child, component, shape => case shape of Refl impossible)
      (buildChildGenerationInventory nameEq selected startOrdinal rest
        (tailRetirementRequirement
          (Fired stepNameEq stepKeyEq (LDivert actor) tag checked) rest
          allRetire))
buildChildGenerationInventory nameEq selected startOrdinal
  (MoreTransitions (Fired stepNameEq stepKeyEq
    (LLeave actor) tag checked) rest) allRetire =
    prependChildInventoryWithoutMatch
      (Fired stepNameEq stepKeyEq (LLeave actor) tag checked) rest selected
      startOrdinal
      (\child, component, shape => case shape of Refl impossible)
      (buildChildGenerationInventory nameEq selected startOrdinal rest
        (tailRetirementRequirement
          (Fired stepNameEq stepKeyEq (LLeave actor) tag checked) rest
          allRetire))
buildChildGenerationInventory nameEq selected startOrdinal
  (MoreTransitions (Fired stepNameEq stepKeyEq
    (LUnload actor) tag checked) rest) allRetire =
    prependChildInventoryWithoutMatch
      (Fired stepNameEq stepKeyEq (LUnload actor) tag checked) rest selected
      startOrdinal
      (\child, component, shape => case shape of Refl impossible)
      (buildChildGenerationInventory nameEq selected startOrdinal rest
        (tailRetirementRequirement
          (Fired stepNameEq stepKeyEq (LUnload actor) tag checked) rest
          allRetire))

0 retiredAfterRetireSpike :
  (fiber : Fiber name key value world error) ->
  retired (retireFiber fiber) = True
retiredAfterRetireSpike
  (MkFiber component parent retiredFlag table lifecycle) = Refl

0 trueFlagInactiveBeginNothing :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (state : SystemState name key value world error) ->
  retiredFlag = True ->
  beginFiberAction @{nameEq} @{keyEq} actor
    (MkFiber component parent retiredFlag table (Inactive Nothing)) state = Nothing
trueFlagInactiveBeginNothing nameEq keyEq actor component parent _ table state
  Refl = Refl

0 retiredLifecycleBeginNothing :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (state : SystemState name key value world error) ->
  retiredFlag = True ->
  beginFiberAction @{nameEq} @{keyEq} actor
    (MkFiber component parent retiredFlag table lifecycle) state = Nothing
retiredLifecycleBeginNothing nameEq keyEq actor component parent retiredFlag table
  (Inactive Nothing) state retiredTrue =
    trueFlagInactiveBeginNothing nameEq keyEq actor component parent retiredFlag
      table state retiredTrue
retiredLifecycleBeginNothing nameEq keyEq actor component parent retiredFlag table
  (Inactive (Just failure)) state retiredTrue = Refl
retiredLifecycleBeginNothing nameEq keyEq actor component parent retiredFlag table
  (Reloading remaining accumulator view) state retiredTrue = Refl
retiredLifecycleBeginNothing nameEq keyEq actor component parent retiredFlag table
  (Active accumulator view) state retiredTrue = Refl
retiredLifecycleBeginNothing nameEq keyEq actor component parent retiredFlag table
  (Unloading accumulator view outcome) state retiredTrue = Refl

0 retiredFiberBeginNothing :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) ->
  (fiber : Fiber name key value world error) ->
  (state : SystemState name key value world error) ->
  retired fiber = True ->
  beginFiberAction @{nameEq} @{keyEq} actor fiber state = Nothing
retiredFiberBeginNothing nameEq keyEq actor
  (MkFiber component parent retiredFlag table lifecycle) state retiredTrue =
    retiredLifecycleBeginNothing nameEq keyEq actor component parent retiredFlag
      table lifecycle state retiredTrue

0 applyBeginAtFoundSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor fibers = Just fiber ->
  applyAction @{nameEq} @{keyEq} (LBegin actor)
    (MkSystemState ambient fibers) =
  beginFiberAction @{nameEq} @{keyEq} actor fiber
    (MkSystemState ambient fibers)
applyBeginAtFoundSpike nameEq keyEq actor ambient fibers fiber found =
  rewrite found in Refl

0 beginEquationFromApplySpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor fibers = Just fiber ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (LBegin actor)
    (MkSystemState ambient fibers) = Just (tag, afterState) ->
  beginFiberAction @{nameEq} @{keyEq} actor fiber
    (MkSystemState ambient fibers) = Just (tag, afterState)
beginEquationFromApplySpike nameEq keyEq actor ambient fibers fiber found tag
  afterState raw =
    trans (sym (applyBeginAtFoundSpike nameEq keyEq actor ambient fibers fiber
      found)) raw

0 nothingCannotEqualJustSpike : Nothing = Just value -> Void
nothingCannotEqualJustSpike Refl impossible

0 retiredCannotBeginState :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LBegin actor) before =
    Just (tag, afterState) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor (registry before) = Just fiber ->
  retired fiber = True -> Void
retiredCannotBeginState nameEq keyEq actor (MkSystemState ambient fibers)
  afterState tag raw fiber found retiredTrue =
    nothingCannotEqualJustSpike
      (trans (sym (retiredFiberBeginNothing nameEq keyEq actor fiber
        (MkSystemState ambient fibers) retiredTrue))
        (beginEquationFromApplySpike nameEq keyEq actor ambient fibers fiber found
          tag afterState raw))

0 retiredCannotBeginSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LBegin actor) before =
    Just (tag, afterState) ->
  (fiber : Fiber name key value world error **
    (lookupFiber @{nameEq} actor (registry before) = Just fiber,
     retired fiber = True)) -> Void
retiredCannotBeginSpike nameEq keyEq actor before afterState tag raw
  (fiber ** (found, retiredTrue)) =
    retiredCannotBeginState nameEq keyEq actor before afterState tag raw fiber
      found retiredTrue

record RetireTargetLookupView
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (actor : name)
  (afterState : SystemState name key value world error) where
  constructor MkRetireTargetLookupView
  retiredTargetFiber : Fiber name key value world error
  0 retiredTargetFound : lookupFiber @{nameEq} actor (registry afterState) =
    Just retiredTargetFiber
  0 retiredTargetTrue : retired retiredTargetFiber = True

0 retireLookupMissingAction :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (0 missing : lookupFiber @{nameEq} {key = key} {value = value}
    {world = world} {error = error} actor source =
    the (Maybe (Fiber name key value world error)) Nothing) ->
  applyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} (ORetire actor)
    (MkSystemState ambient source) = Nothing
retireLookupMissingAction nameEq keyEq actor ambient source missing =
  rewrite missing in Refl

0 retireFoundTargetView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (oldFiber : Fiber name key value world error) ->
  (0 found : lookupFiber @{nameEq} actor source = Just oldFiber) ->
  (tag : RuleTag) ->
  (afterState : SystemState name key value world error) ->
  (0 raw : applyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} (ORetire actor)
    (MkSystemState ambient source) = Just (tag, afterState)) ->
  RetireTargetLookupView name key world error value nameEq actor afterState
retireFoundTargetView nameEq keyEq actor ambient source oldFiber found tag
  afterState raw =
    replace
      {p = \candidate => RetireTargetLookupView name key world error value
        nameEq actor candidate}
      (cong snd (justInjective (trans
        (sym (retireActionAtFoundSpike nameEq keyEq actor ambient source oldFiber
          found)) raw)))
      (MkRetireTargetLookupView (retireFiber oldFiber)
        (lookupReplacedFiber actor oldFiber (retireFiber oldFiber) source found)
        (retiredAfterRetireSpike oldFiber))

0 retireTransitionTargetRegistryView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (tag : RuleTag) ->
  (afterState : SystemState name key value world error) ->
  (0 raw : applyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} (ORetire actor)
    (MkSystemState ambient source) = Just (tag, afterState)) ->
  RetireTargetLookupView name key world error value nameEq actor afterState
retireTransitionTargetRegistryView nameEq keyEq actor ambient source tag
  afterState raw =
    case parentEndpointLookupEquation nameEq actor
      (MkSystemState ambient source) of
        ParentEndpointLookupMissing missing missingReloading missingActive =>
          void (nothingCannotEqualJustSpike (trans
            (sym (retireLookupMissingAction nameEq keyEq actor ambient source
              missing)) raw))
        ParentEndpointLookupFound fiber found foundReloading foundActive =>
          retireFoundTargetView nameEq keyEq actor ambient source fiber found tag
            afterState raw

0 retireTransitionTargetView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (0 raw : applyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} (ORetire actor) before =
    Just (tag, afterState)) ->
  RetireTargetLookupView name key world error value nameEq actor afterState
retireTransitionTargetView nameEq keyEq actor (MkSystemState ambient source)
  afterState tag raw =
    retireTransitionTargetRegistryView nameEq keyEq actor ambient source tag
      afterState raw

0 rawRetireFromActionShape :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) ->
  (action : Action name key value world error) ->
  (0 actionShape : action = ORetire child) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (0 raw : applyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  applyAction @{nameEq} @{keyEq} (ORetire child) before =
    Just (tag, afterState)
rawRetireFromActionShape nameEq keyEq child action actionShape before afterState
  tag raw =
    replace {p = \candidate => applyAction @{nameEq} @{keyEq} candidate before =
      Just (tag, afterState)} actionShape raw

data RetiredRegistryLookupView :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (actor : name) ->
  (target : Registry name key value world error) -> Type where
  RetiredRegistryLookupPresent :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {target : Registry name key value world error} ->
    (0 fiber : Fiber name key value world error) ->
    (0 found : lookupFiber @{nameEq} actor target = Just fiber) ->
    (0 retiredTrue : retired fiber = True) ->
    RetiredRegistryLookupView name key world error value nameEq actor target
  RetiredRegistryLookupMissing :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {target : Registry name key value world error} ->
    (0 missing : lookupFiber @{nameEq} actor target =
      the (Maybe (Fiber name key value world error)) Nothing) ->
    RetiredRegistryLookupView name key world error value nameEq actor target

0 retirementUpdateKeepsTrue :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (old, updated : Fiber name key value world error) ->
  RetirementUpdate old updated -> retired old = True -> retired updated = True
retirementUpdateKeepsTrue old updated (RetirementStable same) oldTrue =
  trans same oldTrue
retirementUpdateKeepsTrue old updated (RetirementApplied updatedTrue) oldTrue =
  updatedTrue

0 retiredReplaceRegistryView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (source : Registry name key value world error) ->
  (updated, oldFiber, retiredFiber : Fiber name key value world error) ->
  (0 oldFound : lookupFiber @{nameEq} actor source = Just oldFiber) ->
  (0 update : RetirementUpdate oldFiber updated) ->
  (0 retiredFound : lookupFiber @{nameEq} actor source = Just retiredFiber) ->
  (0 retiredTrue : retired retiredFiber = True) ->
  RetiredRegistryLookupView name key world error value nameEq actor
    (replaceBinding @{nameEq} actor updated source)
retiredReplaceRegistryView nameEq actor source updated oldFiber retiredFiber
  oldFound update retiredFound retiredTrue =
    case justInjective (trans (sym oldFound) retiredFound) of
      Refl => RetiredRegistryLookupPresent updated
        (lookupReplacedFiber actor retiredFiber updated source retiredFound)
        (retirementUpdateKeepsTrue retiredFiber updated update retiredTrue)

0 retiredAcrossRegistryUpdate :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (source, target : Registry name key value world error) ->
  RegistryLocalUpdate name key world error value nameEq actor source target ->
  (retiredFiber : Fiber name key value world error) ->
  (0 retiredFound : lookupFiber @{nameEq} actor source = Just retiredFiber) ->
  (0 retiredTrue : retired retiredFiber = True) ->
  RetiredRegistryLookupView name key world error value nameEq actor target
retiredAcrossRegistryUpdate nameEq actor source
  (insertBinding @{nameEq} actor inserted source absent)
  (LocalInsert inserted absent) retiredFiber retiredFound retiredTrue =
    void (nothingCannotEqualJustSpike (trans (sym absent) retiredFound))
retiredAcrossRegistryUpdate nameEq actor source
  (replaceBinding @{nameEq} actor updated source)
  (LocalReplace {oldFiber} @{oldFound} @{staticComponent} @{staticParent}
    @{retirementUpdate} updated) retiredFiber retiredFound retiredTrue =
    retiredReplaceRegistryView nameEq actor source updated oldFiber retiredFiber
      oldFound retirementUpdate retiredFound retiredTrue
retiredAcrossRegistryUpdate nameEq actor source
  (deleteBinding @{nameEq} actor source) LocalDelete retiredFiber retiredFound
  retiredTrue =
    RetiredRegistryLookupMissing
      (DGamma.CP4DeletionSelectedOwn.lookupDeleteSelf actor source)

0 retiredForeignActionStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (action : Action name key value world error) ->
  (0 distinct : Not (actor = actionOwner action)) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (0 raw : applyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (retiredFiber : Fiber name key value world error) ->
  (0 retiredFound : lookupFiber @{nameEq} actor (registry before) =
    Just retiredFiber) ->
  (0 retiredTrue : retired retiredFiber = True) ->
  RetiredRegistryLookupView name key world error value nameEq actor
    (registry afterState)
retiredForeignActionStep nameEq keyEq actor action distinct before afterState tag
  raw retiredFiber retiredFound retiredTrue =
    RetiredRegistryLookupPresent retiredFiber
      (trans (systemLocalUpdateForeign nameEq actor (actionOwner action) distinct
        before afterState (applyActionLocalUpdate nameEq keyEq action before
          afterState tag raw)) retiredFound) retiredTrue

0 retiredOwnerSourceFound :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor, owner : name) ->
  (0 same : actor = owner) ->
  (source : Registry name key value world error) ->
  (fiber : Fiber name key value world error) ->
  (0 found : lookupFiber @{nameEq} actor source = Just fiber) ->
  lookupFiber @{nameEq} owner source = Just fiber
retiredOwnerSourceFound nameEq actor owner same source fiber found =
  replace {p = \candidate => lookupFiber @{nameEq} candidate source =
    Just fiber} same found

0 retiredOwnerTargetReindex :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor, owner : name) ->
  (0 same : actor = owner) ->
  (target : Registry name key value world error) ->
  RetiredRegistryLookupView name key world error value nameEq owner target ->
  RetiredRegistryLookupView name key world error value nameEq actor target
retiredOwnerTargetReindex nameEq actor owner same target ownerView =
  replace {p = \candidate => RetiredRegistryLookupView name key world error
    value nameEq candidate target} (sym same) ownerView

0 retiredOwnerActionStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (action : Action name key value world error) ->
  (0 same : actor = actionOwner action) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (0 raw : applyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (retiredFiber : Fiber name key value world error) ->
  (0 retiredFound : lookupFiber @{nameEq} actor (registry before) =
    Just retiredFiber) ->
  (0 retiredTrue : retired retiredFiber = True) ->
  RetiredRegistryLookupView name key world error value nameEq actor
    (registry afterState)
retiredOwnerActionStep nameEq keyEq actor action same before afterState tag raw
  retiredFiber retiredFound retiredTrue =
    retiredOwnerTargetReindex nameEq actor (actionOwner action) same
      (registry afterState)
      (retiredAcrossRegistryUpdate nameEq (actionOwner action) (registry before)
        (registry afterState)
        (systemRegistryUpdate (applyActionLocalUpdate nameEq keyEq action before
          afterState tag raw)) retiredFiber
        (retiredOwnerSourceFound nameEq actor (actionOwner action) same
          (registry before) retiredFiber retiredFound) retiredTrue)

0 retiredAcrossActionStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (0 raw : applyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (retiredFiber : Fiber name key value world error) ->
  (0 retiredFound : lookupFiber @{nameEq} actor (registry before) =
    Just retiredFiber) ->
  (0 retiredTrue : retired retiredFiber = True) ->
  RetiredRegistryLookupView name key world error value nameEq actor
    (registry afterState)
retiredAcrossActionStep nameEq keyEq actor action before afterState tag raw
  retiredFiber retiredFound retiredTrue =
    case decEq @{nameEq} actor (actionOwner action) of
      No distinct => retiredForeignActionStep nameEq keyEq actor action distinct
        before afterState tag raw retiredFiber retiredFound retiredTrue
      Yes same => retiredOwnerActionStep nameEq keyEq actor action same before
        afterState tag raw retiredFiber retiredFound retiredTrue

0 retiredActiveQuietImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world
      (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (fibers : Registry name key value world error) ->
  (0 retiredTrue : retiredFlag = True) ->
  (0 fiberQuiet : quietFiber @{nameEq} @{keyEq}
    (MkFiber component parent retiredFlag table (Active accumulator view))
    fibers = True) -> Void
retiredActiveQuietImpossible nameEq keyEq component parent retiredFlag table
  accumulator view fibers retiredTrue fiberQuiet =
    falseNotTrueO7 (replace
      {p = \flag => quietFiber @{nameEq} @{keyEq}
        (MkFiber component parent flag table (Active accumulator view)) fibers =
        True} retiredTrue fiberQuiet)

0 retiredQuietFiberUninstalled :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (state : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  (0 found : lookupFiber @{nameEq} actor (registry state) = Just fiber) ->
  (0 retiredTrue : retired fiber = True) ->
  (0 fiberQuiet : quietFiber @{nameEq} @{keyEq} fiber (registry state) = True) ->
  installedAt @{nameEq} actor state = False
retiredQuietFiberUninstalled nameEq keyEq actor state
  (MkFiber component parent retiredFlag table (Inactive outcome)) found
  retiredTrue fiberQuiet =
    trans (installedAtFound nameEq actor state
      (MkFiber component parent retiredFlag table (Inactive outcome)) found) Refl
retiredQuietFiberUninstalled nameEq keyEq actor state
  (MkFiber component parent retiredFlag table
    (Reloading remaining accumulator view)) found retiredTrue fiberQuiet =
      void (falseNotTrueO7 fiberQuiet)
retiredQuietFiberUninstalled nameEq keyEq actor state
  (MkFiber component parent retiredFlag table (Active accumulator view)) found
  retiredTrue fiberQuiet =
    void (retiredActiveQuietImpossible nameEq keyEq component parent retiredFlag
      table accumulator view (registry state) retiredTrue fiberQuiet)
retiredQuietFiberUninstalled nameEq keyEq actor state
  (MkFiber component parent retiredFlag table
    (Unloading accumulator view outcome)) found retiredTrue fiberQuiet =
      void (falseNotTrueO7 fiberQuiet)

0 retiredQuietUninstalled :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (state : SystemState name key value world error) ->
  (0 quietState : quiet @{nameEq} @{keyEq} state = True) ->
  RetireTargetLookupView name key world error value nameEq actor state ->
  installedAt @{nameEq} actor state = False
retiredQuietUninstalled nameEq keyEq actor state quietState
  (MkRetireTargetLookupView fiber found retiredTrue) =
    retiredQuietFiberUninstalled nameEq keyEq actor state fiber found retiredTrue
      (quietFiberFromState nameEq keyEq state quietState actor fiber found)

record EventuallyUninstalled
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (actor : name)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState) where
  constructor MkEventuallyUninstalled
  uninstalledState : SystemState name key value world error
  beforeUninstalled : Transitions first uninstalledState
  afterUninstalled : Transitions uninstalledState finalState
  0 eventualUninstalled : installedAt @{nameEq} actor uninstalledState = False
  0 eventualUninstalledDecomposition : appendTransitions beforeUninstalled
    afterUninstalled = trace

0 prependEventuallyUninstalled :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (head : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  EventuallyUninstalled name key world error value nameEq actor rest ->
  EventuallyUninstalled name key world error value nameEq actor
    (MoreTransitions head rest)
prependEventuallyUninstalled nameEq actor head rest
  (MkEventuallyUninstalled state before after uninstalled decomposition) =
    MkEventuallyUninstalled state (MoreTransitions head before) after
      uninstalled (cong (MoreTransitions head) decomposition)

0 retiredEventuallyUninstalled :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (trace : Transitions first finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  (0 finalQuiet : quiet @{nameEq} @{keyEq} finalState = True) ->
  RetireTargetLookupView name key world error value nameEq actor first ->
  EventuallyUninstalled name key world error value nameEq actor trace
retiredEventuallyUninstalled nameEq keyEq actor NoTransitions AlignedEnd
  finalQuiet retiredAt =
    MkEventuallyUninstalled first NoTransitions NoTransitions
      (retiredQuietUninstalled nameEq keyEq actor first finalQuiet retiredAt) Refl
retiredEventuallyUninstalled nameEq keyEq actor
  (MoreTransitions (Fired {before = first} {afterState = middle}
    nameEq keyEq action tag checked) rest)
  (AlignedStep action tag checked rest alignedRest) finalQuiet
  (MkRetireTargetLookupView fiber found retiredTrue) =
    case retiredAcrossActionStep nameEq keyEq actor action first middle tag
      (checkedActionProjects nameEq keyEq action first middle tag checked)
      fiber found retiredTrue of
        RetiredRegistryLookupMissing missing =>
          MkEventuallyUninstalled middle
            (MoreTransitions
              (Fired {before = first} {afterState = middle}
                nameEq keyEq action tag checked) NoTransitions)
            rest (installedAtMissing nameEq actor middle
              (lookupFiber @{nameEq} actor (registry middle)) Refl missing) Refl
        RetiredRegistryLookupPresent nextFiber nextFound nextRetired =>
          prependEventuallyUninstalled nameEq actor
            (Fired {before = first} {afterState = middle}
              nameEq keyEq action tag checked) rest
            (retiredEventuallyUninstalled nameEq keyEq actor rest alignedRest
              finalQuiet
              (MkRetireTargetLookupView nextFiber nextFound nextRetired))

0 futureRetirementEventuallyUninstalled :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) ->
  (trace : Transitions first finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  (0 finalQuiet : quiet @{nameEq} @{keyEq} finalState = True) ->
  ActionOccurs (ORetire child) trace ->
  EventuallyUninstalled name key world error value nameEq child trace
futureRetirementEventuallyUninstalled nameEq keyEq child NoTransitions
  AlignedEnd finalQuiet occurs =
    case occurs of
      ActionOccursHere transition rest actionShape impossible
      ActionOccursLater transition rest later impossible
futureRetirementEventuallyUninstalled nameEq keyEq child
  (MoreTransitions (Fired {before = first} {afterState = middle}
    nameEq keyEq action tag checked) rest)
  (AlignedStep action tag checked rest alignedRest) finalQuiet
  (ActionOccursHere _ _ actionShape) =
    prependEventuallyUninstalled nameEq child
      (Fired {before = first} {afterState = middle}
        nameEq keyEq action tag checked) rest
      (retiredEventuallyUninstalled nameEq keyEq child rest alignedRest
        finalQuiet
        (retireTransitionTargetView nameEq keyEq child first middle tag
          (rawRetireFromActionShape nameEq keyEq child action actionShape first
            middle tag
            (checkedActionProjects nameEq keyEq action first middle tag
              checked))))
futureRetirementEventuallyUninstalled nameEq keyEq child
  (MoreTransitions (Fired {before = first} {afterState = middle}
    nameEq keyEq action tag checked) rest)
  (AlignedStep action tag checked rest alignedRest) finalQuiet
  (ActionOccursLater _ _ later) =
    prependEventuallyUninstalled nameEq child
      (Fired {before = first} {afterState = middle}
        nameEq keyEq action tag checked) rest
      (futureRetirementEventuallyUninstalled nameEq keyEq child rest alignedRest
        finalQuiet later)

0 appendLocatedClosingEpisodeRight :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {actor : name} ->
  {first, leftFinal, finalState : SystemState name key value world error} ->
  (left : Transitions first leftFinal) ->
  LocatedClosedEpisode name key world error value nameEq keyEq actor left ->
  (right : Transitions leftFinal finalState) ->
  LocatedClosedEpisode name key world error value nameEq keyEq actor
    (appendTransitions left right)
appendLocatedClosingEpisodeRight left
  (MkLocatedClosedEpisode preStart afterClose beforeOpening episode afterClosing
    decomposition) right =
      MkLocatedClosedEpisode preStart afterClose beforeOpening episode
        (appendTransitions afterClosing right)
        (trans (cong (appendTransitions beforeOpening)
          (cong (MoreTransitions (beginTransition (closedOpening episode)))
            (sym (appendTransitionsAssociative (closedTransitions episode)
              afterClosing right))))
          (trans (sym (appendTransitionsAssociative beforeOpening
            (MoreTransitions (beginTransition (closedOpening episode))
              (appendTransitions (closedTransitions episode) afterClosing))
            right))
            (cong (\candidate => appendTransitions candidate right)
              decomposition)))

0 closingFromEventuallyUninstalled :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) ->
  (before, opened, finalState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (LBegin child) before =
    Just (tag, opened)) ->
  (rest : Transitions opened finalState) ->
  (0 alignedRest : AlignedTransitions name key world error value nameEq keyEq
    rest) ->
  EventuallyUninstalled name key world error value nameEq child rest ->
  LocatedClosedEpisode name key world error value nameEq keyEq child
    (MoreTransitions
      (Fired {before = before} {afterState = opened}
        nameEq keyEq (LBegin child) tag checked) rest)
closingFromEventuallyUninstalled nameEq keyEq child before opened finalState tag
  checked rest alignedRest
  (MkEventuallyUninstalled endpoint beforeEndpoint afterEndpoint
    endpointUninstalled endpointDecomposition) =
      replace
        {p = \candidate => LocatedClosedEpisode name key world error value
          nameEq keyEq child candidate}
        (trans (appendTransitionsAssociative
          (MoreTransitions
            (Fired {before = before} {afterState = opened}
              nameEq keyEq (LBegin child) tag checked) NoTransitions)
          beforeEndpoint afterEndpoint)
          (cong (MoreTransitions
            (Fired {before = before} {afterState = opened}
              nameEq keyEq (LBegin child) tag checked))
            endpointDecomposition))
        (appendLocatedClosingEpisodeRight
          (appendTransitions
            (MoreTransitions
              (Fired {before = before} {afterState = opened}
                nameEq keyEq (LBegin child) tag checked) NoTransitions)
            beforeEndpoint)
          (extractSpanningClosedEpisode nameEq keyEq child
            (MoreTransitions
              (Fired {before = before} {afterState = opened}
                nameEq keyEq (LBegin child) tag checked) NoTransitions)
            beforeEndpoint
            (AlignedStep (LBegin child) tag checked NoTransitions AlignedEnd)
            (fst (alignedAppendSplit beforeEndpoint afterEndpoint
              (replace
                {p = \candidate => AlignedTransitions name key world error value
                  nameEq keyEq candidate}
                (sym endpointDecomposition) alignedRest)))
            (fst (snd (lBeginBoundary nameEq keyEq child before opened tag
              checked)))
            (snd (snd (lBeginBoundary nameEq keyEq child before opened tag
              checked))) endpointUninstalled)
          afterEndpoint)

0 futureRetirementClosesBegin :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) ->
  (before, opened, finalState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (LBegin child) before =
    Just (tag, opened)) ->
  (rest : Transitions opened finalState) ->
  (0 alignedRest : AlignedTransitions name key world error value nameEq keyEq
    rest) ->
  (0 finalQuiet : quiet @{nameEq} @{keyEq} finalState = True) ->
  ActionOccurs (ORetire child) rest ->
  LocatedClosedEpisode name key world error value nameEq keyEq child
    (MoreTransitions
      (Fired {before = before} {afterState = opened}
        nameEq keyEq (LBegin child) tag checked) rest)
futureRetirementClosesBegin nameEq keyEq child before opened finalState tag
  checked rest alignedRest finalQuiet retires =
    closingFromEventuallyUninstalled nameEq keyEq child before opened finalState
      tag checked rest alignedRest
      (futureRetirementEventuallyUninstalled nameEq keyEq child rest alignedRest
        finalQuiet retires)

0 singletonBeginOwnedCurrent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {ordinal : Nat} ->
  (nameEq : DecEq name) -> (action : Action name key value world error) ->
  (generation : RegistrationGeneration name) ->
  (live : GenerationEnvironment name) ->
  IsBeginAction action ->
  GenerationOwnedActor nameEq [generation] ordinal live action ->
  lookupCurrentGeneration @{nameEq} (actionOwner action) live = Just generation
singletonBeginOwnedCurrent nameEq (LBegin observed) generation live ItIsLBegin
  (_ ** (current, Here)) = current
singletonBeginOwnedCurrent nameEq (LBegin observed) generation live ItIsLBegin
  (_ ** (current, There later)) = absurd later

0 singletonBeginOwnedActor :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {ordinal : Nat} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (generation : RegistrationGeneration name) ->
  (live : GenerationEnvironment name) ->
  (0 stamped : GenerationEnvironmentStamped live) ->
  (0 generationActor : generationName generation = actor) ->
  (action : Action name key value world error) ->
  (begin : IsBeginAction action) ->
  (owned : GenerationOwnedActor nameEq [generation] ordinal live action) ->
  actionOwner action = actor
singletonBeginOwnedActor nameEq actor generation live stamped generationActor
  (LBegin observed) ItIsLBegin (_ ** (current, Here)) =
    trans (sym (stamped observed generation
      (currentGenerationEntryFromLookup nameEq observed generation live
        current))) generationActor
singletonBeginOwnedActor nameEq actor generation live stamped generationActor
  (LBegin observed) ItIsLBegin (_ ** (current, There later)) =
    absurd later

0 notCurrentRejectsRegisteredBegin :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {ordinal : Nat} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (generation : RegistrationGeneration name) ->
  (live : GenerationEnvironment name) ->
  (0 stamped : GenerationEnvironmentStamped live) ->
  (0 generationActor : generationName generation = actor) ->
  (action : Action name key value world error) ->
  (0 noCurrent : Not (lookupCurrentGeneration @{nameEq} actor live =
    Just generation)) ->
  (begin : IsBeginAction action) ->
  (owned : GenerationOwnedActor nameEq [generation] ordinal live action) -> Void
notCurrentRejectsRegisteredBegin nameEq actor generation live stamped
  generationActor action noCurrent begin owned =
    noCurrent (replace
      {p = \candidate => lookupCurrentGeneration @{nameEq} candidate live =
        Just generation}
      (singletonBeginOwnedActor nameEq actor generation live stamped
        generationActor action begin owned)
      (singletonBeginOwnedCurrent nameEq action generation live begin owned))

0 noCurrentAfterOneStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (generation : RegistrationGeneration name) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (0 unique : GenerationEnvironmentNamesUnique live) ->
  (0 less : LT (generationBirthOrdinal generation) ordinal) ->
  {first, middle : SystemState name key value world error} ->
  (transition : Transition first middle) ->
  (0 noCurrent : Not (lookupCurrentGeneration @{nameEq} actor live =
    Just generation)) ->
  Not (lookupCurrentGeneration @{nameEq} actor
    (advanceGenerationEnvironment @{nameEq} ordinal
      (transitionAction transition) live) = Just generation)
noCurrentAfterOneStep nameEq actor generation ordinal live unique less transition
  noCurrent nextCurrent =
    noCurrent (currentGenerationAtScanStart nameEq actor generation ordinal live
      unique less (MoreTransitions transition NoTransitions) (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction transition) live)
      (GenerationTraceScanStep transition NoTransitions GenerationTraceScanEnd)
      nextCurrent)

0 noRegisteredWhenNotCurrent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (generation : RegistrationGeneration name) ->
  (0 generationActor : generationName generation = actor) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (0 unique : GenerationEnvironmentNamesUnique live) ->
  (0 stamped : GenerationEnvironmentStamped live) ->
  (0 less : LT (generationBirthOrdinal generation) ordinal) ->
  (trace : Transitions first finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq ordinal live trace finalOrdinal finalLive ->
  (0 noCurrent : Not (lookupCurrentGeneration @{nameEq} actor live =
    Just generation)) ->
  NoRegisteredEpisode nameEq [generation] ordinal live trace
noRegisteredWhenNotCurrent nameEq actor generation generationActor ordinal live
  unique stamped less NoTransitions ordinal live GenerationTraceScanEnd noCurrent =
    NoRegisteredEpisodeEnd
noRegisteredWhenNotCurrent nameEq actor generation generationActor ordinal live
  unique stamped less
  (MoreTransitions transition@(Fired stepNameEq stepKeyEq action tag checked)
    rest) finalOrdinal finalLive
  (GenerationTraceScanStep _ _ tailScan) noCurrent =
    NoRegisteredEpisodeStep transition rest
      (notCurrentRejectsRegisteredBegin nameEq actor generation live stamped
        generationActor action noCurrent)
      (noRegisteredWhenNotCurrent nameEq actor generation generationActor
        (S ordinal)
        (advanceGenerationEnvironment @{nameEq} ordinal action live)
        (advanceGenerationEnvironmentPreservesUnique nameEq ordinal action live
          unique)
        (advanceGenerationEnvironmentPreservesStamped nameEq ordinal action live
          stamped)
        (lteSuccRight less) rest finalOrdinal finalLive tailScan
        (noCurrentAfterOneStep nameEq actor generation ordinal live unique less
          transition noCurrent))

0 currentGenerationEntryBound :
  {name : Type} -> (ordinal : Nat) ->
  (live : GenerationEnvironment name) ->
  (0 bounded : GenerationEnvironmentBounded ordinal live) ->
  (actor : name) -> (generation : RegistrationGeneration name) ->
  Elem (actor, generation) live ->
  LT (generationBirthOrdinal generation) ordinal
currentGenerationEntryBound ordinal [] bounded actor generation present =
  absurd present
currentGenerationEntryBound ordinal ((actor, generation) :: rest)
  (headBound, tailBound) actor generation Here = headBound
currentGenerationEntryBound ordinal ((current, currentGeneration) :: rest)
  (headBound, tailBound) actor generation (There later) =
    currentGenerationEntryBound ordinal rest tailBound actor generation later

0 beforeGenerationBirthRejectsBegin :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  (generation : RegistrationGeneration name) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (0 bounded : GenerationEnvironmentBounded ordinal live) ->
  (trace : Transitions first finalState) ->
  (birthOrdinal : Nat) -> (birthLive : GenerationEnvironment name) ->
  (scan : GenerationTraceScan nameEq ordinal live trace birthOrdinal birthLive) ->
  (0 birthShape : generationBirthOrdinal generation = birthOrdinal) ->
  (action : Action name key value world error) ->
  (begin : IsBeginAction action) ->
  (owned : GenerationOwnedActor nameEq [generation] ordinal live action) -> Void
beforeGenerationBirthRejectsBegin nameEq generation ordinal live bounded trace
  birthOrdinal birthLive scan birthShape action begin owned =
    LTEImpliesNotGT
      (replace {p = \candidate => LTE ordinal candidate} (sym birthShape)
        (generationScanStartLTE scan))
      (currentGenerationEntryBound ordinal live bounded (actionOwner action)
        generation
        (currentGenerationEntryFromLookup nameEq (actionOwner action) generation
          live
          (singletonBeginOwnedCurrent nameEq action generation live begin
            owned)))

0 noRegisteredBeforeGenerationBirth :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  (generation : RegistrationGeneration name) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (0 bounded : GenerationEnvironmentBounded ordinal live) ->
  (trace : Transitions first finalState) ->
  (birthOrdinal : Nat) -> (birthLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq ordinal live trace birthOrdinal birthLive ->
  (0 birthShape : generationBirthOrdinal generation = birthOrdinal) ->
  NoRegisteredEpisode nameEq [generation] ordinal live trace
noRegisteredBeforeGenerationBirth nameEq generation ordinal live bounded
  NoTransitions ordinal live GenerationTraceScanEnd birthShape =
    NoRegisteredEpisodeEnd
noRegisteredBeforeGenerationBirth nameEq generation ordinal live bounded
  (MoreTransitions transition@(Fired stepNameEq stepKeyEq action tag checked)
    rest) birthOrdinal birthLive
  (GenerationTraceScanStep _ _ tailScan) birthShape =
    NoRegisteredEpisodeStep transition rest
      (beforeGenerationBirthRejectsBegin nameEq generation ordinal live bounded
        (MoreTransitions transition rest) birthOrdinal birthLive
        (GenerationTraceScanStep transition rest tailScan) birthShape action)
      (noRegisteredBeforeGenerationBirth nameEq generation (S ordinal)
        (advanceGenerationEnvironment @{nameEq} ordinal action live)
        (advanceGenerationEnvironmentBounded nameEq ordinal action live bounded)
        rest birthOrdinal birthLive tailScan birthShape)

0 transitionCountAppend :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  transitionCount (appendTransitions left right) =
    transitionCount left + transitionCount right
transitionCountAppend NoTransitions right = Refl
transitionCountAppend (MoreTransitions transition rest) right =
  cong S (transitionCountAppend rest right)

0 leftLTEPlus : (left, right : Nat) -> LTE left (left + right)
leftLTEPlus 0 right = LTEZero
leftLTEPlus (S left) right = LTESucc (leftLTEPlus left right)

record GlobalizedClosing
  {name, key, world, error : Type} (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {first, finalState : SystemState name key value world error}
  (actor : name) (globalTrace : Transitions first finalState)
  (leadingLength : Nat) where
  constructor MkGlobalizedClosing
  0 closingEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    actor globalTrace
  0 openingAfterLeading : LTE leadingLength
    (transitionCount (traceBeforeOpening closingEpisode))

0 globalizeLocatedClosing :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, current, finalState : SystemState name key value world error} ->
  (actor : name) -> (leading : Transitions first current) ->
  (suffix : Transitions current finalState) ->
  (globalTrace : Transitions first finalState) ->
  (0 globalSplit : appendTransitions leading suffix = globalTrace) ->
  LocatedClosedEpisode name key world error value nameEq keyEq actor suffix ->
  GlobalizedClosing value nameEq keyEq actor globalTrace
    (transitionCount leading)
globalizeLocatedClosing nameEq keyEq actor leading suffix globalTrace globalSplit
  (MkLocatedClosedEpisode preStart afterClose beforeOpening episode afterClosing
    decomposition) =
      MkGlobalizedClosing
        (MkLocatedClosedEpisode preStart afterClose
          (appendTransitions leading beforeOpening) episode afterClosing
          (trans
            (trans
              (appendTransitionsAssociative leading beforeOpening
                (MoreTransitions (beginTransition (closedOpening episode))
                  (appendTransitions (closedTransitions episode)
                    afterClosing)))
              (cong (appendTransitions leading) decomposition))
            globalSplit))
        (rewrite transitionCountAppend leading beforeOpening in
          leftLTEPlus (transitionCount leading)
            (transitionCount beforeOpening))

0 globalizedClosingContradictsUpper :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (actor : name) -> (globalTrace : Transitions initial finalState) ->
  (selectedOrdinal, leadingLength : Nat) ->
  (0 selectedBeforeLeading : LTE (S selectedOrdinal) leadingLength) ->
  (0 upper : (closingActor : name) ->
    (closingEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
      closingActor globalTrace) ->
    LTE (transitionCount (traceBeforeOpening closingEpisode))
      selectedOrdinal) ->
  GlobalizedClosing value nameEq keyEq actor globalTrace leadingLength -> Void
globalizedClosingContradictsUpper nameEq keyEq actor globalTrace selectedOrdinal
  leadingLength selectedBeforeLeading upper
  (MkGlobalizedClosing episode leadingBeforeOpening) =
    LTEImpliesNotGT (upper actor episode)
      (transitive selectedBeforeLeading leadingBeforeOpening)

0 sameActorFutureBeginContradictsMaximal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (ordinal, selectedOrdinal : Nat) ->
  (0 selectedBeforeCurrent : LTE (S selectedOrdinal) ordinal) ->
  (initial, before, opened, finalState :
    SystemState name key value world error) ->
  (globalTrace : Transitions initial finalState) ->
  (leading : Transitions initial before) ->
  (current : Transitions before finalState) ->
  (0 globalSplit : appendTransitions leading current = globalTrace) ->
  (0 prefixOrdinal : transitionCount leading = ordinal) ->
  (0 upper : (closingActor : name) ->
    (closingEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
      closingActor globalTrace) ->
    LTE (transitionCount (traceBeforeOpening closingEpisode))
      selectedOrdinal) ->
  (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (LBegin actor) before =
    Just (tag, opened)) ->
  (rest : Transitions opened finalState) ->
  (0 currentShape : current = MoreTransitions
    (Fired nameEq keyEq (LBegin actor) tag checked) rest) ->
  (0 alignedRest : AlignedTransitions name key world error value nameEq keyEq
    rest) ->
  (0 finalQuiet : quiet @{nameEq} @{keyEq} finalState = True) ->
  ActionOccurs (ORetire actor) rest -> Void
sameActorFutureBeginContradictsMaximal nameEq keyEq actor ordinal selectedOrdinal
  selectedBeforeCurrent initial before opened finalState globalTrace leading
  current globalSplit prefixOrdinal upper tag checked rest currentShape alignedRest
  finalQuiet retires =
    globalizedClosingContradictsUpper nameEq keyEq actor globalTrace
      selectedOrdinal (transitionCount leading)
      (replace {p = \candidate => LTE (S selectedOrdinal) candidate}
        (sym prefixOrdinal) selectedBeforeCurrent)
      upper
      (globalizeLocatedClosing nameEq keyEq actor leading current globalTrace
        globalSplit
        (replace
          {p = \candidate => LocatedClosedEpisode name key world error value
            nameEq keyEq actor candidate}
          (sym currentShape)
          (futureRetirementClosesBegin nameEq keyEq actor before opened finalState
            tag checked rest alignedRest finalQuiet retires)))

0 futureRegisteredBeginContradictsMaximal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (generation : RegistrationGeneration name) ->
  (0 generationActor : generationName generation = actor) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (0 stamped : GenerationEnvironmentStamped live) ->
  (selectedOrdinal : Nat) ->
  (0 selectedBeforeCurrent : LTE (S selectedOrdinal) ordinal) ->
  (initial, before, finalState : SystemState name key value world error) ->
  (globalTrace : Transitions initial finalState) ->
  (leading : Transitions initial before) ->
  (current : Transitions before finalState) ->
  (0 globalSplit : appendTransitions leading current = globalTrace) ->
  (0 prefixOrdinal : transitionCount leading = ordinal) ->
  (0 upper : (closingActor : name) ->
    (closingEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
      closingActor globalTrace) ->
    LTE (transitionCount (traceBeforeOpening closingEpisode))
      selectedOrdinal) ->
  (observedActor : name) ->
  (opened : SystemState name key value world error) -> (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (LBegin observedActor)
    before = Just (tag, opened)) ->
  (rest : Transitions opened finalState) ->
  (0 currentShape : current = MoreTransitions
    (Fired nameEq keyEq (LBegin observedActor) tag checked) rest) ->
  (0 alignedRest : AlignedTransitions name key world error value nameEq keyEq
    rest) ->
  (0 finalQuiet : quiet @{nameEq} @{keyEq} finalState = True) ->
  ActionOccurs (ORetire actor) rest ->
  (owned : GenerationOwnedActor nameEq [generation] ordinal live
    (the (Action name key value world error) (LBegin observedActor))) -> Void
futureRegisteredBeginContradictsMaximal nameEq keyEq actor generation
  generationActor ordinal live stamped selectedOrdinal selectedBeforeCurrent
  initial before finalState globalTrace leading current globalSplit prefixOrdinal
  upper observedActor opened tag checked rest currentShape alignedRest finalQuiet
  retires owned =
    case singletonBeginOwnedActor {name = name} {key = key} {value = value}
      {world = world} {error = error} {ordinal = ordinal} nameEq actor generation
      live stamped generationActor (LBegin observedActor) ItIsLBegin owned of
      Refl => sameActorFutureBeginContradictsMaximal nameEq keyEq actor ordinal
        selectedOrdinal selectedBeforeCurrent initial before opened finalState
        globalTrace leading current globalSplit prefixOrdinal upper tag checked
        rest currentShape alignedRest finalQuiet retires

0 retiredSourceRejectsBegin :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (0 raw : applyAction @{nameEq} @{keyEq} (LBegin actor) before =
    Just (tag, afterState)) ->
  (0 retiredAt : RetiredFiberAt name key world error value nameEq actor before) ->
  Void
retiredSourceRejectsBegin nameEq keyEq actor before afterState tag raw retiredAt =
  retiredCannotBeginState nameEq keyEq actor before afterState tag raw
    (retiredFiberAt retiredAt) (retiredFiberFound retiredAt)
    (retiredFiberTrue retiredAt)

0 singletonCurrentRegisteredInactive :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (generation : RegistrationGeneration name) ->
  (0 generationActor : generationName generation = actor) ->
  (live : GenerationEnvironment name) ->
  (0 stamped : GenerationEnvironmentStamped live) ->
  (state : SystemState name key value world error) ->
  (0 actorInactive : InactiveFiberAt name key world error value nameEq actor
    state) ->
  CurrentRegisteredInactiveFibers name key world error value nameEq [generation]
    live state
singletonCurrentRegisteredInactive nameEq actor generation generationActor live
  stamped state actorInactive selected _ Here current =
    replace
      {p = \candidate => InactiveFiberAt name key world error value nameEq
        candidate state}
      (trans (sym generationActor)
        (stamped selected generation
          (currentGenerationEntryFromLookup nameEq selected generation live
            current)))
      actorInactive
singletonCurrentRegisteredInactive nameEq actor generation generationActor live
  stamped state actorInactive selected _ (There later) current =
    absurd later

0 retiredRegisteredNoBegin :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {ordinal : Nat} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (generation : RegistrationGeneration name) ->
  (live : GenerationEnvironment name) ->
  (0 stamped : GenerationEnvironmentStamped live) ->
  (0 generationActor : generationName generation = actor) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (0 raw : applyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (0 retiredAt : RetiredFiberAt name key world error value nameEq actor before) ->
  IsBeginAction action ->
  GenerationOwnedActor nameEq [generation] ordinal live action -> Void
retiredRegisteredNoBegin nameEq keyEq actor generation live stamped
  generationActor (LBegin observedActor) before afterState tag raw retiredAt
  ItIsLBegin owned =
    case singletonBeginOwnedActor {name = name} {key = key} {value = value}
      {world = world} {error = error} {ordinal = ordinal} nameEq actor generation
      live stamped generationActor (LBegin observedActor) ItIsLBegin owned of
      Refl => retiredSourceRejectsBegin nameEq keyEq actor before afterState tag
        raw retiredAt

0 oneStepRetiredPersistence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (generation : RegistrationGeneration name) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (0 unique : GenerationEnvironmentNamesUnique live) ->
  (0 less : LT (generationBirthOrdinal generation) ordinal) ->
  (before, afterState : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (0 noBegin : IsBeginAction action ->
    GenerationOwnedActor nameEq [generation] ordinal live action -> Void) ->
  (0 current : lookupCurrentGeneration @{nameEq} actor live =
    Just generation) ->
  (0 nextCurrent : lookupCurrentGeneration @{nameEq} actor
    (advanceGenerationEnvironment @{nameEq} ordinal action live) =
    Just generation) ->
  (0 retiredAt : RetiredFiberAt name key world error value nameEq actor before) ->
  (0 inactive : InactiveFiberAt name key world error value nameEq actor before) ->
  RetiredFiberAt name key world error value nameEq actor afterState
oneStepRetiredPersistence nameEq keyEq actor generation ordinal live unique less
  before afterState action tag checked noBegin current nextCurrent retiredAt
  inactive =
    retiredInactiveCurrentPersists nameEq keyEq actor generation ordinal live
      unique less
      (MoreTransitions (Fired nameEq keyEq action tag checked) NoTransitions)
      (S ordinal) (advanceGenerationEnvironment @{nameEq} ordinal action live)
      (GenerationTraceScanStep (Fired nameEq keyEq action tag checked)
        NoTransitions GenerationTraceScanEnd)
      (AlignedStep action tag checked NoTransitions AlignedEnd)
      (NoRegisteredEpisodeStep (Fired nameEq keyEq action tag checked)
        NoTransitions noBegin NoRegisteredEpisodeEnd)
      current nextCurrent retiredAt inactive

0 oneStepInactivePersistence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (generation : RegistrationGeneration name) ->
  (0 generationActor : generationName generation = actor) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (0 unique : GenerationEnvironmentNamesUnique live) ->
  (0 stamped : GenerationEnvironmentStamped live) ->
  (before, afterState : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (0 noBegin : IsBeginAction action ->
    GenerationOwnedActor nameEq [generation] ordinal live action -> Void) ->
  (0 nextCurrent : lookupCurrentGeneration @{nameEq} actor
    (advanceGenerationEnvironment @{nameEq} ordinal action live) =
    Just generation) ->
  (0 inactive : InactiveFiberAt name key world error value nameEq actor before) ->
  InactiveFiberAt name key world error value nameEq actor afterState
oneStepInactivePersistence nameEq keyEq actor generation generationActor ordinal
  live unique stamped before afterState action tag checked noBegin nextCurrent
  inactive =
    currentRegisteredInactiveStep nameEq keyEq [generation] ordinal live unique
      action before afterState tag
      (checkedActionProjects nameEq keyEq action before afterState tag checked)
      noBegin
      (singletonCurrentRegisteredInactive nameEq actor generation
        generationActor live stamped before inactive)
      actor generation Here nextCurrent

0 retiredFiberAtFromTargetView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (state : SystemState name key value world error) ->
  RetireTargetLookupView name key world error value nameEq actor state ->
  RetiredFiberAt name key world error value nameEq actor state
retiredFiberAtFromTargetView nameEq actor state
  (MkRetireTargetLookupView fiber found retiredTrue) =
    MkRetiredFiberAt fiber found retiredTrue

0 transitionCountSnoc :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, middle, finalState : SystemState name key value world error} ->
  (leading : Transitions initial middle) ->
  (transition : Transition middle finalState) ->
  transitionCount
    (appendTransitions leading (MoreTransitions transition NoTransitions)) =
  S (transitionCount leading)
transitionCountSnoc NoTransitions transition = Refl
transitionCountSnoc (MoreTransitions previous rest) transition =
  cong S (transitionCountSnoc rest transition)

0 extendLeadingDecomposition :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, first, middle, finalState :
    SystemState name key value world error} ->
  (leading : Transitions initial first) ->
  (transition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (globalTrace : Transitions initial finalState) ->
  (0 globalSplit : appendTransitions leading
    (MoreTransitions transition rest) = globalTrace) ->
  appendTransitions
    (appendTransitions leading (MoreTransitions transition NoTransitions)) rest =
  globalTrace
extendLeadingDecomposition leading transition rest globalTrace globalSplit =
  trans (appendTransitionsAssociative leading
    (MoreTransitions transition NoTransitions) rest) globalSplit

0 retireActionCannotBeBegin :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (action : Action name key value world error) -> (actor : name) ->
  (0 actionShape : action = ORetire actor) -> IsBeginAction action -> Void
retireActionCannotBeBegin (ORetire actor) actor Refl begin impossible

0 laterRetirementNoBegin :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (generation : RegistrationGeneration name) ->
  (0 generationActor : generationName generation = actor) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (0 stamped : GenerationEnvironmentStamped live) ->
  (selectedOrdinal : Nat) ->
  (0 selectedBeforeCurrent : LTE (S selectedOrdinal) ordinal) ->
  (initial, first, middle, finalState :
    SystemState name key value world error) ->
  (globalTrace : Transitions initial finalState) ->
  (leading : Transitions initial first) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} action first =
    Just (tag, middle)) ->
  (rest : Transitions middle finalState) ->
  (0 globalSplit : appendTransitions leading
    (MoreTransitions (Fired {before = first} {afterState = middle}
      nameEq keyEq action tag checked) rest) = globalTrace) ->
  (0 prefixOrdinal : transitionCount leading = ordinal) ->
  (0 upper : (closingActor : name) ->
    (closingEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
      closingActor globalTrace) ->
    LTE (transitionCount (traceBeforeOpening closingEpisode))
      selectedOrdinal) ->
  (0 alignedRest : AlignedTransitions name key world error value nameEq keyEq
    rest) ->
  (0 finalQuiet : quiet @{nameEq} @{keyEq} finalState = True) ->
  ActionOccurs (ORetire actor) rest -> IsBeginAction action ->
  GenerationOwnedActor nameEq [generation] ordinal live action -> Void
laterRetirementNoBegin nameEq keyEq actor generation generationActor ordinal live
  stamped selectedOrdinal selectedBeforeCurrent initial first middle finalState
  globalTrace leading (LBegin observedActor) tag checked rest globalSplit
  prefixOrdinal upper alignedRest finalQuiet later ItIsLBegin owned =
    futureRegisteredBeginContradictsMaximal nameEq keyEq actor generation
      generationActor ordinal live stamped selectedOrdinal selectedBeforeCurrent
      initial first finalState globalTrace leading
      (MoreTransitions (Fired {before = first} {afterState = middle}
        nameEq keyEq (LBegin observedActor) tag checked) rest)
      globalSplit prefixOrdinal upper observedActor middle tag checked rest Refl
      alignedRest finalQuiet later owned

0 noRegisteredAfterRetiredInactive :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (generation : RegistrationGeneration name) ->
  (0 generationActor : generationName generation = actor) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (0 unique : GenerationEnvironmentNamesUnique live) ->
  (0 stamped : GenerationEnvironmentStamped live) ->
  (0 less : LT (generationBirthOrdinal generation) ordinal) ->
  (trace : Transitions first finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq ordinal live trace finalOrdinal finalLive ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  (0 current : lookupCurrentGeneration @{nameEq} actor live =
    Just generation) ->
  (0 retiredAt : RetiredFiberAt name key world error value nameEq actor first) ->
  (0 inactive : InactiveFiberAt name key world error value nameEq actor first) ->
  NoRegisteredEpisode nameEq [generation] ordinal live trace
noRegisteredAfterRetiredInactive nameEq keyEq actor generation generationActor
  ordinal live unique stamped less NoTransitions ordinal live
  GenerationTraceScanEnd AlignedEnd current retiredAt inactive =
    NoRegisteredEpisodeEnd
noRegisteredAfterRetiredInactive nameEq keyEq actor generation generationActor
  ordinal live unique stamped less
  (MoreTransitions transition@(Fired {before = first} {afterState = middle}
    _ _ action tag checked) rest)
  finalOrdinal finalLive (GenerationTraceScanStep _ _ tailScan)
  (AlignedStep _ _ _ _ alignedTail) current retiredAt inactive =
    case decEq
      (lookupCurrentGeneration @{nameEq} actor
        (advanceGenerationEnvironment @{nameEq} ordinal action live))
      (Just generation) of
      No noNext =>
        NoRegisteredEpisodeStep (Fired nameEq keyEq action tag checked) rest
          (retiredRegisteredNoBegin nameEq keyEq actor generation live stamped
            generationActor action first middle tag
            (checkedActionProjects nameEq keyEq action first middle tag checked)
            retiredAt)
          (noRegisteredWhenNotCurrent nameEq actor generation generationActor
            (S ordinal)
            (advanceGenerationEnvironment @{nameEq} ordinal action live)
            (advanceGenerationEnvironmentPreservesUnique nameEq ordinal action
              live unique)
            (advanceGenerationEnvironmentPreservesStamped nameEq ordinal action
              live stamped)
            (lteSuccRight less) rest finalOrdinal finalLive tailScan noNext)
      Yes nextCurrent =>
        NoRegisteredEpisodeStep (Fired nameEq keyEq action tag checked) rest
          (retiredRegisteredNoBegin nameEq keyEq actor generation live stamped
            generationActor action first middle tag
            (checkedActionProjects nameEq keyEq action first middle tag checked)
            retiredAt)
          (noRegisteredAfterRetiredInactive nameEq keyEq actor generation
            generationActor (S ordinal)
            (advanceGenerationEnvironment @{nameEq} ordinal action live)
            (advanceGenerationEnvironmentPreservesUnique nameEq ordinal action
              live unique)
            (advanceGenerationEnvironmentPreservesStamped nameEq ordinal action
              live stamped)
            (lteSuccRight less) rest finalOrdinal finalLive tailScan alignedTail
            nextCurrent
            (oneStepRetiredPersistence nameEq keyEq actor generation ordinal live
              unique less first middle action tag checked
              (retiredRegisteredNoBegin nameEq keyEq actor generation live
                stamped generationActor action first middle tag
                (checkedActionProjects nameEq keyEq action first middle tag
                  checked) retiredAt)
              current nextCurrent retiredAt inactive)
            (oneStepInactivePersistence nameEq keyEq actor generation
              generationActor ordinal live unique stamped first middle action tag
              checked
              (retiredRegisteredNoBegin nameEq keyEq actor generation live
                stamped generationActor action first middle tag
                (checkedActionProjects nameEq keyEq action first middle tag
                  checked) retiredAt)
              nextCurrent inactive))

0 noRegisteredUntilFutureRetirement :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (generation : RegistrationGeneration name) ->
  (0 generationActor : generationName generation = actor) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (0 unique : GenerationEnvironmentNamesUnique live) ->
  (0 stamped : GenerationEnvironmentStamped live) ->
  (0 less : LT (generationBirthOrdinal generation) ordinal) ->
  (selectedOrdinal : Nat) ->
  (0 selectedBeforeCurrent : LTE (S selectedOrdinal) ordinal) ->
  (initial, first, finalState : SystemState name key value world error) ->
  (globalTrace : Transitions initial finalState) ->
  (leading : Transitions initial first) ->
  (trace : Transitions first finalState) ->
  (0 globalSplit : appendTransitions leading trace = globalTrace) ->
  (0 prefixOrdinal : transitionCount leading = ordinal) ->
  (0 upper : (closingActor : name) ->
    (closingEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
      closingActor globalTrace) ->
    LTE (transitionCount (traceBeforeOpening closingEpisode))
      selectedOrdinal) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq ordinal live trace finalOrdinal finalLive ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  (0 finalQuiet : quiet @{nameEq} @{keyEq} finalState = True) ->
  (0 current : lookupCurrentGeneration @{nameEq} actor live =
    Just generation) ->
  (0 inactive : InactiveFiberAt name key world error value nameEq actor first) ->
  ActionOccurs (ORetire actor) trace ->
  NoRegisteredEpisode nameEq [generation] ordinal live trace
noRegisteredUntilFutureRetirement nameEq keyEq actor generation generationActor
  ordinal live unique stamped less selectedOrdinal selectedBeforeCurrent initial
  finalState finalState globalTrace leading NoTransitions globalSplit
  prefixOrdinal upper ordinal live GenerationTraceScanEnd AlignedEnd finalQuiet
  current inactive (ActionOccursHere transition rest actionShape) impossible
noRegisteredUntilFutureRetirement nameEq keyEq actor generation generationActor
  ordinal live unique stamped less selectedOrdinal selectedBeforeCurrent initial
  finalState finalState globalTrace leading NoTransitions globalSplit
  prefixOrdinal upper ordinal live GenerationTraceScanEnd AlignedEnd finalQuiet
  current inactive (ActionOccursLater transition rest later) impossible
noRegisteredUntilFutureRetirement nameEq keyEq actor generation generationActor
  ordinal live unique stamped less selectedOrdinal selectedBeforeCurrent initial
  first finalState globalTrace leading
  (MoreTransitions (Fired {before = first} {afterState = middle}
    nameEq keyEq action tag checked) rest)
  globalSplit prefixOrdinal upper finalOrdinal finalLive
  (GenerationTraceScanStep _ _ tailScan)
  (AlignedStep _ _ _ _ alignedRest) finalQuiet current inactive
  (ActionOccursHere _ _ actionShape) =
    case decEq
      (lookupCurrentGeneration @{nameEq} actor
        (advanceGenerationEnvironment @{nameEq} ordinal action live))
      (Just generation) of
      No noNext =>
        NoRegisteredEpisodeStep (Fired nameEq keyEq action tag checked) rest
          (\begin, owned =>
            retireActionCannotBeBegin action actor actionShape begin)
          (noRegisteredWhenNotCurrent nameEq actor generation generationActor
            (S ordinal)
            (advanceGenerationEnvironment @{nameEq} ordinal action live)
            (advanceGenerationEnvironmentPreservesUnique nameEq ordinal action
              live unique)
            (advanceGenerationEnvironmentPreservesStamped nameEq ordinal action
              live stamped)
            (lteSuccRight less) rest finalOrdinal finalLive tailScan noNext)
      Yes nextCurrent =>
        NoRegisteredEpisodeStep (Fired nameEq keyEq action tag checked) rest
          (\begin, owned =>
            retireActionCannotBeBegin action actor actionShape begin)
          (noRegisteredAfterRetiredInactive nameEq keyEq actor generation
            generationActor (S ordinal)
            (advanceGenerationEnvironment @{nameEq} ordinal action live)
            (advanceGenerationEnvironmentPreservesUnique nameEq ordinal action
              live unique)
            (advanceGenerationEnvironmentPreservesStamped nameEq ordinal action
              live stamped)
            (lteSuccRight less) rest finalOrdinal finalLive tailScan alignedRest
            nextCurrent
            (retiredFiberAtFromTargetView nameEq actor middle
              (retireTransitionTargetView nameEq keyEq actor first middle tag
                (rawRetireFromActionShape nameEq keyEq actor action actionShape
                  first middle tag
                  (checkedActionProjects nameEq keyEq action first middle tag
                    checked))))
            (oneStepInactivePersistence nameEq keyEq actor generation
              generationActor ordinal live unique stamped first middle action tag
              checked
              (\begin, owned =>
                retireActionCannotBeBegin action actor actionShape begin)
              nextCurrent inactive))
noRegisteredUntilFutureRetirement nameEq keyEq actor generation generationActor
  ordinal live unique stamped less selectedOrdinal selectedBeforeCurrent initial
  first finalState globalTrace leading
  (MoreTransitions (Fired {before = first} {afterState = middle}
    nameEq keyEq action tag checked) rest)
  globalSplit prefixOrdinal upper finalOrdinal finalLive
  (GenerationTraceScanStep _ _ tailScan)
  (AlignedStep _ _ _ _ alignedRest) finalQuiet current inactive
  (ActionOccursLater _ _ later) =
    case decEq
      (lookupCurrentGeneration @{nameEq} actor
        (advanceGenerationEnvironment @{nameEq} ordinal action live))
      (Just generation) of
      No noNext =>
        NoRegisteredEpisodeStep (Fired nameEq keyEq action tag checked) rest
          (laterRetirementNoBegin nameEq keyEq actor generation generationActor
            ordinal live stamped selectedOrdinal selectedBeforeCurrent initial
            first middle finalState globalTrace leading action tag checked rest
            globalSplit prefixOrdinal upper alignedRest finalQuiet later)
          (noRegisteredWhenNotCurrent nameEq actor generation generationActor
            (S ordinal)
            (advanceGenerationEnvironment @{nameEq} ordinal action live)
            (advanceGenerationEnvironmentPreservesUnique nameEq ordinal action
              live unique)
            (advanceGenerationEnvironmentPreservesStamped nameEq ordinal action
              live stamped)
            (lteSuccRight less) rest finalOrdinal finalLive tailScan noNext)
      Yes nextCurrent =>
        NoRegisteredEpisodeStep (Fired nameEq keyEq action tag checked) rest
          (laterRetirementNoBegin nameEq keyEq actor generation generationActor
            ordinal live stamped selectedOrdinal selectedBeforeCurrent initial
            first middle finalState globalTrace leading action tag checked rest
            globalSplit prefixOrdinal upper alignedRest finalQuiet later)
          (noRegisteredUntilFutureRetirement nameEq keyEq actor generation
            generationActor (S ordinal)
            (advanceGenerationEnvironment @{nameEq} ordinal action live)
            (advanceGenerationEnvironmentPreservesUnique nameEq ordinal action
              live unique)
            (advanceGenerationEnvironmentPreservesStamped nameEq ordinal action
              live stamped)
            (lteSuccRight less) selectedOrdinal
            (lteSuccRight selectedBeforeCurrent) initial middle finalState
            globalTrace
            (appendTransitions leading
              (MoreTransitions
                (Fired {before = first} {afterState = middle}
                  nameEq keyEq action tag checked) NoTransitions))
            rest
            (extendLeadingDecomposition leading
              (Fired {before = first} {afterState = middle}
                nameEq keyEq action tag checked)
              rest globalTrace globalSplit)
            (trans (transitionCountSnoc leading
              (Fired {before = first} {afterState = middle}
                nameEq keyEq action tag checked))
              (cong S prefixOrdinal))
            upper finalOrdinal finalLive tailScan alignedRest finalQuiet
            nextCurrent
            (oneStepInactivePersistence nameEq keyEq actor generation
              generationActor ordinal live unique stamped first middle action tag
              checked
              (laterRetirementNoBegin nameEq keyEq actor generation
                generationActor ordinal live stamped selectedOrdinal
                selectedBeforeCurrent initial first middle finalState globalTrace
                leading action tag checked rest globalSplit prefixOrdinal upper
                alignedRest finalQuiet later)
              nextCurrent inactive)
            later)

0 appendActionOccursRight :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  ActionOccurs action left ->
  ActionOccurs action (appendTransitions left right)
appendActionOccursRight action (MoreTransitions transition rest) right
  (ActionOccursHere _ _ actionShape) =
    ActionOccursHere transition (appendTransitions rest right) actionShape
appendActionOccursRight action (MoreTransitions transition rest) right
  (ActionOccursLater _ _ later) =
    ActionOccursLater transition (appendTransitions rest right)
      (appendActionOccursRight action rest right later)

record GlobalGeneratedCapital
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (globalTrace : Transitions initial finalState) (selected : name)
  (selectedOrdinal : Nat) (generation : RegistrationGeneration name) where
  constructor MkGlobalGeneratedCapital
  generatedActor : name
  generatedActorComponent : Component key value world error
  generatedRegistration : LocatedGeneratedRegistration generatedActor selected
    generatedActorComponent globalTrace
  0 generatedActorShape : generationName generation = generatedActor
  0 generatedBirthShape : generationBirthOrdinal generation =
    registrationOrdinal generatedRegistration
  0 selectedBeforeGeneratedBirth : LTE selectedOrdinal
    (registrationOrdinal generatedRegistration)
  generatedRetirement : ActionOccurs (ORetire generatedActor)
    (afterRegistration generatedRegistration)

0 globalGeneratedCapitalAtBirth :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (globalTrace : Transitions initial finalState) -> (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected globalTrace) ->
  (generation : RegistrationGeneration name) ->
  (child : name) -> (component : Component key value world error) ->
  (birth : LocatedActionOccurrence (OInsert child (ChildOf selected) component)
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode)))) ->
  (0 stamp : generation = MkRegistrationGeneration child
    (transitionCount (traceBeforeOpening episode) +
      locatedActionOrdinal birth)) ->
  ActionOccurs (ORetire child) (afterActionOccurrence birth) ->
  GlobalGeneratedCapital name key world error value nameEq keyEq globalTrace
    selected (transitionCount (traceBeforeOpening episode)) generation
globalGeneratedCapitalAtBirth nameEq keyEq globalTrace selected episode generation
  child component
  (MkLocatedActionOccurrence before afterState beforeTrace transition rest
    actionShape decomposition) stamp retiresLater =
      MkGlobalGeneratedCapital child component
        (locatedEpisodeChildRegistration nameEq keyEq globalTrace selected child
          component episode
          (MkLocatedActionOccurrence before afterState beforeTrace transition
            rest actionShape decomposition))
        (trans (cong generationName stamp) Refl)
        (trans (cong generationBirthOrdinal stamp)
          (sym (transitionCountAppend (traceBeforeOpening episode)
            beforeTrace)))
        (rewrite transitionCountAppend (traceBeforeOpening episode) beforeTrace in
          leftLTEPlus (transitionCount (traceBeforeOpening episode))
            (transitionCount beforeTrace))
        (appendActionOccursRight (ORetire child) rest
          (traceAfterClosing episode) retiresLater)

0 globalGeneratedCapital :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (globalTrace : Transitions initial finalState) -> (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected globalTrace) ->
  (generation : RegistrationGeneration name) ->
  GeneratedDuring name key world error value selected
    (transitionCount (traceBeforeOpening episode))
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode))) generation ->
  GlobalGeneratedCapital name key world error value nameEq keyEq globalTrace
    selected (transitionCount (traceBeforeOpening episode)) generation
globalGeneratedCapital nameEq keyEq globalTrace selected episode generation
  (MkGeneratedDuring child component birth stamp retiresLater) =
    globalGeneratedCapitalAtBirth nameEq keyEq globalTrace selected episode
      generation child component birth stamp retiresLater

record CompleteGenerationScan
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (ordinal : Nat)
  (live : GenerationEnvironment name)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState) where
  constructor MkCompleteGenerationScan
  completeFinalOrdinal : Nat
  completeFinalLive : GenerationEnvironment name
  0 completeScan : GenerationTraceScan nameEq ordinal live trace
    completeFinalOrdinal completeFinalLive

0 completeGenerationScan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (live : GenerationEnvironment name) ->
  (trace : Transitions first finalState) ->
  CompleteGenerationScan name key world error value nameEq ordinal live trace
completeGenerationScan nameEq ordinal live NoTransitions =
  MkCompleteGenerationScan ordinal live GenerationTraceScanEnd
completeGenerationScan nameEq ordinal live
  (MoreTransitions transition rest) =
    case completeGenerationScan nameEq (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction transition) live)
      rest of
      MkCompleteGenerationScan finalOrdinal finalLive tailScan =>
        MkCompleteGenerationScan finalOrdinal finalLive
          (GenerationTraceScanStep transition rest tailScan)

0 generationScanPreservesBounded :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (live : GenerationEnvironment name) ->
  (trace : Transitions first finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  (scan : GenerationTraceScan nameEq ordinal live trace finalOrdinal finalLive) ->
  GenerationEnvironmentBounded ordinal live ->
  GenerationEnvironmentBounded finalOrdinal finalLive
generationScanPreservesBounded nameEq ordinal live NoTransitions ordinal live
  GenerationTraceScanEnd bounded = bounded
generationScanPreservesBounded nameEq ordinal live
  (MoreTransitions transition rest) finalOrdinal finalLive
  (GenerationTraceScanStep _ _ tailScan) bounded =
    generationScanPreservesBounded nameEq (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction transition) live)
      rest finalOrdinal finalLive tailScan
      (advanceGenerationEnvironmentBounded nameEq ordinal
        (transitionAction transition) live bounded)

0 splitGenerationScanAtAppend :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (live : GenerationEnvironment name) ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq ordinal live (appendTransitions left right)
    finalOrdinal finalLive ->
  SplitGenerationScan name nameEq ordinal live left right finalOrdinal finalLive
splitGenerationScanAtAppend nameEq ordinal live NoTransitions right finalOrdinal
  finalLive scan =
    MkSplitGenerationScan ordinal live GenerationTraceScanEnd scan
splitGenerationScanAtAppend nameEq ordinal live
  (MoreTransitions transition rest) right finalOrdinal finalLive
  (GenerationTraceScanStep _ _ tailScan) =
    case splitGenerationScanAtAppend nameEq (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction transition) live)
      rest right finalOrdinal finalLive tailScan of
      MkSplitGenerationScan middleOrdinal middleLive leftScan rightScan =>
        MkSplitGenerationScan middleOrdinal middleLive
          (GenerationTraceScanStep transition rest leftScan) rightScan

record RegistrationScanCapital
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (startOrdinal : Nat)
  (startLive : GenerationEnvironment name)
  {initial, finalState : SystemState name key value world error}
  (globalTrace : Transitions initial finalState)
  {child, parent : name} {component : Component key value world error}
  (registration : LocatedGeneratedRegistration child parent component
    globalTrace)
  (finalOrdinal : Nat) (finalLive : GenerationEnvironment name) where
  constructor MkRegistrationScanCapital
  registrationBirthOrdinal : Nat
  registrationBirthLive : GenerationEnvironment name
  0 scanBeforeRegistration : GenerationTraceScan nameEq startOrdinal startLive
    (beforeRegistration registration) registrationBirthOrdinal
    registrationBirthLive
  0 scanAfterRegistration : GenerationTraceScan nameEq
    (S registrationBirthOrdinal)
    (advanceGenerationEnvironment @{nameEq} registrationBirthOrdinal
      (transitionAction (registrationTransition registration))
      registrationBirthLive)
    (afterRegistration registration) finalOrdinal finalLive

0 registrationScanCapitalFromSplit :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (startOrdinal : Nat) ->
  (startLive : GenerationEnvironment name) ->
  {initial, finalState : SystemState name key value world error} ->
  (globalTrace : Transitions initial finalState) ->
  {child, parent : name} -> {component : Component key value world error} ->
  (registration : LocatedGeneratedRegistration child parent component
    globalTrace) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  SplitGenerationScan name nameEq startOrdinal startLive
    (beforeRegistration registration)
    (MoreTransitions (registrationTransition registration)
      (afterRegistration registration))
    finalOrdinal finalLive ->
  RegistrationScanCapital name key world error value nameEq startOrdinal
    startLive globalTrace registration finalOrdinal finalLive
registrationScanCapitalFromSplit nameEq startOrdinal startLive globalTrace
  registration finalOrdinal finalLive
  (MkSplitGenerationScan birthOrdinal birthLive beforeScan
    (GenerationTraceScanStep _ _ tailScan)) =
      MkRegistrationScanCapital birthOrdinal birthLive beforeScan tailScan

0 registrationScanCapital :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (startOrdinal : Nat) ->
  (startLive : GenerationEnvironment name) ->
  {initial, finalState : SystemState name key value world error} ->
  {child, parent : name} -> {component : Component key value world error} ->
  (globalTrace : Transitions initial finalState) ->
  (registration : LocatedGeneratedRegistration child parent component
    globalTrace) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq startOrdinal startLive globalTrace finalOrdinal
    finalLive ->
  RegistrationScanCapital name key world error value nameEq startOrdinal
    startLive globalTrace registration finalOrdinal finalLive
registrationScanCapital nameEq startOrdinal startLive globalTrace registration
  finalOrdinal finalLive scan =
    registrationScanCapitalFromSplit nameEq startOrdinal startLive globalTrace
      registration finalOrdinal finalLive
      (splitGenerationScanAtAppend nameEq startOrdinal startLive
        (beforeRegistration registration)
        (MoreTransitions (registrationTransition registration)
          (afterRegistration registration))
        finalOrdinal finalLive
        (replace
          {p = \candidate => GenerationTraceScan nameEq startOrdinal startLive
            candidate finalOrdinal finalLive}
          (sym (registrationDecomposition registration)) scan))

0 alignedHeadRaw :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {before, afterState, finalState : SystemState name key value world error} ->
  (transition : Transition before afterState) ->
  (rest : Transitions afterState finalState) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions transition rest) ->
  applyAction @{nameEq} @{keyEq} (transitionAction transition) before =
    Just (transitionTag transition, afterState)
alignedHeadRaw nameEq keyEq (Fired nameEq keyEq action tag checked) rest
  (AlignedStep action tag checked rest tail) =
    checkedActionProjects nameEq keyEq action _ _ tag checked

0 alignedTailAfterHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {before, afterState, finalState : SystemState name key value world error} ->
  (transition : Transition before afterState) ->
  (rest : Transitions afterState finalState) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions transition rest) ->
  AlignedTransitions name key world error value nameEq keyEq rest
alignedTailAfterHead nameEq keyEq
  (Fired nameEq keyEq action tag checked) rest
  (AlignedStep action tag checked rest tail) = tail

0 generationScanOrdinalCount :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (live : GenerationEnvironment name) ->
  (trace : Transitions first finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq ordinal live trace finalOrdinal finalLive ->
  finalOrdinal = ordinal + transitionCount trace
generationScanOrdinalCount nameEq ordinal live NoTransitions ordinal live
  GenerationTraceScanEnd = sym (plusZeroRightNeutral ordinal)
generationScanOrdinalCount nameEq ordinal live
  (MoreTransitions transition rest) finalOrdinal finalLive
  (GenerationTraceScanStep _ _ tailScan) =
    trans
      (generationScanOrdinalCount nameEq (S ordinal)
        (advanceGenerationEnvironment @{nameEq} ordinal
          (transitionAction transition) live)
        rest finalOrdinal finalLive tailScan)
      (plusSuccRightSucc ordinal (transitionCount rest))

0 currentAfterGeneratedInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (child : name) -> (ordinal : Nat) ->
  (live : GenerationEnvironment name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (action : Action name key value world error) ->
  (0 actionShape : action = OInsert child parent component) ->
  (generation : RegistrationGeneration name) ->
  (0 generationShape : generation =
    MkRegistrationGeneration child ordinal) ->
  lookupCurrentGeneration @{nameEq} child
    (advanceGenerationEnvironment @{nameEq} ordinal action live) =
    Just generation
currentAfterGeneratedInsert nameEq child ordinal live parent component
  (OInsert child parent component) Refl generation generationShape =
    replace
      {p = \observed => lookupCurrentGeneration @{nameEq} child
        (putCurrentGeneration @{nameEq} child
          (MkRegistrationGeneration child ordinal) live) = Just observed}
      (sym generationShape)
      (lookupPutCurrentSelf nameEq child
        (MkRegistrationGeneration child ordinal) live)

0 inactiveAfterGeneratedInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (child : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (action : Action name key value world error) ->
  (0 actionShape : action = OInsert child parent component) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (0 raw : applyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  InactiveFiberAt name key world error value nameEq child afterState
inactiveAfterGeneratedInsert nameEq keyEq child parent component
  (OInsert child parent component) Refl before afterState tag raw =
    MkInactiveFiberAt component parent False emptyOwned Nothing
      (oInsertResultLookup nameEq keyEq child parent component before afterState
        tag raw)

0 generatedInsertCannotBeBegin :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (action : Action name key value world error) ->
  (child : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (0 actionShape : action = OInsert child parent component) ->
  IsBeginAction action -> Void
generatedInsertCannotBeBegin
  (OInsert child parent component) child parent component Refl begin impossible

0 registrationGenerationEta :
  (generation : RegistrationGeneration name) ->
  MkRegistrationGeneration (generationName generation)
    (generationBirthOrdinal generation) = generation
registrationGenerationEta (MkRegistrationGeneration actor ordinal) = Refl

0 registrationGenerationFromFields :
  (generation : RegistrationGeneration name) -> (actor : name) ->
  (ordinal : Nat) ->
  (0 actorShape : generationName generation = actor) ->
  (0 ordinalShape : generationBirthOrdinal generation = ordinal) ->
  generation = MkRegistrationGeneration actor ordinal
registrationGenerationFromFields generation actor ordinal actorShape
  ordinalShape =
    trans (sym (registrationGenerationEta generation))
      (cong2 MkRegistrationGeneration actorShape ordinalShape)

0 noRegisteredAppendAtScan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  (middleOrdinal : Nat) -> (middleLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq ordinal live left middleOrdinal middleLive ->
  NoRegisteredEpisode nameEq registered ordinal live left ->
  NoRegisteredEpisode nameEq registered middleOrdinal middleLive right ->
  NoRegisteredEpisode nameEq registered ordinal live
    (appendTransitions left right)
noRegisteredAppendAtScan nameEq registered ordinal live NoTransitions right
  ordinal live GenerationTraceScanEnd NoRegisteredEpisodeEnd rightProof =
    rightProof
noRegisteredAppendAtScan nameEq registered ordinal live
  (MoreTransitions transition rest) right middleOrdinal middleLive
  (GenerationTraceScanStep _ _ tailScan)
  (NoRegisteredEpisodeStep _ _ noBegin tailProof) rightProof =
    NoRegisteredEpisodeStep transition (appendTransitions rest right) noBegin
      (noRegisteredAppendAtScan nameEq registered (S ordinal)
        (advanceGenerationEnvironment @{nameEq} ordinal
          (transitionAction transition) live)
        rest right middleOrdinal middleLive tailScan tailProof rightProof)

0 combineNoRegistered :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  (headGeneration : RegistrationGeneration name) ->
  (tailGenerations : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (trace : Transitions first finalState) ->
  NoRegisteredEpisode nameEq [headGeneration] ordinal live trace ->
  NoRegisteredEpisode nameEq tailGenerations ordinal live trace ->
  NoRegisteredEpisode nameEq (headGeneration :: tailGenerations) ordinal live
    trace
combineNoRegistered nameEq headGeneration tailGenerations ordinal live
  NoTransitions NoRegisteredEpisodeEnd NoRegisteredEpisodeEnd =
    NoRegisteredEpisodeEnd
combineNoRegistered nameEq headGeneration tailGenerations ordinal live
  (MoreTransitions transition rest)
  (NoRegisteredEpisodeStep _ _ headNoBegin headTail)
  (NoRegisteredEpisodeStep _ _ tailNoBegin tailTail) =
    NoRegisteredEpisodeStep transition rest
      (\begin, owned => case owned of
        (observed ** (current, Here)) =>
          headNoBegin begin (observed ** (current, Here))
        (observed ** (current, There member)) =>
          tailNoBegin begin (observed ** (current, member)))
      (combineNoRegistered nameEq headGeneration tailGenerations (S ordinal)
        (advanceGenerationEnvironment @{nameEq} ordinal
          (transitionAction transition) live)
        rest headTail tailTail)

0 registeredGenerationNoEpisodeAtCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (globalTrace : Transitions initial finalState) -> (selected : name) ->
  (selectedOrdinal : Nat) ->
  (generation : RegistrationGeneration name) -> (actor : name) ->
  (component : Component key value world error) ->
  (registration : LocatedGeneratedRegistration actor selected component
    globalTrace) ->
  (0 generationActor : generationName generation = actor) ->
  (0 generationBirth : generationBirthOrdinal generation =
    registrationOrdinal registration) ->
  (0 selectedBeforeBirth : LTE selectedOrdinal
    (registrationOrdinal registration)) ->
  ActionOccurs (ORetire actor) (afterRegistration registration) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  (cut : RegistrationScanCapital name key world error value nameEq 0 []
    globalTrace registration finalOrdinal finalLive) ->
  (0 aligned : AlignedTransitions name key world error value nameEq keyEq
    globalTrace) ->
  (0 finalQuiet : quiet @{nameEq} @{keyEq} finalState = True) ->
  (0 upper : (closingActor : name) ->
    (closingEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
      closingActor globalTrace) ->
    LTE (transitionCount (traceBeforeOpening closingEpisode))
      selectedOrdinal) ->
  NoRegisteredEpisode nameEq [generation] 0 [] globalTrace
registeredGenerationNoEpisodeAtCut nameEq keyEq globalTrace selected
  selectedOrdinal generation actor component registration generationActor
  generationBirth selectedBeforeBirth retires finalOrdinal finalLive
  (MkRegistrationScanCapital birthOrdinal birthLive beforeScan tailScan)
  aligned finalQuiet upper =
    replace
      {p = \candidate => NoRegisteredEpisode nameEq [generation] 0 [] candidate}
      (registrationDecomposition registration)
      (noRegisteredAppendAtScan nameEq [generation] 0 []
      (beforeRegistration registration)
      (MoreTransitions (registrationTransition registration)
        (afterRegistration registration))
      birthOrdinal birthLive beforeScan
      (noRegisteredBeforeGenerationBirth nameEq generation 0 [] ()
        (beforeRegistration registration) birthOrdinal birthLive beforeScan
        (trans generationBirth
          (sym (generationScanOrdinalCount nameEq 0 []
            (beforeRegistration registration) birthOrdinal birthLive
            beforeScan))))
      (NoRegisteredEpisodeStep (registrationTransition registration)
        (afterRegistration registration)
        (\begin, owned => generatedInsertCannotBeBegin
          (transitionAction (registrationTransition registration)) actor
          (ChildOf selected) component (registrationAction registration) begin)
        (noRegisteredUntilFutureRetirement nameEq keyEq actor generation
          generationActor (S birthOrdinal)
          (advanceGenerationEnvironment @{nameEq} birthOrdinal
            (transitionAction (registrationTransition registration)) birthLive)
          (advanceGenerationEnvironmentPreservesUnique nameEq birthOrdinal
            (transitionAction (registrationTransition registration)) birthLive
            (generationTraceScanPreservesUnique nameEq beforeScan UniqueNil))
          (advanceGenerationEnvironmentPreservesStamped nameEq birthOrdinal
            (transitionAction (registrationTransition registration)) birthLive
            (generationTraceScanPreservesStamped nameEq beforeScan
              emptyGenerationEnvironmentStamped))
          (replace {p = \candidate => LT candidate (S birthOrdinal)}
            (sym (trans generationBirth
              (sym (generationScanOrdinalCount nameEq 0 []
                (beforeRegistration registration) birthOrdinal birthLive
                beforeScan)))) reflexive)
          selectedOrdinal
          (LTESucc (replace {p = \candidate => LTE selectedOrdinal candidate}
            (sym (generationScanOrdinalCount nameEq 0 []
              (beforeRegistration registration) birthOrdinal birthLive
              beforeScan)) selectedBeforeBirth))
          initial (registrationAfter registration) finalState globalTrace
          (appendTransitions (beforeRegistration registration)
            (MoreTransitions (registrationTransition registration)
              NoTransitions))
          (afterRegistration registration)
          (extendLeadingDecomposition (beforeRegistration registration)
            (registrationTransition registration)
            (afterRegistration registration) globalTrace
            (registrationDecomposition registration))
          (trans
            (transitionCountSnoc (beforeRegistration registration)
              (registrationTransition registration))
            (cong S (sym (generationScanOrdinalCount nameEq 0 []
              (beforeRegistration registration) birthOrdinal birthLive
              beforeScan))))
          upper finalOrdinal finalLive tailScan
          (alignedTailAfterHead nameEq keyEq
            (registrationTransition registration)
            (afterRegistration registration)
            (snd (alignedAppendSplit (beforeRegistration registration)
              (MoreTransitions (registrationTransition registration)
                (afterRegistration registration))
              (replace
                {p = \candidate => AlignedTransitions name key world error value
                  nameEq keyEq candidate}
                (sym (registrationDecomposition registration)) aligned))))
          finalQuiet
          (currentAfterGeneratedInsert nameEq actor birthOrdinal birthLive
            (ChildOf selected) component
            (transitionAction (registrationTransition registration))
            (registrationAction registration) generation
            (registrationGenerationFromFields generation actor birthOrdinal
              generationActor
              (trans generationBirth
                (sym (generationScanOrdinalCount nameEq 0 []
                  (beforeRegistration registration) birthOrdinal birthLive
                  beforeScan)))))
          (inactiveAfterGeneratedInsert nameEq keyEq actor (ChildOf selected)
            component (transitionAction (registrationTransition registration))
            (registrationAction registration)
            (registrationBefore registration) (registrationAfter registration)
            (transitionTag (registrationTransition registration))
            (alignedHeadRaw nameEq keyEq
              (registrationTransition registration)
              (afterRegistration registration)
              (snd (alignedAppendSplit (beforeRegistration registration)
                (MoreTransitions (registrationTransition registration)
                  (afterRegistration registration))
                (replace
                  {p = \candidate => AlignedTransitions name key world error
                    value nameEq keyEq candidate}
                  (sym (registrationDecomposition registration)) aligned)))))
          retires)))

0 registeredGenerationNoEpisodeFromCapital :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (globalTrace : Transitions initial finalState) -> (selected : name) ->
  (selectedOrdinal : Nat) -> (generation : RegistrationGeneration name) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  (0 fullScan : GenerationTraceScan nameEq 0 [] globalTrace finalOrdinal
    finalLive) ->
  (0 aligned : AlignedTransitions name key world error value nameEq keyEq
    globalTrace) ->
  (0 finalQuiet : quiet @{nameEq} @{keyEq} finalState = True) ->
  (0 upper : (closingActor : name) ->
    (closingEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
      closingActor globalTrace) ->
    LTE (transitionCount (traceBeforeOpening closingEpisode))
      selectedOrdinal) ->
  GlobalGeneratedCapital name key world error value nameEq keyEq globalTrace
    selected selectedOrdinal generation ->
  NoRegisteredEpisode nameEq [generation] 0 [] globalTrace
registeredGenerationNoEpisodeFromCapital nameEq keyEq globalTrace selected
  selectedOrdinal generation finalOrdinal finalLive fullScan aligned finalQuiet
  upper
  (MkGlobalGeneratedCapital actor component registration generationActor
    generationBirth selectedBeforeBirth retires) =
      registeredGenerationNoEpisodeAtCut nameEq keyEq globalTrace selected
        selectedOrdinal generation actor component registration generationActor
        generationBirth selectedBeforeBirth retires finalOrdinal finalLive
        (registrationScanCapital nameEq 0 [] globalTrace registration
          finalOrdinal finalLive fullScan)
        aligned finalQuiet upper

0 registeredGenerationNoEpisode :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (globalTrace : Transitions initial finalState) -> (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected globalTrace) ->
  (generation : RegistrationGeneration name) ->
  GeneratedDuring name key world error value selected
    (transitionCount (traceBeforeOpening episode))
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode))) generation ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  (0 fullScan : GenerationTraceScan nameEq 0 [] globalTrace finalOrdinal
    finalLive) ->
  (0 aligned : AlignedTransitions name key world error value nameEq keyEq
    globalTrace) ->
  (0 finalQuiet : quiet @{nameEq} @{keyEq} finalState = True) ->
  (0 upper : (closingActor : name) ->
    (closingEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
      closingActor globalTrace) ->
    LTE (transitionCount (traceBeforeOpening closingEpisode))
      (transitionCount (traceBeforeOpening episode))) ->
  NoRegisteredEpisode nameEq [generation] 0 [] globalTrace
registeredGenerationNoEpisode nameEq keyEq globalTrace selected episode generation
  generated finalOrdinal finalLive fullScan aligned finalQuiet upper =
    registeredGenerationNoEpisodeFromCapital nameEq keyEq globalTrace selected
      (transitionCount (traceBeforeOpening episode)) generation finalOrdinal
      finalLive fullScan aligned finalQuiet upper
      (globalGeneratedCapital nameEq keyEq globalTrace selected episode generation
        generated)

0 noRegisteredEmptyGenerations :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (live : GenerationEnvironment name) ->
  (trace : Transitions first finalState) ->
  NoRegisteredEpisode nameEq [] ordinal live trace
noRegisteredEmptyGenerations nameEq ordinal live NoTransitions =
  NoRegisteredEpisodeEnd
noRegisteredEmptyGenerations nameEq ordinal live
  (MoreTransitions transition rest) =
    NoRegisteredEpisodeStep transition rest
      (\begin, owned => case owned of
        (generation ** (current, member)) => absurd member)
      (noRegisteredEmptyGenerations nameEq (S ordinal)
        (advanceGenerationEnvironment @{nameEq} ordinal
          (transitionAction transition) live)
        rest)

0 allGeneratedChildrenHaveNoEpisode :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (globalTrace : Transitions initial finalState) -> (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected globalTrace) ->
  (registered : List (RegistrationGeneration name)) ->
  (0 sound : (generation : RegistrationGeneration name) ->
    Elem generation registered ->
    GeneratedDuring name key world error value selected
      (transitionCount (traceBeforeOpening episode))
      (MoreTransitions
        (beginTransition (closedOpening (locatedEpisode episode)))
        (closedTransitions (locatedEpisode episode))) generation) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  (0 fullScan : GenerationTraceScan nameEq 0 [] globalTrace finalOrdinal
    finalLive) ->
  (0 aligned : AlignedTransitions name key world error value nameEq keyEq
    globalTrace) ->
  (0 finalQuiet : quiet @{nameEq} @{keyEq} finalState = True) ->
  (0 upper : (closingActor : name) ->
    (closingEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
      closingActor globalTrace) ->
    LTE (transitionCount (traceBeforeOpening closingEpisode))
      (transitionCount (traceBeforeOpening episode))) ->
  NoRegisteredEpisode nameEq registered 0 [] globalTrace
allGeneratedChildrenHaveNoEpisode nameEq keyEq globalTrace selected episode []
  sound finalOrdinal finalLive fullScan aligned finalQuiet upper =
    noRegisteredEmptyGenerations nameEq 0 [] globalTrace
allGeneratedChildrenHaveNoEpisode nameEq keyEq globalTrace selected episode
  (generation :: rest) sound finalOrdinal finalLive fullScan aligned finalQuiet
  upper =
    combineNoRegistered nameEq generation rest 0 [] globalTrace
      (registeredGenerationNoEpisode nameEq keyEq globalTrace selected episode
        generation (sound generation Here) finalOrdinal finalLive fullScan
        aligned finalQuiet upper)
      (allGeneratedChildrenHaveNoEpisode nameEq keyEq globalTrace selected
        episode rest (\candidate, member => sound candidate (There member))
        finalOrdinal finalLive fullScan aligned finalQuiet upper)

0 selectedChildrenHaveNoEpisodeFromComplete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (globalTrace : Transitions initial finalState) -> (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected globalTrace) ->
  (inventory : ChildGenerationInventory name key world error value selected
    (transitionCount (traceBeforeOpening episode))
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode)))) ->
  (0 aligned : AlignedTransitions name key world error value nameEq keyEq
    globalTrace) ->
  (0 finalQuiet : quiet @{nameEq} @{keyEq} finalState = True) ->
  (0 upper : (closingActor : name) ->
    (closingEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
      closingActor globalTrace) ->
    LTE (transitionCount (traceBeforeOpening closingEpisode))
      (transitionCount (traceBeforeOpening episode))) ->
  CompleteGenerationScan name key world error value nameEq 0 [] globalTrace ->
  NoRegisteredEpisode nameEq (selectedGenerations inventory) 0 [] globalTrace
selectedChildrenHaveNoEpisodeFromComplete nameEq keyEq globalTrace selected
  episode inventory aligned finalQuiet upper
  (MkCompleteGenerationScan finalOrdinal finalLive fullScan) =
    allGeneratedChildrenHaveNoEpisode nameEq keyEq globalTrace selected episode
      (selectedGenerations inventory) (selectedGenerationSound inventory)
      finalOrdinal finalLive fullScan aligned finalQuiet upper

0 selectedChildrenHaveNoEpisode :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (globalTrace : Transitions initial finalState) -> (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected globalTrace) ->
  (inventory : ChildGenerationInventory name key world error value selected
    (transitionCount (traceBeforeOpening episode))
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode)))) ->
  (0 aligned : AlignedTransitions name key world error value nameEq keyEq
    globalTrace) ->
  (0 finalQuiet : quiet @{nameEq} @{keyEq} finalState = True) ->
  (0 upper : (closingActor : name) ->
    (closingEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
      closingActor globalTrace) ->
    LTE (transitionCount (traceBeforeOpening closingEpisode))
      (transitionCount (traceBeforeOpening episode))) ->
  NoRegisteredEpisode nameEq (selectedGenerations inventory) 0 [] globalTrace
selectedChildrenHaveNoEpisode nameEq keyEq globalTrace selected episode inventory
  aligned finalQuiet upper =
    selectedChildrenHaveNoEpisodeFromComplete nameEq keyEq globalTrace selected
      episode inventory aligned finalQuiet upper
      (completeGenerationScan nameEq 0 [] globalTrace)

0 maximalCandidateFromGenerationScan :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq trace) ->
  (scan : ClosingEpisodeScan name key world error value nameEq keyEq trace) ->
  (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected trace) ->
  ((other : ClosingEpisodeOccurrence name key world error value nameEq keyEq
      trace) ->
    Elem other (scannedClosingOccurrences scan) ->
    LTE (scannedClosingOrdinal other)
      (transitionCount (traceBeforeOpening episode))) ->
  (startOrdinal : Nat) -> (startLive : GenerationEnvironment name) ->
  (beforeScan : GenerationTraceScan nameEq 0 []
    (traceBeforeOpening episode) startOrdinal startLive) ->
  ((inventory : ChildGenerationInventory name key world error value selected
      startOrdinal
      (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
        (closedTransitions (locatedEpisode episode)))) ->
    NoRegisteredEpisode nameEq (selectedGenerations inventory) 0 [] trace) ->
  DeletableClosingEpisode name key world error value nameEq keyEq trace
maximalCandidateFromGenerationScan nameEq keyEq protocol trace premises scan
  selected episode upper startOrdinal startLive beforeScan noRegistered =
    MkDeletableClosingEpisode selected episode
      (selectedGenerations
        (buildChildGenerationInventory nameEq selected startOrdinal
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode episode)))
            (closedTransitions (locatedEpisode episode)))
          (\child, component, birth =>
            selectedChildRetirementAfterBirth protocol nameEq keyEq trace selected
              child component episode (replayAligned (chainReplayCapital premises))
              (replayDiscipline (chainReplayCapital premises)) birth)))
      (selectedInventoryOutside protocol nameEq keyEq trace selected episode
        (replayAligned (chainReplayCapital premises))
        (replayDiscipline (chainReplayCapital premises)) startOrdinal
        (buildChildGenerationInventory nameEq selected startOrdinal
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode episode)))
            (closedTransitions (locatedEpisode episode)))
          (\child, component, birth =>
            selectedChildRetirementAfterBirth protocol nameEq keyEq trace selected
              child component episode (replayAligned (chainReplayCapital premises))
              (replayDiscipline (chainReplayCapital premises)) birth)))
      startOrdinal startLive beforeScan
      (registeredDuringFromInventory
        (buildChildGenerationInventory nameEq selected startOrdinal
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode episode)))
            (closedTransitions (locatedEpisode episode)))
          (\child, component, birth =>
            selectedChildRetirementAfterBirth protocol nameEq keyEq trace selected
              child component episode (replayAligned (chainReplayCapital premises))
              (replayDiscipline (chainReplayCapital premises)) birth)))
      (maximalClosingHasNoScopedDependent scan selected episode upper
        startOrdinal startLive)
      (noRegistered
        (buildChildGenerationInventory nameEq selected startOrdinal
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode episode)))
            (closedTransitions (locatedEpisode episode)))
          (\child, component, birth =>
            selectedChildRetirementAfterBirth protocol nameEq keyEq trace selected
              child component episode (replayAligned (chainReplayCapital premises))
              (replayDiscipline (chainReplayCapital premises)) birth)))

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
  (0 scan : ClosingEpisodeScan name key world error value nameEq keyEq trace) ->
  Type where
  NoMaximalClosingEpisode :
    (0 empty : scannedClosingOccurrences scan = []) ->
    MaximalClosingSelection name key world error value protocol nameEq keyEq
      trace premises scan
  SelectedMaximalClosingEpisode :
    (0 candidate : DeletableClosingEpisode name key world error value nameEq keyEq
      trace) ->
    (0 selected : Elem (transitionCount
      (traceBeforeOpening (selectedEpisode candidate)))
      (map DGamma.CP5ConfluenceDeletionChainSpike.scannedClosingOrdinal
        (scannedClosingOccurrences scan))) ->
    MaximalClosingSelection name key world error value protocol nameEq keyEq
      trace premises scan

record ExactZeroGenerationScan
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState) where
  constructor MkExactZeroGenerationScan
  exactZeroFinalLive : GenerationEnvironment name
  0 exactZeroScan : GenerationTraceScan nameEq 0 [] trace
    (transitionCount trace) exactZeroFinalLive

0 exactZeroGenerationScanFromComplete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (trace : Transitions first finalState) ->
  CompleteGenerationScan name key world error value nameEq 0 [] trace ->
  ExactZeroGenerationScan name key world error value nameEq trace
exactZeroGenerationScanFromComplete nameEq trace
  (MkCompleteGenerationScan finalOrdinal finalLive scan) =
    MkExactZeroGenerationScan finalLive
      (replace
        {p = \candidate => GenerationTraceScan nameEq 0 [] trace candidate
          finalLive}
        (generationScanOrdinalCount nameEq 0 [] trace finalOrdinal finalLive scan)
        scan)

0 exactZeroGenerationScan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (trace : Transitions first finalState) ->
  ExactZeroGenerationScan name key world error value nameEq trace
exactZeroGenerationScan nameEq trace =
  exactZeroGenerationScanFromComplete nameEq trace
    (completeGenerationScan nameEq 0 [] trace)

0 maximalSelectionFromPrefixScan :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq trace) ->
  (scan : ClosingEpisodeScan name key world error value nameEq keyEq trace) ->
  (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected trace) ->
  (0 selectedMember : Elem (transitionCount (traceBeforeOpening episode))
    (map DGamma.CP5ConfluenceDeletionChainSpike.scannedClosingOrdinal
      (scannedClosingOccurrences scan))) ->
  (0 upper : (other : ClosingEpisodeOccurrence name key world error value
      nameEq keyEq trace) ->
    Elem other (scannedClosingOccurrences scan) ->
    LTE (scannedClosingOrdinal other)
      (transitionCount (traceBeforeOpening episode))) ->
  ExactZeroGenerationScan name key world error value nameEq
    (traceBeforeOpening episode) ->
  MaximalClosingSelection name key world error value protocol nameEq keyEq trace
    premises scan
maximalSelectionFromPrefixScan nameEq keyEq protocol trace premises scan selected
  episode selectedMember upper
  (MkExactZeroGenerationScan startLive beforeScan) =
    SelectedMaximalClosingEpisode
      (maximalCandidateFromGenerationScan nameEq keyEq protocol trace premises
        scan selected episode upper
        (transitionCount (traceBeforeOpening episode)) startLive beforeScan
        (\inventory => selectedChildrenHaveNoEpisode nameEq keyEq trace selected
          episode inventory (replayAligned (chainReplayCapital premises))
          (replayQuiet (chainReplayCapital premises))
          (maximalClosingOrdinalBound scan selected episode upper)))
      selectedMember

0 maximalSelectionFromOccurrence :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq trace) ->
  (scan : ClosingEpisodeScan name key world error value nameEq keyEq trace) ->
  (occurrence : ClosingEpisodeOccurrence name key world error value nameEq keyEq
    trace) ->
  (0 member : Elem occurrence (scannedClosingOccurrences scan)) ->
  (0 upper : (other : ClosingEpisodeOccurrence name key world error value
      nameEq keyEq trace) ->
    Elem other (scannedClosingOccurrences scan) ->
    LTE (scannedClosingOrdinal other) (scannedClosingOrdinal occurrence)) ->
  MaximalClosingSelection name key world error value protocol nameEq keyEq trace
    premises scan
maximalSelectionFromOccurrence nameEq keyEq protocol trace premises scan
  (ErasedClosingEpisodeOccurrence selected episode) member upper =
    maximalSelectionFromPrefixScan nameEq keyEq protocol trace premises scan
      selected episode (elemMap scannedClosingOrdinal member) upper
      (exactZeroGenerationScan nameEq (traceBeforeOpening episode))

0 maximalSelectionFromMaximum :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq trace) ->
  (scan : ClosingEpisodeScan name key world error value nameEq keyEq trace) ->
  MaximumBy DGamma.CP5ConfluenceDeletionChainSpike.scannedClosingOrdinal
    (scannedClosingOccurrences scan) ->
  MaximalClosingSelection name key world error value protocol nameEq keyEq trace
    premises scan
maximalSelectionFromMaximum nameEq keyEq protocol trace premises scan
  (MkMaximumBy maximum member upper) =
    maximalSelectionFromOccurrence nameEq keyEq protocol trace premises scan
      maximum member upper

0 maximalSelectionFromList :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq trace) ->
  (scan : ClosingEpisodeScan name key world error value nameEq keyEq trace) ->
  (occurrences : List (ClosingEpisodeOccurrence name key world error value
    nameEq keyEq trace)) ->
  (0 occurrencesShape : scannedClosingOccurrences scan = occurrences) ->
  MaximalClosingSelection name key world error value protocol nameEq keyEq trace
    premises scan
maximalSelectionFromList nameEq keyEq protocol trace premises scan []
  occurrencesShape = NoMaximalClosingEpisode occurrencesShape
maximalSelectionFromList nameEq keyEq protocol trace premises scan
  (head :: tail) occurrencesShape =
    maximalSelectionFromMaximum nameEq keyEq protocol trace premises scan
      (replace
        {p = \items => MaximumBy
          DGamma.CP5ConfluenceDeletionChainSpike.scannedClosingOrdinal items}
        (sym occurrencesShape)
        (chooseMaximumBy
          DGamma.CP5ConfluenceDeletionChainSpike.scannedClosingOrdinal head
          tail))

||| O8 maximal candidate selection is no longer bundled with D72 enrichment.
public export
0 selectMaximalClosingEpisodeSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (initial, finalState : SystemState name key value world error) ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq trace) ->
  (0 scan : ClosingEpisodeScan name key world error value nameEq keyEq trace) ->
  MaximalClosingSelection name key world error value protocol nameEq keyEq trace
    premises scan
selectMaximalClosingEpisodeSpike nameEq keyEq protocol initial finalState trace
  premises scan =
    maximalSelectionFromList nameEq keyEq protocol trace premises scan
      (scannedClosingOccurrences scan) Refl

||| The selected scan fixes the exact global opening ordinal used by every
||| generation-scoped Lemma-72 consumer.
0 deletionCandidateStartOrdinalExact :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, finalState : SystemState name key value world error} ->
  {trace : Transitions initial finalState} ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq
    trace) ->
  transitionCount (traceBeforeOpening (selectedEpisode candidate)) =
    selectedStartOrdinal candidate
deletionCandidateStartOrdinalExact {nameEq} candidate =
  sym (generationScanOrdinalCount nameEq 0 []
    (traceBeforeOpening (selectedEpisode candidate))
    (selectedStartOrdinal candidate) (selectedStartLive candidate)
    (selectedBeforeScan candidate))

0 appendLeftOccursScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState, stepBefore, stepAfter :
    SystemState name key value world error} ->
  {transition : Transition stepBefore stepAfter} ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  OccursIn transition left ->
  OccursIn transition (appendTransitions left right)
appendLeftOccursScoped NoTransitions right occurs impossible
appendLeftOccursScoped (MoreTransitions head rest) right OccursHere = OccursHere
appendLeftOccursScoped (MoreTransitions head rest) right (OccursLater later) =
  OccursLater (appendLeftOccursScoped rest right later)

0 appendRightOccursScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState, stepBefore, stepAfter :
    SystemState name key value world error} ->
  {transition : Transition stepBefore stepAfter} ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  OccursIn transition right ->
  OccursIn transition (appendTransitions left right)
appendRightOccursScoped NoTransitions right occurs = occurs
appendRightOccursScoped (MoreTransitions head rest) right occurs =
  OccursLater (appendRightOccursScoped rest right occurs)

0 transportOccursScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState, stepBefore, stepAfter :
    SystemState name key value world error} ->
  {transition : Transition stepBefore stepAfter} ->
  {left, right : Transitions first finalState} ->
  (0 exactTrace : left = right) ->
  OccursIn transition left -> OccursIn transition right
transportOccursScoped Refl occurs = occurs

0 scopedSpanningDecomposition :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {actor : name} ->
  {initial, preStart, opened, anchorState, closeBefore, closeAfter, finalState :
    SystemState name key value world error} ->
  (beforeOpening : Transitions initial preStart) ->
  (opening : BeginStep nameEq keyEq actor preStart opened) ->
  (afterOpening : Transitions opened anchorState) ->
  (beforeClosing : Transitions anchorState closeBefore) ->
  (closing : UnloadStep nameEq keyEq actor closeBefore closeAfter) ->
  (afterClosing : Transitions closeAfter finalState) ->
  (leftTrace : Transitions initial anchorState) ->
  (rightTrace : Transitions anchorState finalState) ->
  (0 openingSplit : appendTransitions beforeOpening
    (MoreTransitions (beginTransition opening) afterOpening) = leftTrace) ->
  (0 closingSplit : appendTransitions beforeClosing
    (MoreTransitions (unloadTransition closing) afterClosing) = rightTrace) ->
  appendTransitions beforeOpening
    (MoreTransitions (beginTransition opening)
      (appendTransitions (appendTransitions afterOpening beforeClosing)
        (MoreTransitions (unloadTransition closing) afterClosing))) =
  appendTransitions leftTrace rightTrace
scopedSpanningDecomposition beforeOpening opening afterOpening beforeClosing
  closing afterClosing leftTrace rightTrace openingSplit closingSplit =
    rewrite appendTransitionsAssociative afterOpening beforeClosing
      (MoreTransitions (unloadTransition closing) afterClosing) in
    rewrite closingSplit in
    rewrite sym (appendTransitionsAssociative beforeOpening
      (MoreTransitions (beginTransition opening) afterOpening) rightTrace) in
    rewrite openingSplit in Refl

0 extendLocatedClosingRightScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {actor : name} ->
  {prefixInitial, prefixFinal, globalFinal :
    SystemState name key value world error} ->
  (prefixTrace : Transitions prefixInitial prefixFinal) ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq actor
    prefixTrace) ->
  (suffixTrace : Transitions prefixFinal globalFinal) ->
  (global : Transitions prefixInitial globalFinal) ->
  (0 exactTrace : appendTransitions prefixTrace suffixTrace = global) ->
  LocatedClosedEpisode name key world error value nameEq keyEq actor global
extendLocatedClosingRightScoped prefixTrace located suffixTrace global
  exactTrace =
    replace
      {p = \candidate => LocatedClosedEpisode name key world error value nameEq
        keyEq actor candidate}
      exactTrace
      (appendLocatedClosingEpisodeRight prefixTrace located suffixTrace)

0 selectedGenerationConsumerOrdinalScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, selectedBefore, selectedAfter, foreignBefore :
    SystemState name key value world error} ->
  (selectedPrefixTrace : Transitions first selectedBefore) ->
  (selectedToForeign : Transitions selectedAfter foreignBefore) ->
  (foreignPrefixTrace : Transitions first foreignBefore) ->
  (selectedStartOrdinal : Nat) ->
  (0 selectedOrdinalExact :
    transitionCount selectedPrefixTrace = selectedStartOrdinal) ->
  (0 foreignOrdinalExact :
    transitionCount foreignPrefixTrace =
      transitionCount selectedPrefixTrace + S (transitionCount selectedToForeign)) ->
  transitionCount foreignPrefixTrace =
    selectedStartOrdinal + S (transitionCount selectedToForeign)
selectedGenerationConsumerOrdinalScoped selectedPrefixTrace selectedToForeign
  foreignPrefixTrace selectedStartOrdinal selectedOrdinalExact
  foreignOrdinalExact =
    trans foreignOrdinalExact
      (cong (\ordinal => ordinal + S (transitionCount selectedToForeign))
        selectedOrdinalExact)

0 locatedActionFromOccursScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {stepBefore, stepAfter, first, finalState :
    SystemState name key value world error} ->
  (transition : Transition stepBefore stepAfter) ->
  (action : Action name key value world error) ->
  (0 actionShape : transitionAction transition = action) ->
  (trace : Transitions first finalState) ->
  OccursIn transition trace ->
  LocatedActionOccurrence action trace
locatedActionFromOccursScoped transition action actionShape trace occurs =
  case locateTransitionOccurrence transition trace occurs of
    MkLocatedTransitionOccurrence beforeTrace afterTrace decomposition =>
      MkLocatedActionOccurrence stepBefore stepAfter beforeTrace transition
        afterTrace actionShape decomposition

0 insideSelectedContradictsScopedMaximality :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, finalState : SystemState name key value world error} ->
  {global : Transitions initial finalState} ->
  (selected, consumer : name) ->
  (selectedStartOrdinal : Nat) ->
  (selectedStartLive : GenerationEnvironment name) ->
  (selectedEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  (consumerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    consumer global) ->
  (selectedToConsumer : Transitions
    (closedStartState (locatedEpisode selectedEpisode))
    (locatedPreStart consumerEpisode)) ->
  (consumerToAnchor : Transitions
    (closedStartState (locatedEpisode consumerEpisode))
    (lastInstalledState (locatedEpisode selectedEpisode))) ->
  (0 selectedInsideExact :
    closedInside (locatedEpisode selectedEpisode) =
      appendTransitions selectedToConsumer
        (MoreTransitions
          (beginTransition (closedOpening (locatedEpisode consumerEpisode)))
          consumerToAnchor)) ->
  (0 consumerPrefixCountExact :
    transitionCount (traceBeforeOpening consumerEpisode) =
      transitionCount (traceBeforeOpening selectedEpisode) +
        S (transitionCount selectedToConsumer)) ->
  (0 selectedOrdinalExact :
    transitionCount (traceBeforeOpening selectedEpisode) =
      selectedStartOrdinal) ->
  (0 noDependent : NoDependentClosingEpisodeForGeneration
    {nameEq = nameEq} {keyEq = keyEq} {global = global} selected
    selectedStartOrdinal selectedStartLive selectedEpisode) ->
  PrecedenceEdge nameEq selected consumer
    (closedStartState (locatedEpisode consumerEpisode)) ->
  Void
insideSelectedContradictsScopedMaximality selected consumer
  selectedStartOrdinal selectedStartLive selectedEpisode consumerEpisode
  selectedToConsumer consumerToAnchor selectedInsideExact
  consumerPrefixCountExact selectedOrdinalExact noDependent edge =
    noDependent consumer consumerEpisode
      (MkGenerationScopedClosingStart selectedOrdinalExact
        (MkLocatedActionOccurrence (locatedPreStart consumerEpisode)
          (closedStartState (locatedEpisode consumerEpisode)) selectedToConsumer
          (beginTransition (closedOpening (locatedEpisode consumerEpisode)))
          consumerToAnchor Refl (sym selectedInsideExact))
        (selectedGenerationConsumerOrdinalScoped
          (traceBeforeOpening selectedEpisode) selectedToConsumer
          (traceBeforeOpening consumerEpisode) selectedStartOrdinal
          selectedOrdinalExact consumerPrefixCountExact))
      edge

record ScopedClosingLocalization
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (actor : name)
  {prefixInitial, prefixFinal, globalFinal, stepBefore, stepAfter :
    SystemState name key value world error}
  (transition : Transition stepBefore stepAfter)
  (prefixTrace : Transitions prefixInitial prefixFinal)
  (global : Transitions prefixInitial globalFinal)
  (anchor : ForeignLifecycleInstalledAnchor name key world error value nameEq
    keyEq actor transition prefixTrace) where
  constructor MkScopedClosingLocalization
  localizedPrefixEpisode : LocatedClosedEpisode name key world error value
    nameEq keyEq actor prefixTrace
  localizedGlobalEpisode : LocatedClosedEpisode name key world error value
    nameEq keyEq actor global
  0 localizedOpeningCountExact : transitionCount
    (traceBeforeOpening localizedGlobalEpisode) = transitionCount
    (traceBeforeOpening localizedPrefixEpisode)
  0 localizedOpeningStateExact :
    closedStartState (locatedEpisode localizedGlobalEpisode) =
      closedStartState (locatedEpisode localizedPrefixEpisode)
  localizedActivationToAnchor : Transitions
    (closedStartState (locatedEpisode localizedPrefixEpisode))
    (lifecycleInstalledState anchor)
  0 localizedActivationInstalled : InstalledTrace name key world error value
    nameEq keyEq actor localizedActivationToAnchor
  0 localizedOpeningSplit :
    appendTransitions (traceBeforeOpening localizedPrefixEpisode)
      (MoreTransitions
        (beginTransition (closedOpening (locatedEpisode localizedPrefixEpisode)))
        localizedActivationToAnchor) = lifecycleBeforeInstalled anchor
  localizedAnchorToClosing : Transitions (lifecycleInstalledState anchor)
    (lastInstalledState (locatedEpisode localizedPrefixEpisode))
  0 localizedInsideSplit :
    appendTransitions localizedActivationToAnchor localizedAnchorToClosing =
      closedInside (locatedEpisode localizedPrefixEpisode)

0 buildScopedClosingFromOpening :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {actor : name} ->
  {prefixInitial, prefixFinal, globalFinal, stepBefore, stepAfter, preStart,
    opened : SystemState name key value world error} ->
  (transition : Transition stepBefore stepAfter) ->
  (prefixTrace : Transitions prefixInitial prefixFinal) ->
  (anchor : ForeignLifecycleInstalledAnchor name key world error value nameEq
    keyEq actor transition prefixTrace) ->
  (beforeOpening : Transitions prefixInitial preStart) ->
  (opening : BeginStep nameEq keyEq actor preStart opened) ->
  (afterOpening : Transitions opened (lifecycleInstalledState anchor)) ->
  (0 openingSplit : appendTransitions beforeOpening
    (MoreTransitions (beginTransition opening) afterOpening) =
      lifecycleBeforeInstalled anchor) ->
  (0 installedAfterOpening : InstalledTrace name key world error value nameEq
    keyEq actor afterOpening) ->
  (closingResult : FirstClosingResult name key world error value nameEq keyEq
    actor (lifecycleAfterInstalled anchor)) ->
  (suffixTrace : Transitions prefixFinal globalFinal) ->
  (global : Transitions prefixInitial globalFinal) ->
  (0 globalSplit : appendTransitions prefixTrace suffixTrace = global) ->
  ScopedClosingLocalization name key world error value nameEq keyEq actor
    transition prefixTrace global anchor
buildScopedClosingFromOpening transition prefixTrace anchor beforeOpening opening
  afterOpening openingSplit installedAfterOpening closingResult suffixTrace
  global globalSplit =
    case closingResult of
      MkFirstClosingResult closeBefore closeAfter beforeClosing installedBefore
        closing afterClosing closingSplit =>
          MkScopedClosingLocalization
            (MkLocatedClosedEpisode preStart closeAfter beforeOpening
              (MkClosedEpisode opened closeBefore opening
                (appendTransitions afterOpening beforeClosing)
                (appendInstalledTrace afterOpening beforeClosing
                  installedAfterOpening installedBefore)
                closing)
              afterClosing
              (trans
                (rewrite appendTransitionsAssociative
                  (appendTransitions afterOpening beforeClosing)
                  (MoreTransitions (unloadTransition closing) NoTransitions)
                  afterClosing in
                    scopedSpanningDecomposition beforeOpening opening
                      afterOpening beforeClosing closing afterClosing
                      (lifecycleBeforeInstalled anchor)
                      (lifecycleAfterInstalled anchor) openingSplit closingSplit)
                (lifecycleAnchorDecomposition anchor)))
            (extendLocatedClosingRightScoped prefixTrace
              (MkLocatedClosedEpisode preStart closeAfter beforeOpening
                (MkClosedEpisode opened closeBefore opening
                  (appendTransitions afterOpening beforeClosing)
                  (appendInstalledTrace afterOpening beforeClosing
                    installedAfterOpening installedBefore)
                  closing)
                afterClosing
                (trans
                  (rewrite appendTransitionsAssociative
                    (appendTransitions afterOpening beforeClosing)
                    (MoreTransitions (unloadTransition closing) NoTransitions)
                    afterClosing in
                      scopedSpanningDecomposition beforeOpening opening
                        afterOpening beforeClosing closing afterClosing
                        (lifecycleBeforeInstalled anchor)
                        (lifecycleAfterInstalled anchor) openingSplit
                        closingSplit)
                  (lifecycleAnchorDecomposition anchor)))
              suffixTrace global globalSplit)
            Refl Refl afterOpening installedAfterOpening openingSplit beforeClosing
            Refl

0 buildScopedClosingFromOpeningResult :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {actor : name} ->
  {prefixInitial, prefixFinal, globalFinal, stepBefore, stepAfter :
    SystemState name key value world error} ->
  (transition : Transition stepBefore stepAfter) ->
  (prefixTrace : Transitions prefixInitial prefixFinal) ->
  (anchor : ForeignLifecycleInstalledAnchor name key world error value nameEq
    keyEq actor transition prefixTrace) ->
  (openingResult : LastOpeningResult name key world error value nameEq keyEq
    actor (lifecycleBeforeInstalled anchor)) ->
  (closingResult : FirstClosingResult name key world error value nameEq keyEq
    actor (lifecycleAfterInstalled anchor)) ->
  (suffixTrace : Transitions prefixFinal globalFinal) ->
  (global : Transitions prefixInitial globalFinal) ->
  (0 globalSplit : appendTransitions prefixTrace suffixTrace = global) ->
  ScopedClosingLocalization name key world error value nameEq keyEq actor
    transition prefixTrace global anchor
buildScopedClosingFromOpeningResult transition prefixTrace anchor openingResult
  closingResult suffixTrace global globalSplit =
    case openingResult of
      MkLastOpeningResult preStart opened beforeOpening opening afterOpening
        openingSplit installedAfterOpening =>
          buildScopedClosingFromOpening transition prefixTrace anchor
            beforeOpening opening afterOpening openingSplit
            installedAfterOpening closingResult suffixTrace global globalSplit

0 localizeScopedClosing :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {prefixInitial, prefixFinal, globalFinal, stepBefore, stepAfter :
    SystemState name key value world error} ->
  (transition : Transition stepBefore stepAfter) ->
  (prefixTrace : Transitions prefixInitial prefixFinal) ->
  (0 aligned : AlignedTransitions name key world error value nameEq keyEq
    prefixTrace) ->
  (0 initialEmpty : bindings (registry prefixInitial) = []) ->
  (anchor : ForeignLifecycleInstalledAnchor name key world error value nameEq
    keyEq actor transition prefixTrace) ->
  (closingResult : FirstClosingResult name key world error value nameEq keyEq
    actor (lifecycleAfterInstalled anchor)) ->
  (suffixTrace : Transitions prefixFinal globalFinal) ->
  (global : Transitions prefixInitial globalFinal) ->
  (0 globalSplit : appendTransitions prefixTrace suffixTrace = global) ->
  ScopedClosingLocalization name key world error value nameEq keyEq actor
    transition prefixTrace global anchor
localizeScopedClosing nameEq keyEq actor transition prefixTrace aligned
  initialEmpty anchor closingResult suffixTrace global globalSplit =
    buildScopedClosingFromOpeningResult transition prefixTrace anchor
      (extractLastOpening nameEq keyEq actor (lifecycleBeforeInstalled anchor)
        (fst (alignedAppendSplit (lifecycleBeforeInstalled anchor)
          (lifecycleAfterInstalled anchor)
          (replace
            {p = \candidate => AlignedTransitions name key world error value
              nameEq keyEq candidate}
            (sym (lifecycleAnchorDecomposition anchor)) aligned)))
        (emptyRegistryUninstalled nameEq actor prefixInitial initialEmpty)
        (lifecycleAnchorInstalled anchor))
      closingResult suffixTrace global globalSplit

0 installedTraceEndScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {actor : name} ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  InstalledTrace name key world error value nameEq keyEq actor trace ->
  installedAt @{nameEq} actor finalState = True
installedTraceEndScoped NoTransitions (InstalledEnd installed) = installed
installedTraceEndScoped
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
  (InstalledStep action tag checked rest sourceInstalled tailInstalled) =
    installedTraceEndScoped rest tailInstalled

0 installedSourceContradictsBeginScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {before, afterState : SystemState name key value world error} ->
  (opening : BeginStep nameEq keyEq actor before afterState) ->
  installedAt @{nameEq} actor before = True ->
  Void
installedSourceContradictsBeginScoped nameEq keyEq actor {before} {afterState}
  opening sourceInstalled =
    falseNotTrueO7
      (trans
        (sym (fst (snd (lBeginBoundary nameEq keyEq actor before afterState
          LBeginTag (beginEquation opening)))))
        sourceInstalled)

0 installedTraceExcludesBeginScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {first, finalState, beginBefore, beginAfter :
    SystemState name key value world error} ->
  (insideTrace : Transitions first finalState) ->
  (0 installedTrace : InstalledTrace name key world error value nameEq keyEq
    actor insideTrace) ->
  (opening : BeginStep nameEq keyEq actor beginBefore beginAfter) ->
  OccursIn (beginTransition opening) insideTrace ->
  Void
installedTraceExcludesBeginScoped nameEq keyEq actor insideTrace installedTrace
  opening occurs =
    case splitInstalledAtOccurrence (beginTransition opening) insideTrace
      installedTrace occurs of
      MkInstalledOccurrenceSplit beforeOccurrence afterOccurrence
        installedBefore installedAfter sourceInstalled targetInstalled
        decomposition =>
          installedSourceContradictsBeginScoped nameEq keyEq actor opening
            sourceInstalled

data AppendOccurrenceScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState, stepBefore, stepAfter :
    SystemState name key value world error} ->
  (transition : Transition stepBefore stepAfter) ->
  (leftTrace : Transitions first middle) ->
  (rightTrace : Transitions middle finalState) ->
  Type where
  AppendOccurrenceOnLeft :
    OccursIn transition leftTrace ->
    AppendOccurrenceScoped transition leftTrace rightTrace
  AppendOccurrenceOnRight :
    OccursIn transition rightTrace ->
    AppendOccurrenceScoped transition leftTrace rightTrace

0 classifyAppendOccurrenceScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState, stepBefore, stepAfter :
    SystemState name key value world error} ->
  {transition : Transition stepBefore stepAfter} ->
  (leftTrace : Transitions first middle) ->
  (rightTrace : Transitions middle finalState) ->
  OccursIn transition (appendTransitions leftTrace rightTrace) ->
  AppendOccurrenceScoped transition leftTrace rightTrace
classifyAppendOccurrenceScoped NoTransitions rightTrace occurs =
  AppendOccurrenceOnRight occurs
classifyAppendOccurrenceScoped (MoreTransitions head rest) rightTrace
  OccursHere = AppendOccurrenceOnLeft OccursHere
classifyAppendOccurrenceScoped (MoreTransitions head rest) rightTrace
  (OccursLater later) =
    case classifyAppendOccurrenceScoped rest rightTrace later of
      AppendOccurrenceOnLeft onLeft =>
        AppendOccurrenceOnLeft (OccursLater onLeft)
      AppendOccurrenceOnRight onRight => AppendOccurrenceOnRight onRight

0 beginUnloadTransitionImpossibleScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {actor : name} ->
  {beginBefore, beginAfter, closeBefore, closeAfter :
    SystemState name key value world error} ->
  (opening : BeginStep nameEq keyEq actor beginBefore beginAfter) ->
  (closing : UnloadStep nameEq keyEq actor closeBefore closeAfter) ->
  OccursIn (beginTransition opening)
    (MoreTransitions (unloadTransition closing) NoTransitions) ->
  Void
beginUnloadTransitionImpossibleScoped opening closing OccursHere impossible
beginUnloadTransitionImpossibleScoped opening closing (OccursLater later)
  impossible

0 closedEpisodeExcludesBeginScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {preStart, afterClose, beginBefore, beginAfter :
    SystemState name key value world error} ->
  (episode : ClosedEpisode name key world error value nameEq keyEq actor
    preStart afterClose) ->
  (opening : BeginStep nameEq keyEq actor beginBefore beginAfter) ->
  OccursIn (beginTransition opening) (closedTransitions episode) ->
  Void
closedEpisodeExcludesBeginScoped nameEq keyEq actor episode opening occurs =
  case classifyAppendOccurrenceScoped (closedInside episode)
    (MoreTransitions (unloadTransition (closing episode)) NoTransitions)
    occurs of
    AppendOccurrenceOnLeft insideOccurs =>
      installedTraceExcludesBeginScoped nameEq keyEq actor
        (closedInside episode) (closedInsideInstalled episode) opening
        insideOccurs
    AppendOccurrenceOnRight closingOccurs =>
      beginUnloadTransitionImpossibleScoped opening (closing episode)
        closingOccurs

0 orientTransitionHeadRightScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (leftHead, rightHead : Transition first middle) ->
  (rightTrace : Transitions middle finalState) ->
  (0 headEq : leftHead = rightHead) ->
  MoreTransitions rightHead rightTrace = MoreTransitions leftHead rightTrace
orientTransitionHeadRightScoped leftHead rightHead rightTrace headEq =
  cong (\candidate => MoreTransitions candidate rightTrace) (sym headEq)

0 commonTransitionPrefixInjectiveScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (commonHead : Transition first middle) ->
  (leftTrace, rightTrace : Transitions middle finalState) ->
  (0 sameAppend :
    MoreTransitions commonHead leftTrace =
      MoreTransitions commonHead rightTrace) ->
  leftTrace = rightTrace
commonTransitionPrefixInjectiveScoped commonHead leftTrace rightTrace
  sameAppend =
    case sameAppend of
      Refl => Refl

0 cancelTransitionHeadScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (leftHead, rightHead : Transition first middle) ->
  (leftTrace, rightTrace : Transitions middle finalState) ->
  (0 headEq : leftHead = rightHead) ->
  (0 sameAppend :
    MoreTransitions leftHead leftTrace =
      MoreTransitions rightHead rightTrace) ->
  leftTrace = rightTrace
cancelTransitionHeadScoped leftHead rightHead leftTrace rightTrace headEq
  sameAppend =
    commonTransitionPrefixInjectiveScoped leftHead leftTrace rightTrace
      (trans sameAppend
        (orientTransitionHeadRightScoped leftHead rightHead rightTrace headEq))

0 cancelTransitionPrefixScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (prefixTrace : Transitions first middle) ->
  (leftTrace, rightTrace : Transitions middle finalState) ->
  (0 sameAppend :
    appendTransitions prefixTrace leftTrace =
      appendTransitions prefixTrace rightTrace) ->
  leftTrace = rightTrace
cancelTransitionPrefixScoped NoTransitions leftTrace rightTrace sameAppend =
  sameAppend
cancelTransitionPrefixScoped (MoreTransitions commonHead prefixRest) leftTrace
  rightTrace sameAppend =
    cancelTransitionPrefixScoped prefixRest leftTrace rightTrace
      (cancelTransitionHeadScoped commonHead commonHead
        (appendTransitions prefixRest leftTrace)
        (appendTransitions prefixRest rightTrace) Refl sameAppend)

0 providerClosedDecompositionScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {provider, consumer : name} ->
  {initial, finalState : SystemState name key value world error} ->
  {global : Transitions initial finalState} ->
  (providerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    provider global) ->
  (consumerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    consumer global) ->
  (containment : ProviderContainsConsumer providerEpisode consumerEpisode) ->
  closedTransitions (locatedEpisode providerEpisode) =
    appendTransitions (strictToTransitions (providerToConsumer containment))
      (appendTransitions (closedTransitions (locatedEpisode consumerEpisode))
        (strictToTransitions (consumerToProviderClose containment)))
providerClosedDecompositionScoped providerEpisode consumerEpisode containment =
  cancelTransitionPrefixScoped (prefixThroughOpening providerEpisode)
    (closedTransitions (locatedEpisode providerEpisode))
    (appendTransitions (strictToTransitions (providerToConsumer containment))
      (appendTransitions (closedTransitions (locatedEpisode consumerEpisode))
        (strictToTransitions (consumerToProviderClose containment))))
    (trans (closingOrderInGlobal containment)
      (rewrite openingOrderInGlobal containment in
       rewrite appendTransitionsAssociative
         (prefixThroughOpening providerEpisode)
         (strictToTransitions (providerToConsumer containment))
         (closedTransitions (locatedEpisode consumerEpisode)) in
       rewrite appendTransitionsAssociative
         (prefixThroughOpening providerEpisode)
         (appendTransitions (strictToTransitions
           (providerToConsumer containment))
           (closedTransitions (locatedEpisode consumerEpisode)))
         (strictToTransitions (consumerToProviderClose containment)) in
       rewrite appendTransitionsAssociative
         (strictToTransitions (providerToConsumer containment))
         (closedTransitions (locatedEpisode consumerEpisode))
         (strictToTransitions (consumerToProviderClose containment)) in Refl))

0 containingProviderExcludesConsumerBeginScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {selected, actor : name} ->
  {prefixInitial, prefixFinal, beginBefore, beginAfter :
    SystemState name key value world error} ->
  {prefixTrace : Transitions prefixInitial prefixFinal} ->
  (providerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected prefixTrace) ->
  (consumerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    actor prefixTrace) ->
  (containment : ProviderContainsConsumer providerEpisode consumerEpisode) ->
  (opening : BeginStep nameEq keyEq selected beginBefore beginAfter) ->
  OccursIn (beginTransition opening)
    (closedTransitions (locatedEpisode consumerEpisode)) ->
  Void
containingProviderExcludesConsumerBeginScoped providerEpisode consumerEpisode
  containment opening occurs =
    closedEpisodeExcludesBeginScoped nameEq keyEq selected
      (locatedEpisode providerEpisode) opening
      (transportOccursScoped (sym (providerClosedDecompositionScoped
        providerEpisode consumerEpisode containment))
        (appendRightOccursScoped
          (strictToTransitions (providerToConsumer containment))
          (appendTransitions
            (closedTransitions (locatedEpisode consumerEpisode))
            (strictToTransitions (consumerToProviderClose containment)))
          (appendLeftOccursScoped
            (closedTransitions (locatedEpisode consumerEpisode))
            (strictToTransitions (consumerToProviderClose containment))
            occurs)))

0 missingLookupRejectsInstalledScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (state : SystemState name key value world error) ->
  (0 missing : lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor (registry state) = Nothing) ->
  installedAt @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor state = True ->
  Void
missingLookupRejectsInstalledScoped nameEq actor state missing installed =
  falseNotTrueO7
    (trans
      (sym (installedAtMissing nameEq actor state Nothing missing Refl))
      installed)

0 installedFiberScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (state : SystemState name key value world error) ->
  installedAt @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor state = True ->
  (fiber : Fiber name key value world error **
    lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} actor (registry state) = Just fiber)
installedFiberScoped nameEq actor state installed =
  case inspectErased (lookupFiber @{nameEq} actor (registry state)) of
    MkErasedInspection Nothing exact =>
      void (missingLookupRejectsInstalledScoped nameEq actor state exact
        installed)
    MkErasedInspection (Just fiber) exact => (fiber ** exact)

record ScopedCommittedOpeningEvidence
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (selected, actor : name) (wanted : key)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState)
  (consumerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    actor global) where
  constructor MkScopedCommittedOpeningEvidence
  0 openingResolutionScoped : resolvedProviderAt @{nameEq} @{keyEq} actor wanted
    selected (closedStartState (locatedEpisode consumerEpisode)) = True
  0 openingPrecedenceScoped : PrecedenceEdge nameEq selected actor
    (closedStartState (locatedEpisode consumerEpisode))

0 committedSelectionAtOpeningScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> (wanted : key) ->
  (openingState, current : SystemState name key value world error) ->
  (activationToCurrent : Transitions openingState current) ->
  (0 ownerInstalled : InstalledTrace name key world error value nameEq keyEq
    actor activationToCurrent) ->
  (openingOwner, currentSelected, currentOwner :
    Fiber name key value world error) ->
  (0 openingFound : lookupFiber @{nameEq} actor (registry openingState) =
    Just openingOwner) ->
  (0 selectedFound : lookupFiber @{nameEq} selected (registry current) =
    Just currentSelected) ->
  (0 ownerFound : lookupFiber @{nameEq} actor (registry current) =
    Just currentOwner) ->
  (0 currentWellFormed : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 ownerDeclares : Elem wanted (dependencies
    (componentDependencies (fiberComponent currentOwner)))) ->
  (0 candidateTrue : providerCandidate @{keyEq} wanted currentSelected = True) ->
  viewLookup @{keyEq} wanted
    (dependencies (componentDependencies
      (fiberComponent (committedFiber (installedOwnerSnapshot
        (installedOwnerCommittedSnapshot nameEq actor openingState openingOwner
          openingFound (installedTraceStart ownerInstalled)))))))
    (committedView (installedOwnerSnapshot
      (installedOwnerCommittedSnapshot nameEq actor openingState openingOwner
        openingFound (installedTraceStart ownerInstalled)))) = Just selected
committedSelectionAtOpeningScoped nameEq keyEq selected actor wanted openingState
  current activationToCurrent ownerInstalled openingOwner currentSelected
  currentOwner openingFound selectedFound ownerFound currentWellFormed
  ownerDeclares candidateTrue =
    committedProviderProvisionPersists nameEq keyEq actor wanted selected
      (committedSnapshotProviders
        (installedOwnerCommittedSnapshot nameEq actor openingState openingOwner
          openingFound (installedTraceStart ownerInstalled)))
      (currentCommittedProviders
        (selectedCandidateGivesCommittedSnapshot nameEq keyEq selected actor
          wanted current currentSelected currentOwner selectedFound ownerFound
          currentWellFormed
          (installedTraceEndScoped activationToCurrent ownerInstalled)
          ownerDeclares candidateTrue))
      activationToCurrent ownerInstalled
      (installedOwnerSnapshot
        (installedOwnerCommittedSnapshot nameEq actor openingState openingOwner
          openingFound (installedTraceStart ownerInstalled)))
      (currentCommittedSnapshot
        (selectedCandidateGivesCommittedSnapshot nameEq keyEq selected actor
          wanted current currentSelected currentOwner selectedFound ownerFound
          currentWellFormed
          (installedTraceEndScoped activationToCurrent ownerInstalled)
          ownerDeclares candidateTrue))
      (currentSnapshotSelects
        (selectedCandidateGivesCommittedSnapshot nameEq keyEq selected actor
          wanted current currentSelected currentOwner selectedFound ownerFound
          currentWellFormed
          (installedTraceEndScoped activationToCurrent ownerInstalled)
          ownerDeclares candidateTrue))

0 openingResolvedFromCommittedScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> (wanted : key) ->
  (openingState, current : SystemState name key value world error) ->
  (activationToCurrent : Transitions openingState current) ->
  (0 ownerInstalled : InstalledTrace name key world error value nameEq keyEq
    actor activationToCurrent) ->
  (openingOwner, currentSelected, currentOwner :
    Fiber name key value world error) ->
  (0 openingFound : lookupFiber @{nameEq} actor (registry openingState) =
    Just openingOwner) ->
  (0 selectedFound : lookupFiber @{nameEq} selected (registry current) =
    Just currentSelected) ->
  (0 ownerFound : lookupFiber @{nameEq} actor (registry current) =
    Just currentOwner) ->
  (0 currentWellFormed : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 ownerDeclares : Elem wanted (dependencies
    (componentDependencies (fiberComponent currentOwner)))) ->
  (0 candidateTrue : providerCandidate @{keyEq} wanted currentSelected = True) ->
  resolvedProviderAt @{nameEq} @{keyEq} actor wanted selected openingState = True
openingResolvedFromCommittedScoped nameEq keyEq selected actor wanted
  openingState current activationToCurrent ownerInstalled openingOwner
  currentSelected currentOwner openingFound selectedFound ownerFound
  currentWellFormed ownerDeclares candidateTrue =
    snapshotResolvesRelianceAnchor nameEq keyEq actor wanted selected
      (installedOwnerSnapshot
        (installedOwnerCommittedSnapshot nameEq actor openingState openingOwner
          openingFound (installedTraceStart ownerInstalled)))
      (committedSelectionAtOpeningScoped nameEq keyEq selected actor wanted
        openingState current activationToCurrent ownerInstalled openingOwner
        currentSelected currentOwner openingFound selectedFound ownerFound
        currentWellFormed ownerDeclares candidateTrue)

0 precedenceFromOpeningResolutionScoped :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> (wanted : key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (0 aligned : AlignedTransitions name key world error value nameEq keyEq
    global) ->
  (0 initialWellFormed : registryWellFormed @{nameEq} @{keyEq} initial = True) ->
  (consumerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    actor global) ->
  (current : SystemState name key value world error) ->
  (activationToCurrent : Transitions
    (closedStartState (locatedEpisode consumerEpisode)) current) ->
  (0 ownerInstalled : InstalledTrace name key world error value nameEq keyEq
    actor activationToCurrent) ->
  (openingOwner, currentOwner : Fiber name key value world error) ->
  (0 openingFound : lookupFiber @{nameEq} actor
    (registry (closedStartState (locatedEpisode consumerEpisode))) =
      Just openingOwner) ->
  (0 ownerFound : lookupFiber @{nameEq} actor (registry current) =
    Just currentOwner) ->
  (0 openingResolved : resolvedProviderAt @{nameEq} @{keyEq} actor wanted
    selected (closedStartState (locatedEpisode consumerEpisode)) = True) ->
  (0 ownerDeclares : Elem wanted (dependencies
    (componentDependencies (fiberComponent currentOwner)))) ->
  PrecedenceEdge nameEq selected actor
    (closedStartState (locatedEpisode consumerEpisode))
precedenceFromOpeningResolutionScoped nameEq keyEq selected actor wanted global
  aligned initialWellFormed consumerEpisode current activationToCurrent
  ownerInstalled openingOwner currentOwner openingFound ownerFound openingResolved
  ownerDeclares =
    MkPrecedenceEdge wanted
      (resolvedProviderFiber
        (resolvedProviderData nameEq keyEq actor wanted selected
          (closedStartState (locatedEpisode consumerEpisode))
          (episodeStartWellFormed nameEq keyEq actor global aligned
            initialWellFormed consumerEpisode)
          openingResolved))
      openingOwner
      (resolvedProviderLookup
        (resolvedProviderData nameEq keyEq actor wanted selected
          (closedStartState (locatedEpisode consumerEpisode))
          (episodeStartWellFormed nameEq keyEq actor global aligned
            initialWellFormed consumerEpisode)
          openingResolved))
      openingFound
      (resolvedProviderDeclaresRelianceAnchor nameEq keyEq selected wanted
        (closedStartState (locatedEpisode consumerEpisode))
        (resolvedProviderData nameEq keyEq actor wanted selected
          (closedStartState (locatedEpisode consumerEpisode))
          (episodeStartWellFormed nameEq keyEq actor global aligned
            initialWellFormed consumerEpisode)
          openingResolved))
      (replace
        {p = \component => Elem wanted
          (dependencies (componentDependencies component))}
        (installedTracePreservesComponent nameEq keyEq actor activationToCurrent
          ownerInstalled openingOwner currentOwner openingFound ownerFound)
        ownerDeclares)

0 buildScopedCommittedOpeningEvidence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> (wanted : key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (0 aligned : AlignedTransitions name key world error value nameEq keyEq
    global) ->
  (0 initialWellFormed : registryWellFormed @{nameEq} @{keyEq} initial = True) ->
  (consumerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    actor global) ->
  (current : SystemState name key value world error) ->
  (activationToCurrent : Transitions
    (closedStartState (locatedEpisode consumerEpisode)) current) ->
  (0 ownerInstalled : InstalledTrace name key world error value nameEq keyEq
    actor activationToCurrent) ->
  (openingOwner, currentSelected, currentOwner :
    Fiber name key value world error) ->
  (0 openingFound : lookupFiber @{nameEq} actor
    (registry (closedStartState (locatedEpisode consumerEpisode))) =
      Just openingOwner) ->
  (0 selectedFound : lookupFiber @{nameEq} selected (registry current) =
    Just currentSelected) ->
  (0 ownerFound : lookupFiber @{nameEq} actor (registry current) =
    Just currentOwner) ->
  (0 currentWellFormed : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 ownerDeclares : Elem wanted (dependencies
    (componentDependencies (fiberComponent currentOwner)))) ->
  (0 candidateTrue : providerCandidate @{keyEq} wanted currentSelected = True) ->
  ScopedCommittedOpeningEvidence name key world error value nameEq keyEq selected
    actor wanted global consumerEpisode
buildScopedCommittedOpeningEvidence nameEq keyEq selected actor wanted global
  aligned initialWellFormed consumerEpisode current activationToCurrent
  ownerInstalled openingOwner currentSelected currentOwner openingFound
  selectedFound ownerFound currentWellFormed ownerDeclares candidateTrue =
    MkScopedCommittedOpeningEvidence
      (openingResolvedFromCommittedScoped nameEq keyEq selected actor wanted
        (closedStartState (locatedEpisode consumerEpisode)) current
        activationToCurrent ownerInstalled openingOwner currentSelected
        currentOwner openingFound selectedFound ownerFound currentWellFormed
        ownerDeclares candidateTrue)
      (precedenceFromOpeningResolutionScoped nameEq keyEq selected actor wanted
        global aligned initialWellFormed consumerEpisode current
        activationToCurrent ownerInstalled openingOwner currentOwner openingFound
        ownerFound
        (openingResolvedFromCommittedScoped nameEq keyEq selected actor wanted
          (closedStartState (locatedEpisode consumerEpisode)) current
          activationToCurrent ownerInstalled openingOwner currentSelected
          currentOwner openingFound selectedFound ownerFound currentWellFormed
          ownerDeclares candidateTrue)
        ownerDeclares)

0 insideScopedOpeningContradiction :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  (selected, actor : name) -> (wanted : key) ->
  (selectedStartOrdinal : Nat) ->
  (selectedStartLive : GenerationEnvironment name) ->
  {initial, finalState : SystemState name key value world error} ->
  {global : Transitions initial finalState} ->
  (selectedEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  (0 selectedOrdinalExact : transitionCount
    (traceBeforeOpening selectedEpisode) = selectedStartOrdinal) ->
  (0 noDependent : NoDependentClosingEpisodeForGeneration
    {nameEq = nameEq} {keyEq = keyEq} {global = global} selected
    selectedStartOrdinal selectedStartLive selectedEpisode) ->
  {prefixFinal, stepBefore, stepAfter :
    SystemState name key value world error} ->
  {transition : Transition stepBefore stepAfter} ->
  {prefixTrace : Transitions initial prefixFinal} ->
  {anchor : ForeignLifecycleInstalledAnchor name key world error value nameEq
    keyEq actor transition prefixTrace} ->
  (localization : ScopedClosingLocalization name key world error value nameEq
    keyEq actor transition prefixTrace global anchor) ->
  (selectedToAnchor : Transitions
    (closedStartState (locatedEpisode selectedEpisode))
    (lifecycleInstalledState anchor)) ->
  (selectedAfterAnchor : Transitions (lifecycleInstalledState anchor)
    (lastInstalledState (locatedEpisode selectedEpisode))) ->
  (0 selectedWholeExact : appendTransitions selectedToAnchor
    selectedAfterAnchor = closedInside (locatedEpisode selectedEpisode)) ->
  (selectedToForeign : Transitions
    (closedStartState (locatedEpisode selectedEpisode))
    (locatedPreStart (localizedPrefixEpisode localization))) ->
  (0 selectedInsideExact : selectedToAnchor =
    appendTransitions selectedToForeign
      (MoreTransitions
        (beginTransition (closedOpening
          (locatedEpisode (localizedPrefixEpisode localization))))
        (localizedActivationToAnchor localization))) ->
  (0 foreignPrefixCountExact : transitionCount
    (traceBeforeOpening (localizedPrefixEpisode localization)) =
      transitionCount (traceBeforeOpening selectedEpisode) +
        S (transitionCount selectedToForeign)) ->
  (evidence : ScopedCommittedOpeningEvidence name key world error value nameEq
    keyEq selected actor wanted global (localizedGlobalEpisode localization)) ->
  Void
insideScopedOpeningContradiction selected actor wanted selectedStartOrdinal
  selectedStartLive selectedEpisode selectedOrdinalExact noDependent localization
  selectedToAnchor selectedAfterAnchor selectedWholeExact selectedToForeign
  selectedInsideExact foreignPrefixCountExact evidence =
    noDependent actor (localizedGlobalEpisode localization)
      (MkGenerationScopedClosingStart selectedOrdinalExact
        (MkLocatedActionOccurrence
          (locatedPreStart (localizedPrefixEpisode localization))
          (closedStartState
            (locatedEpisode (localizedPrefixEpisode localization)))
          selectedToForeign
          (beginTransition (closedOpening
            (locatedEpisode (localizedPrefixEpisode localization))))
          (appendTransitions (localizedActivationToAnchor localization)
            selectedAfterAnchor)
          Refl
          (trans
            (sym (appendTransitionsAssociative selectedToForeign
              (MoreTransitions
                (beginTransition (closedOpening
                  (locatedEpisode (localizedPrefixEpisode localization))))
                (localizedActivationToAnchor localization))
              selectedAfterAnchor))
            (trans
              (cong (\candidate => appendTransitions candidate
                selectedAfterAnchor) (sym selectedInsideExact))
              selectedWholeExact)))
        (trans (localizedOpeningCountExact localization)
          (selectedGenerationConsumerOrdinalScoped
            (traceBeforeOpening selectedEpisode) selectedToForeign
            (traceBeforeOpening (localizedPrefixEpisode localization))
            selectedStartOrdinal selectedOrdinalExact foreignPrefixCountExact)))
      (openingPrecedenceScoped evidence)

0 beforeScopedSelectedBeginOccurs :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {selected, actor : name} ->
  {initial, finalState, prefixFinal, stepBefore, stepAfter :
    SystemState name key value world error} ->
  {global : Transitions initial finalState} ->
  (selectedEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  {transition : Transition stepBefore stepAfter} ->
  {prefixTrace : Transitions initial prefixFinal} ->
  {anchor : ForeignLifecycleInstalledAnchor name key world error value nameEq
    keyEq actor transition prefixTrace} ->
  (localization : ScopedClosingLocalization name key world error value nameEq
    keyEq actor transition prefixTrace global anchor) ->
  (selectedToAnchor : Transitions
    (closedStartState (locatedEpisode selectedEpisode))
    (lifecycleInstalledState anchor)) ->
  (foreignToSelected : Transitions
    (closedStartState
      (locatedEpisode (localizedPrefixEpisode localization)))
    (locatedPreStart selectedEpisode)) ->
  (0 foreignSuffixExact : localizedActivationToAnchor localization =
    appendTransitions foreignToSelected
      (MoreTransitions
        (beginTransition (closedOpening (locatedEpisode selectedEpisode)))
        selectedToAnchor)) ->
  OccursIn
    (beginTransition (closedOpening (locatedEpisode selectedEpisode)))
    (closedTransitions
      (locatedEpisode (localizedPrefixEpisode localization)))
beforeScopedSelectedBeginOccurs selectedEpisode localization selectedToAnchor
  foreignToSelected foreignSuffixExact =
    appendLeftOccursScoped
      (closedInside (locatedEpisode (localizedPrefixEpisode localization)))
      (MoreTransitions
        (unloadTransition
          (closing (locatedEpisode (localizedPrefixEpisode localization))))
        NoTransitions)
      (transportOccursScoped (localizedInsideSplit localization)
        (appendLeftOccursScoped (localizedActivationToAnchor localization)
          (localizedAnchorToClosing localization)
          (transportOccursScoped (sym foreignSuffixExact)
            (appendRightOccursScoped foreignToSelected
              (MoreTransitions
                (beginTransition
                  (closedOpening (locatedEpisode selectedEpisode)))
                selectedToAnchor)
              OccursHere))))

0 beforeScopedOpeningContradiction :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> (0 actorDistinct : Not (actor = selected)) ->
  (wanted : key) ->
  {initial, finalState, prefixFinal, stepBefore, stepAfter :
    SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (0 initialWellFormed : registryWellFormed @{nameEq} @{keyEq} initial = True) ->
  (0 initialEmpty : bindings (registry initial) = []) ->
  (selectedEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  {transition : Transition stepBefore stepAfter} ->
  (prefixTrace : Transitions initial prefixFinal) ->
  (0 prefixAligned : AlignedTransitions name key world error value nameEq keyEq
    prefixTrace) ->
  (0 selectedFinalFalse : installedAt @{nameEq} selected prefixFinal = False) ->
  {anchor : ForeignLifecycleInstalledAnchor name key world error value nameEq
    keyEq actor transition prefixTrace} ->
  (localization : ScopedClosingLocalization name key world error value nameEq
    keyEq actor transition prefixTrace global anchor) ->
  (selectedToAnchor : Transitions
    (closedStartState (locatedEpisode selectedEpisode))
    (lifecycleInstalledState anchor)) ->
  (foreignToSelected : Transitions
    (closedStartState
      (locatedEpisode (localizedPrefixEpisode localization)))
    (locatedPreStart selectedEpisode)) ->
  (0 foreignSuffixExact : localizedActivationToAnchor localization =
    appendTransitions foreignToSelected
      (MoreTransitions
        (beginTransition (closedOpening (locatedEpisode selectedEpisode)))
        selectedToAnchor)) ->
  (evidence : ScopedCommittedOpeningEvidence name key world error value nameEq
    keyEq selected actor wanted global (localizedGlobalEpisode localization)) ->
  Void
beforeScopedOpeningContradiction nameEq keyEq selected actor actorDistinct wanted
  global initialWellFormed initialEmpty selectedEpisode prefixTrace prefixAligned
  selectedFinalFalse localization selectedToAnchor foreignToSelected
  foreignSuffixExact evidence =
    case orderingTheoremProof nameEq keyEq initial prefixFinal prefixTrace
      prefixAligned initialWellFormed initialEmpty actor selected actorDistinct
      wanted selectedFinalFalse (localizedPrefixEpisode localization)
      (replace
        {p = \state => resolvedProviderAt @{nameEq} @{keyEq} actor wanted
          selected state = True}
        (localizedOpeningStateExact localization)
        (openingResolutionScoped evidence)) of
      (providerEpisode ** ordering) =>
        containingProviderExcludesConsumerBeginScoped providerEpisode
          (localizedPrefixEpisode localization)
          (containment ordering)
          (closedOpening (locatedEpisode selectedEpisode))
          (beforeScopedSelectedBeginOccurs selectedEpisode localization
            selectedToAnchor foreignToSelected foreignSuffixExact)

0 generationScopedCandidateTrueFromOpening :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> (0 actorDistinct : Not (actor = selected)) ->
  (wanted : key) ->
  {initial, finalState, prefixFinal, stepBefore, stepAfter :
    SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (0 aligned : AlignedTransitions name key world error value nameEq keyEq
    global) ->
  (0 initialWellFormed : registryWellFormed @{nameEq} @{keyEq} initial = True) ->
  (0 initialEmpty : bindings (registry initial) = []) ->
  (selectedStartOrdinal : Nat) ->
  (selectedStartLive : GenerationEnvironment name) ->
  (selectedEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  (0 selectedOrdinalExact : transitionCount
    (traceBeforeOpening selectedEpisode) = selectedStartOrdinal) ->
  (0 noDependent : NoDependentClosingEpisodeForGeneration
    {nameEq = nameEq} {keyEq = keyEq} {global = global} selected
    selectedStartOrdinal selectedStartLive selectedEpisode) ->
  {transition : Transition stepBefore stepAfter} ->
  (prefixTrace : Transitions initial prefixFinal) ->
  (0 prefixAligned : AlignedTransitions name key world error value nameEq keyEq
    prefixTrace) ->
  (0 selectedFinalFalse : installedAt @{nameEq} selected prefixFinal = False) ->
  {anchor : ForeignLifecycleInstalledAnchor name key world error value nameEq
    keyEq actor transition prefixTrace} ->
  (localization : ScopedClosingLocalization name key world error value nameEq
    keyEq actor transition prefixTrace global anchor) ->
  (selectedToAnchor : Transitions
    (closedStartState (locatedEpisode selectedEpisode))
    (lifecycleInstalledState anchor)) ->
  (selectedAfterAnchor : Transitions (lifecycleInstalledState anchor)
    (lastInstalledState (locatedEpisode selectedEpisode))) ->
  (0 selectedWholeExact : appendTransitions selectedToAnchor
    selectedAfterAnchor = closedInside (locatedEpisode selectedEpisode)) ->
  (0 selectedAnchorExact : appendTransitions
    (traceBeforeOpening selectedEpisode)
    (MoreTransitions
      (beginTransition (closedOpening (locatedEpisode selectedEpisode)))
      selectedToAnchor) = lifecycleBeforeInstalled anchor) ->
  (current : SystemState name key value world error) ->
  (activationToCurrent : Transitions
    (closedStartState
      (locatedEpisode (localizedGlobalEpisode localization))) current) ->
  (0 ownerInstalled : InstalledTrace name key world error value nameEq keyEq
    actor activationToCurrent) ->
  (openingOwner, currentSelected, currentOwner :
    Fiber name key value world error) ->
  (0 openingFound : lookupFiber @{nameEq} actor
    (registry (closedStartState
      (locatedEpisode (localizedGlobalEpisode localization)))) =
      Just openingOwner) ->
  (0 selectedFound : lookupFiber @{nameEq} selected (registry current) =
    Just currentSelected) ->
  (0 ownerFound : lookupFiber @{nameEq} actor (registry current) =
    Just currentOwner) ->
  (0 currentWellFormed : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 ownerDeclares : Elem wanted (dependencies
    (componentDependencies (fiberComponent currentOwner)))) ->
  (0 candidateTrue : providerCandidate @{keyEq} wanted currentSelected = True) ->
  Void
generationScopedCandidateTrueFromOpening nameEq keyEq selected actor
  actorDistinct wanted global aligned initialWellFormed initialEmpty
  selectedStartOrdinal selectedStartLive selectedEpisode selectedOrdinalExact
  noDependent prefixTrace prefixAligned selectedFinalFalse localization
  selectedToAnchor selectedAfterAnchor selectedWholeExact selectedAnchorExact
  current activationToCurrent ownerInstalled openingOwner currentSelected
  currentOwner openingFound selectedFound ownerFound currentWellFormed
  ownerDeclares candidateTrue =
    case erasedFirstLifecyclePreIntervalCovering name key world error value
      nameEq keyEq selected actor actorDistinct initial
      (locatedPreStart selectedEpisode)
      (closedStartState (locatedEpisode selectedEpisode))
      (locatedPreStart (localizedPrefixEpisode localization))
      (closedStartState
        (locatedEpisode (localizedPrefixEpisode localization)))
      (lifecycleInstalledState anchor)
      (traceBeforeOpening selectedEpisode)
      (closedOpening (locatedEpisode selectedEpisode)) selectedToAnchor
      (traceBeforeOpening (localizedPrefixEpisode localization))
      (closedOpening (locatedEpisode (localizedPrefixEpisode localization)))
      (localizedActivationToAnchor localization)
      (localizedActivationInstalled localization)
      (trans selectedAnchorExact (sym (localizedOpeningSplit localization))) of
      ForeignOpeningInsideSelectedInterval selectedToForeign
        selectedInsideExact foreignPrefixCountExact foreignInstalled =>
          insideScopedOpeningContradiction selected actor wanted
            selectedStartOrdinal selectedStartLive selectedEpisode
            selectedOrdinalExact noDependent localization selectedToAnchor
            selectedAfterAnchor selectedWholeExact selectedToForeign
            selectedInsideExact foreignPrefixCountExact
            (buildScopedCommittedOpeningEvidence nameEq keyEq selected actor
              wanted global aligned initialWellFormed
              (localizedGlobalEpisode localization) current activationToCurrent
              ownerInstalled openingOwner currentSelected currentOwner
              openingFound selectedFound ownerFound currentWellFormed
              ownerDeclares candidateTrue)
      ForeignOpeningBeforeSelectedInterval foreignToSelected foreignSuffixExact
        foreignInstalled =>
          beforeScopedOpeningContradiction nameEq keyEq selected actor
            actorDistinct wanted global initialWellFormed initialEmpty
            selectedEpisode prefixTrace prefixAligned selectedFinalFalse
            localization selectedToAnchor foreignToSelected foreignSuffixExact
            (buildScopedCommittedOpeningEvidence nameEq keyEq selected actor
              wanted global aligned initialWellFormed
              (localizedGlobalEpisode localization) current activationToCurrent
              ownerInstalled openingOwner currentSelected currentOwner
              openingFound selectedFound ownerFound currentWellFormed
              ownerDeclares candidateTrue)

0 generationScopedCandidateTrueImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> (0 actorDistinct : Not (actor = selected)) ->
  (wanted : key) ->
  {initial, finalState, prefixFinal, stepBefore, stepAfter :
    SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (0 aligned : AlignedTransitions name key world error value nameEq keyEq
    global) ->
  (0 initialWellFormed : registryWellFormed @{nameEq} @{keyEq} initial = True) ->
  (0 initialEmpty : bindings (registry initial) = []) ->
  (selectedStartOrdinal : Nat) ->
  (selectedStartLive : GenerationEnvironment name) ->
  (selectedEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  (0 selectedOrdinalExact : transitionCount
    (traceBeforeOpening selectedEpisode) = selectedStartOrdinal) ->
  (0 noDependent : NoDependentClosingEpisodeForGeneration
    {nameEq = nameEq} {keyEq = keyEq} {global = global} selected
    selectedStartOrdinal selectedStartLive selectedEpisode) ->
  {transition : Transition stepBefore stepAfter} ->
  (prefixTrace : Transitions initial prefixFinal) ->
  (0 prefixAligned : AlignedTransitions name key world error value nameEq keyEq
    prefixTrace) ->
  (0 selectedFinalFalse : installedAt @{nameEq} selected prefixFinal = False) ->
  {anchor : ForeignLifecycleInstalledAnchor name key world error value nameEq
    keyEq actor transition prefixTrace} ->
  (localization : ScopedClosingLocalization name key world error value nameEq
    keyEq actor transition prefixTrace global anchor) ->
  (selectedToAnchor : Transitions
    (closedStartState (locatedEpisode selectedEpisode))
    (lifecycleInstalledState anchor)) ->
  (selectedAfterAnchor : Transitions (lifecycleInstalledState anchor)
    (lastInstalledState (locatedEpisode selectedEpisode))) ->
  (0 selectedWholeExact : appendTransitions selectedToAnchor
    selectedAfterAnchor = closedInside (locatedEpisode selectedEpisode)) ->
  (0 selectedAnchorExact : appendTransitions
    (traceBeforeOpening selectedEpisode)
    (MoreTransitions
      (beginTransition (closedOpening (locatedEpisode selectedEpisode)))
      selectedToAnchor) = lifecycleBeforeInstalled anchor) ->
  (current : SystemState name key value world error) ->
  (activationToCurrent : Transitions
    (closedStartState
      (locatedEpisode (localizedGlobalEpisode localization))) current) ->
  (0 ownerInstalled : InstalledTrace name key world error value nameEq keyEq
    actor activationToCurrent) ->
  (currentSelected, currentOwner : Fiber name key value world error) ->
  (0 selectedFound : lookupFiber @{nameEq} selected (registry current) =
    Just currentSelected) ->
  (0 ownerFound : lookupFiber @{nameEq} actor (registry current) =
    Just currentOwner) ->
  (0 currentWellFormed : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 ownerDeclares : Elem wanted (dependencies
    (componentDependencies (fiberComponent currentOwner)))) ->
  (0 candidateTrue : providerCandidate @{keyEq} wanted currentSelected = True) ->
  Void
generationScopedCandidateTrueImpossible nameEq keyEq selected actor
  actorDistinct wanted global aligned initialWellFormed initialEmpty
  selectedStartOrdinal selectedStartLive selectedEpisode selectedOrdinalExact
  noDependent prefixTrace prefixAligned selectedFinalFalse localization
  selectedToAnchor selectedAfterAnchor selectedWholeExact selectedAnchorExact
  current activationToCurrent ownerInstalled currentSelected currentOwner
  selectedFound ownerFound currentWellFormed ownerDeclares candidateTrue =
    case installedFiberScoped nameEq actor
      (closedStartState
        (locatedEpisode (localizedGlobalEpisode localization)))
      (installedTraceStart ownerInstalled) of
      (openingOwner ** openingFound) =>
        generationScopedCandidateTrueFromOpening nameEq keyEq selected actor
          actorDistinct wanted global aligned initialWellFormed initialEmpty
          selectedStartOrdinal selectedStartLive selectedEpisode
          selectedOrdinalExact noDependent prefixTrace prefixAligned
          selectedFinalFalse localization selectedToAnchor selectedAfterAnchor
          selectedWholeExact selectedAnchorExact current activationToCurrent
          ownerInstalled openingOwner currentSelected currentOwner openingFound
          selectedFound ownerFound currentWellFormed ownerDeclares candidateTrue

0 generationScopedCrossingExcludesSelected :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> (0 actorDistinct : Not (actor = selected)) ->
  {initial, finalState, prefixFinal, stepBefore, stepAfter :
    SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (0 aligned : AlignedTransitions name key world error value nameEq keyEq
    global) ->
  (0 initialWellFormed : registryWellFormed @{nameEq} @{keyEq} initial = True) ->
  (0 initialEmpty : bindings (registry initial) = []) ->
  (selectedStartOrdinal : Nat) ->
  (selectedStartLive : GenerationEnvironment name) ->
  (selectedEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  (0 selectedOrdinalExact : transitionCount
    (traceBeforeOpening selectedEpisode) = selectedStartOrdinal) ->
  (0 noDependent : NoDependentClosingEpisodeForGeneration
    {nameEq = nameEq} {keyEq = keyEq} {global = global} selected
    selectedStartOrdinal selectedStartLive selectedEpisode) ->
  {transition : Transition stepBefore stepAfter} ->
  (prefixTrace : Transitions initial prefixFinal) ->
  (0 prefixAligned : AlignedTransitions name key world error value nameEq keyEq
    prefixTrace) ->
  (0 selectedFinalFalse : installedAt @{nameEq} selected prefixFinal = False) ->
  {anchor : ForeignLifecycleInstalledAnchor name key world error value nameEq
    keyEq actor transition prefixTrace} ->
  (localization : ScopedClosingLocalization name key world error value nameEq
    keyEq actor transition prefixTrace global anchor) ->
  (selectedToAnchor : Transitions
    (closedStartState (locatedEpisode selectedEpisode))
    (lifecycleInstalledState anchor)) ->
  (selectedAfterAnchor : Transitions (lifecycleInstalledState anchor)
    (lastInstalledState (locatedEpisode selectedEpisode))) ->
  (0 selectedWholeExact : appendTransitions selectedToAnchor
    selectedAfterAnchor = closedInside (locatedEpisode selectedEpisode)) ->
  (0 selectedAnchorExact : appendTransitions
    (traceBeforeOpening selectedEpisode)
    (MoreTransitions
      (beginTransition (closedOpening (locatedEpisode selectedEpisode)))
      selectedToAnchor) = lifecycleBeforeInstalled anchor) ->
  (current : SystemState name key value world error) ->
  (activationToCurrent : Transitions
    (closedStartState
      (locatedEpisode (localizedGlobalEpisode localization))) current) ->
  (0 ownerInstalled : InstalledTrace name key world error value nameEq keyEq
    actor activationToCurrent) ->
  (currentSelected, currentOwner : Fiber name key value world error) ->
  (0 selectedFound : lookupFiber @{nameEq} selected (registry current) =
    Just currentSelected) ->
  (0 ownerFound : lookupFiber @{nameEq} actor (registry current) =
    Just currentOwner) ->
  (0 currentWellFormed : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (wanted : key) ->
  (0 ownerDeclares : Elem wanted (dependencies
    (componentDependencies (fiberComponent currentOwner)))) ->
  providerCandidate @{keyEq} wanted currentSelected = False
generationScopedCrossingExcludesSelected nameEq keyEq selected actor
  actorDistinct global aligned initialWellFormed initialEmpty
  selectedStartOrdinal selectedStartLive selectedEpisode selectedOrdinalExact
  noDependent prefixTrace prefixAligned selectedFinalFalse localization
  selectedToAnchor selectedAfterAnchor selectedWholeExact selectedAnchorExact
  current activationToCurrent ownerInstalled currentSelected currentOwner
  selectedFound ownerFound currentWellFormed wanted ownerDeclares =
    case inspectErased (providerCandidate @{keyEq} wanted currentSelected) of
      MkErasedInspection False exact => exact
      MkErasedInspection True exact =>
        void (generationScopedCandidateTrueImpossible nameEq keyEq selected actor
          actorDistinct wanted global aligned initialWellFormed initialEmpty
          selectedStartOrdinal selectedStartLive selectedEpisode
          selectedOrdinalExact noDependent prefixTrace prefixAligned
          selectedFinalFalse localization selectedToAnchor selectedAfterAnchor
          selectedWholeExact selectedAnchorExact current activationToCurrent
          ownerInstalled currentSelected currentOwner selectedFound ownerFound
          currentWellFormed ownerDeclares exact)

||| Research-side generalized seam for the selected-episode fold.  Unlike the
||| frozen production anchor provider, this callback exposes every
||| occurrence-local lifecycle fact before asking for the selected-provider
||| exclusion.  The returned Boolean observation is therefore generation
||| scoped and never requires a raw-name-global dependency predicate.
public export
record ScopedSelectedEpisodeLifecycleProvider
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (registered : List (RegistrationGeneration name))
  {globalFirst, globalLast, selectedPre, selectedAfter :
    SystemState name key value world error}
  (global : Transitions globalFirst globalLast)
  (selectedEpisode : ClosedEpisode name key world error value nameEq keyEq
    selected selectedPre selectedAfter) where
  constructor MkScopedSelectedEpisodeLifecycleProvider
  0 scopedLifecycleExcludesSelectedAt :
    (ordinal : Nat) -> (live : GenerationEnvironment name) ->
    (action : Action name key value world error) ->
    (lifecycle : isLifecycleAction action = True) ->
    (distinct : Not (actionOwner action = selected)) ->
    (before, afterState : SystemState name key value world error) ->
    (tag : RuleTag) ->
    (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
      Just (tag, afterState)) ->
    (rest : Transitions afterState (lastInstalledState selectedEpisode)) ->
    InstalledTrace name key world error value nameEq keyEq selected rest ->
    (occurs : OccursIn
      (Fired {before = before} {afterState = afterState}
        nameEq keyEq action tag checked) global) ->
    (insidePrefix : Transitions (closedStartState selectedEpisode) before) ->
    appendTransitions insidePrefix
      (MoreTransitions (Fired nameEq keyEq action tag checked) rest) =
        closedInside selectedEpisode ->
    {wholeFirst, wholeLast : SystemState name key value world error} ->
    {whole : Transitions wholeFirst wholeLast} ->
    {survivor : SystemState name key value world error} ->
    (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
      keyEq selected registered ordinal live whole before survivor) ->
    (leftSelected, leftOwner, rightOwner : Fiber name key value world error) ->
    lookupFiber @{nameEq} selected
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))) =
      Just leftSelected ->
    lookupFiber @{nameEq} (actionOwner action)
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))) =
      Just leftOwner ->
    lookupFiber @{nameEq} selected (registry before) = Just leftSelected ->
    lookupFiber @{nameEq} (actionOwner action) (registry before) =
      Just leftOwner ->
    lookupFiber @{nameEq} (actionOwner action) (registry survivor) =
      Just rightOwner ->
    FiberControlRelated leftOwner rightOwner ->
    (wanted : key) ->
    Elem wanted (dependencies
      (componentDependencies (fiberComponent leftOwner))) ->
    providerCandidate @{keyEq} wanted leftSelected = False

||| Scoped-exclusion consumption point.  This is the clause-for-clause analog
||| of the production provider-evidence dispatcher after its raw dependency
||| predicate has been eliminated: source saturation consumes only the direct
||| occurrence-local Boolean exclusion.
0 scopedForeignLifecycleControlsFromExclusion :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (action : Action name key value world error) ->
  Not (actionOwner action = selected) ->
  isLifecycleAction action = True ->
  (planAmbient, survivorAmbient : world) ->
  (plan, survivor : Registry name key value world error) ->
  (leftOwner, rightOwner, leftSelected : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected plan = Just leftSelected ->
  lookupFiber @{nameEq} (actionOwner action) plan = Just leftOwner ->
  lookupFiber @{nameEq} (actionOwner action) survivor = Just rightOwner ->
  ((wanted : key) -> Elem wanted (dependencies
    (componentDependencies (fiberComponent leftOwner))) ->
    providerCandidate @{keyEq} wanted leftSelected = False) ->
  SelectedSurvivorCleanInactive name key world error value nameEq selected
    (MkSystemState survivorAmbient survivor) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (bindings plan) (bindings survivor) ->
  ((current : name) -> Not (current = selected) ->
    {leftFiber, rightFiber : Fiber name key value world error} ->
    Elem (Bind current leftFiber) (bindings plan) ->
    Elem (Bind current rightFiber) (bindings survivor) ->
    FiberControlRelated leftFiber rightFiber ->
    bindings (ownedValues (fiberTable leftFiber)) =
      bindings (ownedValues (fiberTable rightFiber))) ->
  (tag : RuleTag) -> (planAfter : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} action (MkSystemState planAmbient plan) =
    Just (tag, planAfter) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkSystemState survivorAmbient survivor) = True ->
  ForeignAdvanceOutcomeProvider name key world error value nameEq keyEq action
    planAmbient survivorAmbient plan survivor ->
  ForeignLifecycleControlReplay name key world error value nameEq keyEq selected
    action tag planAfter (MkSystemState survivorAmbient survivor)
scopedForeignLifecycleControlsFromExclusion nameEq keyEq selected action
  actorDistinct lifecycle planAmbient survivorAmbient plan survivor leftOwner
  rightOwner leftSelected selectedFound leftFound rightFound selectedExcluded
  cleanInactive ordered foreignTables tag planAfter planRaw survivorWellFormed
  outcomes =
    replayForeignLifecycleControlsFromFrame nameEq keyEq selected action
      actorDistinct lifecycle planAmbient survivorAmbient plan survivor leftOwner
      rightOwner leftFound rightFound
      (foreignLifecycleGuardFrameFromProviderExclusion nameEq keyEq selected
        (actionOwner action) actorDistinct leftOwner rightOwner leftSelected plan
        survivor selectedFound leftFound rightFound cleanInactive ordered
        foreignTables selectedExcluded)
      tag planAfter planRaw survivorWellFormed outcomes

0 scopedSystemStateEta :
  (state : SystemState name key value world error) ->
  MkSystemState (worldState state) (registry state) = state
scopedSystemStateEta (MkSystemState ambient fibers) = Refl

0 scopedLifecycleControlTransportBefore :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {selected : name} ->
  {action : Action name key value world error} -> {tag : RuleTag} ->
  {planAfter, leftBefore, rightBefore :
    SystemState name key value world error} ->
  leftBefore = rightBefore ->
  ForeignLifecycleControlReplay name key world error value nameEq keyEq selected
    action tag planAfter leftBefore ->
  ForeignLifecycleControlReplay name key world error value nameEq keyEq selected
    action tag planAfter rightBefore
scopedLifecycleControlTransportBefore Refl replay = replay

0 scopedSelectedLifecycleOutcomes :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) ->
  (actorDistinct : Not (actionOwner action = selected)) ->
  {wholeFirst, wholeLast, before, afterState, survivor :
    SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (independent : TraceIndependent name key world error value keyEq whole) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) whole) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  (emptyPlan : EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary)))) ->
  (ownerLookup : lookupFiber @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} (actionOwner action)
    (planTarget (completePlanResult (selectedBoundaryPlan boundary))) =
    lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} (actionOwner action) (registry before)) ->
  ForeignAdvanceOutcomeProvider name key world error value nameEq keyEq action
    (worldState before) (worldState survivor)
    (planTarget (completePlanResult (selectedBoundaryPlan boundary)))
    (registry survivor)
scopedSelectedLifecycleOutcomes nameEq keyEq selected registered ordinal live
  (OInsert actor parent component) actorDistinct whole independent tag checked
  occurs boundary emptyPlan ownerLookup = ()
scopedSelectedLifecycleOutcomes nameEq keyEq selected registered ordinal live
  (ORetire actor) actorDistinct whole independent tag checked occurs boundary
  emptyPlan ownerLookup = ()
scopedSelectedLifecycleOutcomes nameEq keyEq selected registered ordinal live
  (ORemove actor) actorDistinct whole independent tag checked occurs boundary
  emptyPlan ownerLookup = ()
scopedSelectedLifecycleOutcomes nameEq keyEq selected registered ordinal live
  (LBegin actor) actorDistinct whole independent tag checked occurs boundary
  emptyPlan ownerLookup = ()
scopedSelectedLifecycleOutcomes nameEq keyEq selected registered ordinal live
  (LAdvance actor) actorDistinct whole independent tag checked occurs boundary
  emptyPlan ownerLookup =
    selectedForeignAdvanceOutcomeProvider nameEq keyEq selected actor
      actorDistinct whole independent before afterState survivor tag checked
      occurs boundary emptyPlan
      (\fiber, planFound => trans (sym ownerLookup) planFound)
scopedSelectedLifecycleOutcomes nameEq keyEq selected registered ordinal live
  (LDivert actor) actorDistinct whole independent tag checked occurs boundary
  emptyPlan ownerLookup = ()
scopedSelectedLifecycleOutcomes nameEq keyEq selected registered ordinal live
  (LLeave actor) actorDistinct whole independent tag checked occurs boundary
  emptyPlan ownerLookup = ()
scopedSelectedLifecycleOutcomes nameEq keyEq selected registered ordinal live
  (LUnload actor) actorDistinct whole independent tag checked occurs boundary
  emptyPlan ownerLookup = ()

data ScopedLocatedRegistrationStep :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) ->
  {stepBefore, stepAfter, globalFirst, globalLast :
    SystemState name key value world error} ->
  (transition : Transition stepBefore stepAfter) ->
  (global : Transitions globalFirst globalLast) -> Type where
  MkScopedLocatedRegistrationStep :
    {protocol : RegistrationProtocol key value world error} ->
    {nameEq : DecEq name} ->
    {stepBefore, stepAfter, globalFirst, globalLast :
      SystemState name key value world error} ->
    {transition : Transition stepBefore stepAfter} ->
    {global : Transitions globalFirst globalLast} ->
    (future : Transitions stepAfter globalLast) ->
    RegistrationStepDiscipline protocol nameEq (transitionAction transition)
      stepBefore future ->
    ScopedLocatedRegistrationStep protocol nameEq transition global

0 scopedRegistrationDisciplineAtOccurrence :
  (transition : Transition stepBefore stepAfter) ->
  (global : Transitions globalFirst globalLast) ->
  RegistrationDiscipline protocol nameEq global ->
  OccursIn transition global ->
  ScopedLocatedRegistrationStep protocol nameEq transition global
scopedRegistrationDisciplineAtOccurrence transition
  (MoreTransitions transition rest)
  (RegistrationDisciplineStep transition rest stepDiscipline tailDiscipline)
  OccursHere = MkScopedLocatedRegistrationStep rest stepDiscipline
scopedRegistrationDisciplineAtOccurrence wanted
  (MoreTransitions head rest)
  (RegistrationDisciplineStep head rest stepDiscipline tailDiscipline)
  (OccursLater later) =
    case scopedRegistrationDisciplineAtOccurrence wanted rest tailDiscipline
      later of
      MkScopedLocatedRegistrationStep future futureDiscipline =>
        MkScopedLocatedRegistrationStep future futureDiscipline

0 scopedSelectedPlanExactBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  GenerationEnvironmentNamesUnique live ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole original survivor) ->
  NoEpisodeReplayBoundary name key world error value nameEq keyEq registered live
    original
    (MkSystemState (worldState original)
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))))
scopedSelectedPlanExactBoundary nameEq keyEq unique boundary =
  case original of
    MkSystemState ambient source =>
      MkNoEpisodeReplayBoundary ambient source Refl
        (selectedBoundaryPlan boundary) Refl Refl unique
        (selectedOriginalWellFormed boundary)
        (inactivePlanPreservesWellFormed nameEq keyEq ambient source
          (planTarget (completePlanResult (selectedBoundaryPlan boundary)))
          (inactiveLeafPlan (completePlanResult
            (selectedBoundaryPlan boundary)))
          (selectedOriginalWellFormed boundary))

0 scopedRetainedNoEpisodeBoundaryStep :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (global : Transitions globalFirst globalLast) ->
  (globalDiscipline : RegistrationDiscipline protocol nameEq global) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (wholeInGlobal : OccurrenceEmbedding whole global) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (unique : GenerationEnvironmentNamesUnique live) ->
  (action : Action name key value world error) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) whole) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  Not (GenerationOwnedActor nameEq registered ordinal live action) ->
  RetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
    registered (advanceGenerationEnvironment @{nameEq} ordinal action live)
    action tag afterState
    (MkSystemState (worldState before)
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))))
scopedRetainedNoEpisodeBoundaryStep protocol nameEq keyEq selected registered
  global globalDiscipline whole wholeInGlobal ordinal live unique action before
  afterState survivor tag checked occurs boundary notOwned =
    case scopedRegistrationDisciplineAtOccurrence
      (Fired nameEq keyEq action tag checked) global globalDiscipline
      (wholeInGlobal (Fired nameEq keyEq action tag checked) occurs) of
      MkScopedLocatedRegistrationStep future futureDiscipline =>
        retainedSuffixHeadPreservesNoEpisodeBoundary protocol nameEq keyEq
          registered ordinal live action before
          (MkSystemState (worldState before)
            (planTarget (completePlanResult
              (selectedBoundaryPlan boundary))))
          (scopedSelectedPlanExactBoundary nameEq keyEq unique boundary) tag
          checked future futureDiscipline notOwned

0 scopedForeignRetainedHead :
  ForeignRetainedEpisodeStep name key world error value nameEq keyEq selected
    registered ordinal live whole action afterState survivor ->
  SelectedEpisodeRetainedHead name key world error value nameEq keyEq selected
    registered ordinal live whole action afterState survivor
scopedForeignRetainedHead
  (MkForeignRetainedEpisodeStep named fired nextBoundary) =
    MkSelectedEpisodeRetainedHead named fired nextBoundary

0 scopedSelectedSourceOutsidePlan :
  (nameEq : DecEq name) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentStamped live ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole original survivor) ->
  ActorOutsideDeletionPlan selected
    (inactiveLeafPlan (completePlanResult (selectedBoundaryPlan boundary)))
scopedSelectedSourceOutsidePlan nameEq selected registered live stamped outside
  boundary = selectedOutsideBoundaryPlan selected registered live stamped outside
    (selectedBoundaryPlan boundary)

0 scopedLifecycleNonInsert :
  (action : Action name key value world error) ->
  isLifecycleAction action = True -> NonInsertAction action
scopedLifecycleNonInsert (OInsert actor parent component) Refl impossible
scopedLifecycleNonInsert (ORetire actor) Refl impossible
scopedLifecycleNonInsert (ORemove actor) Refl impossible
scopedLifecycleNonInsert (LBegin actor) lifecycle = NonInsertBegin
scopedLifecycleNonInsert (LAdvance actor) lifecycle = NonInsertAdvance
scopedLifecycleNonInsert (LDivert actor) lifecycle = NonInsertDivert
scopedLifecycleNonInsert (LLeave actor) lifecycle = NonInsertLeave
scopedLifecycleNonInsert (LUnload actor) lifecycle = NonInsertUnload

0 scopedFalseNotTrue : False = True -> Void
scopedFalseNotTrue Refl impossible

data ScopedSystemStateProjection :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (state : SystemState name key value world error) -> Type where
  MkScopedSystemStateProjection :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {state : SystemState name key value world error} ->
    (projectedWorld : world) ->
    (projectedRegistry : Registry name key value world error) ->
    (0 projectedStateExact :
      (state = MkSystemState projectedWorld projectedRegistry)) ->
    ScopedSystemStateProjection name key world error value state

0 scopedSystemStateProjection :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (state : SystemState name key value world error) ->
  ScopedSystemStateProjection name key world error value state
scopedSystemStateProjection name key world error value state =
  case state of
    MkSystemState observedWorld observedRegistry =>
      MkScopedSystemStateProjection observedWorld observedRegistry Refl

0 scopedInsertAbsentNotInstalledFromProjection :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (actor : name) ->
  (state : SystemState name key value world error) ->
  (projectedWorld : world) ->
  (projectedRegistry : Registry name key value world error) ->
  (0 projectedStateExact :
    (state = MkSystemState projectedWorld projectedRegistry)) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor projectedRegistry =
    the (Maybe (Fiber name key value world error)) Nothing ->
  installedAt @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor state = True ->
  Void
scopedInsertAbsentNotInstalledFromProjection name key world error value nameEq
  actor state projectedWorld projectedRegistry projectedStateExact absent
  installedTrue =
    scopedFalseNotTrue
      (the (False = True)
        (trans
          (sym
            (installedAtMissing
              {name = name} {key = key} {world = world} {error = error}
              {value = value} nameEq actor state
              (the (Maybe (Fiber name key value world error)) Nothing)
              (trans
                (cong
                  (lookupFiber @{nameEq} {name = name} {key = key}
                    {value = value} {world = world} {error = error} actor)
                  (cong registry projectedStateExact))
                absent)
              Refl))
          installedTrue))

0 scopedSelectedInsertPlanImpossible :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (state : SystemState name key value world error) ->
  (projectedWorld : world) ->
  (projectedRegistry : Registry name key value world error) ->
  (0 projectedStateExact :
    (state = MkSystemState projectedWorld projectedRegistry)) ->
  (afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error}
    (OInsert selected parent component) state = Just (tag, afterState) ->
  installedAt @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} selected state = True ->
  Void
scopedSelectedInsertPlanImpossible name key world error value nameEq keyEq
  selected parent component state projectedWorld projectedRegistry
  projectedStateExact afterState tag raw sourceInstalled =
    case foreignInsertPlanView nameEq keyEq selected parent component
      projectedWorld projectedRegistry tag afterState
      (trans
        (sym
          (cong
            (applyAction @{nameEq} @{keyEq} {name = name} {key = key}
              {value = value} {world = world} {error = error}
              (the (Action name key value world error)
                (OInsert selected parent component)))
            projectedStateExact))
        raw) of
      MkForeignInsertPlanView absent guards =>
        scopedInsertAbsentNotInstalledFromProjection name key world error value
          nameEq selected state projectedWorld projectedRegistry
          projectedStateExact absent sourceInstalled

0 scopedSelectedInsertImpossible :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  checkedApplyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (OInsert selected parent component) before = Just (tag, afterState) ->
  installedAt @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} selected before = True ->
  Void
scopedSelectedInsertImpossible name key world error value nameEq keyEq selected
  parent component before afterState tag checked sourceInstalled =
    case scopedSystemStateProjection name key world error value before of
      MkScopedSystemStateProjection projectedWorld projectedRegistry
        projectedStateExact =>
          scopedSelectedInsertPlanImpossible name key world error value nameEq
            keyEq selected parent component before projectedWorld
            projectedRegistry projectedStateExact afterState tag
            (checkedActionProjects nameEq keyEq
              (the (Action name key value world error)
                (OInsert selected parent component))
              before afterState tag checked)
            sourceInstalled

0 scopedRetireViewTag :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (actor : name) -> (ambient : world) ->
  (source : Registry name key value world error) -> (tag : RuleTag) ->
  (afterState : SystemState name key value world error) ->
  RetireSuccessView name key world error value nameEq actor ambient source tag
    afterState ->
  (tag = ORetireTag)
scopedRetireViewTag name key world error value nameEq actor ambient source tag
  afterState view =
    case view of
      MkRetireSuccessView fiber found => Refl

0 scopedSelectedRetireRetainedHeadAtTag :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  {wholeFirst, wholeLast : SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  checkedApplyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (ORetire selected) before = Just (ORetireTag, afterState) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  RetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
    registered live (ORetire selected) ORetireTag afterState
    (MkSystemState (worldState before)
      (planTarget (completePlanResult (selectedBoundaryPlan boundary)))) ->
  SelectedEpisodeRetainedHead name key world error value nameEq keyEq selected
    registered ordinal live whole (ORetire selected) afterState survivor
scopedSelectedRetireRetainedHeadAtTag name key world error value nameEq keyEq
  selected registered ordinal live whole before afterState survivor checkedAt
  boundary stepAt =
    case retainedSelectedRetirePreservesEpisodeBoundary nameEq keyEq selected
      registered ordinal live whole before afterState survivor checkedAt boundary
      stepAt of
      MkSelectedRetainedEpisodeStep named fired nextBoundary =>
        MkSelectedEpisodeRetainedHead named fired nextBoundary

0 scopedSelectedRetireRetainedHead :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  {wholeFirst, wholeLast : SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (ORetire selected) before = Just (tag, afterState)) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  (exactStep : RetainedNoEpisodeBoundaryStep name key world error value nameEq
    keyEq registered live (ORetire selected) tag afterState
    (MkSystemState (worldState before)
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))))) ->
  SelectedEpisodeRetainedHead name key world error value nameEq keyEq selected
    registered ordinal live whole (ORetire selected) afterState survivor
scopedSelectedRetireRetainedHead name key world error value nameEq keyEq selected
  registered ordinal live whole before afterState survivor tag checked boundary
  exactStep =
    scopedSelectedRetireRetainedHeadAtTag name key world error value nameEq keyEq
      selected registered ordinal live whole before afterState survivor
      (replace
        {p = \observed =>
          checkedApplyAction @{nameEq} @{keyEq} {name = name} {key = key}
            {value = value} {world = world} {error = error}
            (ORetire selected) before = Just (observed, afterState)}
        (scopedRetireViewTag name key world error value nameEq selected
          (worldState before) (registry before) tag afterState
          (retireSuccessView nameEq keyEq selected (worldState before)
            (registry before) tag afterState
            (trans
              (cong
                (applyAction @{nameEq} @{keyEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error}
                  (the (Action name key value world error)
                    (ORetire selected)))
                (scopedSystemStateEta before))
              (checkedActionProjects nameEq keyEq
                (the (Action name key value world error) (ORetire selected))
                before afterState tag checked))))
        checked)
      boundary
      (replace
        {p = \observed =>
          RetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
            registered live (ORetire selected) observed afterState
            (MkSystemState (worldState before)
              (planTarget
                (completePlanResult (selectedBoundaryPlan boundary))))}
        (scopedRetireViewTag name key world error value nameEq selected
          (worldState before) (registry before) tag afterState
          (retireSuccessView nameEq keyEq selected (worldState before)
            (registry before) tag afterState
            (trans
              (cong
                (applyAction @{nameEq} @{keyEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error}
                  (the (Action name key value world error)
                    (ORetire selected)))
                (scopedSystemStateEta before))
              (checkedActionProjects nameEq keyEq
                (the (Action name key value world error) (ORetire selected))
                before afterState tag checked))))
        exactStep)

0 scopedSelectedRetireOwnedHead :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) ->
  (0 ownerSelected : (actor = selected)) ->
  (registered : List (RegistrationGeneration name)) ->
  {globalFirst, globalLast : SystemState name key value world error} ->
  (global : Transitions globalFirst globalLast) ->
  (globalDiscipline : RegistrationDiscipline protocol nameEq global) ->
  {wholeFirst, wholeLast : SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (wholeInGlobal : OccurrenceEmbedding whole global) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (unique : GenerationEnvironmentNamesUnique live) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (ORetire actor) before = Just (tag, afterState)) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState} nameEq keyEq
      (the (Action name key value world error) (ORetire actor)) tag checked)
    whole) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  (retained : Not (EpisodeGenerationDeletedActor nameEq selected registered
    ordinal live
    (the (Action name key value world error) (ORetire actor)))) ->
  SelectedEpisodeRetainedHead name key world error value nameEq keyEq selected
    registered ordinal live whole
    (the (Action name key value world error) (ORetire actor)) afterState survivor
scopedSelectedRetireOwnedHead name key world error value protocol nameEq keyEq
  selected actor ownerSelected registered global globalDiscipline whole
  wholeInGlobal ordinal live unique before afterState survivor tag checked occurs
  boundary retained =
    case ownerSelected of
      Refl =>
        scopedSelectedRetireRetainedHead name key world error value nameEq keyEq
          selected registered ordinal live whole before afterState survivor tag
          checked boundary
          (scopedRetainedNoEpisodeBoundaryStep protocol nameEq keyEq selected
            registered global globalDiscipline whole wholeInGlobal ordinal live
            unique (ORetire selected) before afterState survivor tag checked
            occurs boundary
            (\owned => retained (DeleteRegisteredGeneration owned)))

0 ScopedForeignLifecycleExclusion :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {selected : name} -> {registered : List (RegistrationGeneration name)} ->
  {ordinal : Nat} -> {live : GenerationEnvironment name} ->
  {wholeFirst, wholeLast, before, survivor :
    SystemState name key value world error} ->
  {whole : Transitions wholeFirst wholeLast} ->
  {action : Action name key value world error} ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) -> Type
ScopedForeignLifecycleExclusion {name} {key} {world} {error} {value}
  {nameEq} {keyEq} {selected} {before} {survivor} {action} boundary =
    (leftSelected, leftOwner, rightOwner : Fiber name key value world error) ->
    lookupFiber @{nameEq} selected
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))) =
      Just leftSelected ->
    lookupFiber @{nameEq} (actionOwner action)
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))) =
      Just leftOwner ->
    lookupFiber @{nameEq} selected (registry before) = Just leftSelected ->
    lookupFiber @{nameEq} (actionOwner action) (registry before) =
      Just leftOwner ->
    lookupFiber @{nameEq} (actionOwner action) (registry survivor) =
      Just rightOwner ->
    FiberControlRelated leftOwner rightOwner ->
    (wanted : key) ->
    Elem wanted (dependencies
      (componentDependencies (fiberComponent leftOwner))) ->
    providerCandidate @{keyEq} wanted leftSelected = False

0 retainedForeignLifecycleFromScopedOwner :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) ->
  (lifecycle : isLifecycleAction action = True) ->
  (distinct : Not (actionOwner action = selected)) ->
  {wholeFirst, wholeLast : SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) whole) ->
  (independent : TraceIndependent name key world error value keyEq whole) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  (emptyPlan : EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary)))) ->
  (selectedOutsidePlan : ActorOutsideDeletionPlan selected
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary)))) ->
  (ownerOutsidePlan : ActorOutsideDeletionPlan (actionOwner action)
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary)))) ->
  (exactStep : RetainedNoEpisodeBoundaryStep name key world error value nameEq
    keyEq registered
    (advanceGenerationEnvironment @{nameEq} ordinal action live) action tag
    afterState
    (MkSystemState (worldState before)
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))))) ->
  (scopedExclusion : ScopedForeignLifecycleExclusion
    {name = name} {key = key} {world = world} {error = error} {value = value}
    {nameEq = nameEq} {keyEq = keyEq} {selected = selected}
    {registered = registered} {ordinal = ordinal} {live = live}
    {wholeFirst = wholeFirst} {wholeLast = wholeLast} {before = before}
    {survivor = survivor} {whole = whole} {action = action} boundary) ->
  (leftOwner : Fiber name key value world error) ->
  lookupFiber @{nameEq} (actionOwner action)
    (planTarget (completePlanResult (selectedBoundaryPlan boundary))) =
    Just leftOwner ->
  ForeignRetainedEpisodeStep name key world error value nameEq keyEq selected
    registered ordinal live whole action afterState survivor
retainedForeignLifecycleFromScopedOwner
  {name} {key} {world} {error} {value}
  nameEq keyEq selected registered ordinal live action lifecycle distinct whole
  before afterState survivor tag checked occurs independent boundary emptyPlan
  selectedOutsidePlan ownerOutsidePlan exactStep scopedExclusion leftOwner
  leftFound =
    case foreignControlLookupFound nameEq (actionOwner action)
      (planTarget (completePlanResult (selectedBoundaryPlan boundary)))
      (registry survivor) leftOwner leftFound
      (selectedOrderedForeignLookupControls nameEq selected
        (actionOwner action) distinct
        (planTarget (completePlanResult (selectedBoundaryPlan boundary)))
        (registry survivor) (selectedBoundaryOrderedControls boundary)) of
      MkForeignRelatedFiberFound rightOwner rightFound ownersRelated =>
        packageForeignLifecycleEpisodeStep nameEq keyEq selected registered
          ordinal live action lifecycle distinct whole before afterState
          survivor tag checked occurs independent boundary exactStep leftOwner
          rightOwner
          (trans
            (sym (lookupOutsideInactivePlan nameEq (actionOwner action)
              (registry before)
              (planTarget (completePlanResult
                (selectedBoundaryPlan boundary)))
              (inactiveLeafPlan (completePlanResult
                (selectedBoundaryPlan boundary))) ownerOutsidePlan))
            leftFound)
          rightFound ownersRelated
          (scopedLifecycleControlTransportBefore
            (scopedSystemStateEta survivor)
            (scopedForeignLifecycleControlsFromExclusion nameEq keyEq selected
              action distinct lifecycle (worldState before)
              (worldState survivor)
              (planTarget (completePlanResult
                (selectedBoundaryPlan boundary)))
              (registry survivor) leftOwner rightOwner
              (modelFiber (selectedBoundaryModel
                (selectedBoundaryEffects boundary)))
              (trans
                (lookupOutsideInactivePlan nameEq selected (registry before)
                  (planTarget (completePlanResult
                    (selectedBoundaryPlan boundary)))
                  (inactiveLeafPlan (completePlanResult
                    (selectedBoundaryPlan boundary))) selectedOutsidePlan)
                (modelFound (selectedBoundaryModel
                  (selectedBoundaryEffects boundary))))
              leftFound rightFound
              (scopedExclusion
                (modelFiber (selectedBoundaryModel
                  (selectedBoundaryEffects boundary)))
                leftOwner rightOwner
                (trans
                  (lookupOutsideInactivePlan nameEq selected (registry before)
                    (planTarget (completePlanResult
                      (selectedBoundaryPlan boundary)))
                    (inactiveLeafPlan (completePlanResult
                      (selectedBoundaryPlan boundary))) selectedOutsidePlan)
                  (modelFound (selectedBoundaryModel
                    (selectedBoundaryEffects boundary))))
                leftFound
                (modelFound (selectedBoundaryModel
                  (selectedBoundaryEffects boundary)))
                (trans
                  (sym (lookupOutsideInactivePlan nameEq (actionOwner action)
                    (registry before)
                    (planTarget (completePlanResult
                      (selectedBoundaryPlan boundary)))
                    (inactiveLeafPlan (completePlanResult
                      (selectedBoundaryPlan boundary))) ownerOutsidePlan))
                  leftFound)
                rightFound ownersRelated)
              (replace
                {p = \observed => SelectedSurvivorCleanInactive name key world
                  error value nameEq selected observed}
                (sym (scopedSystemStateEta survivor))
                (selectedBoundarySurvivorCleanInactive boundary))
              (selectedBoundaryOrderedControls boundary)
              (selectedBoundaryForeignLocatedTablesSame nameEq keyEq selected
                boundary)
              (namedTag (retainedBoundaryNamed exactStep))
              (namedAfter (retainedBoundaryNamed exactStep))
              (namedFireProjectsRaw nameEq keyEq action
                (MkSystemState (worldState before)
                  (planTarget (completePlanResult
                    (selectedBoundaryPlan boundary))))
                (retainedBoundaryNamed exactStep)
                (retainedBoundaryFires exactStep))
              (selectedSurvivorWellFormed boundary)
              (scopedSelectedLifecycleOutcomes nameEq keyEq selected registered
                ordinal live action distinct whole independent tag checked
                occurs boundary emptyPlan
                (lookupOutsideInactivePlan nameEq (actionOwner action)
                  (registry before)
                  (planTarget (completePlanResult
                    (selectedBoundaryPlan boundary)))
                  (inactiveLeafPlan (completePlanResult
                    (selectedBoundaryPlan boundary))) ownerOutsidePlan))))

||| Raw-free retained foreign lifecycle replay.  The selected local replayer
||| specializes its occurrence-scoped provider before entering this helper, so
||| the control dispatcher consumes only the direct Boolean exclusion leaf.
0 retainedForeignLifecycleFromScopedExclusion :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) ->
  (lifecycle : isLifecycleAction action = True) ->
  (distinct : Not (actionOwner action = selected)) ->
  {wholeFirst, wholeLast : SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) whole) ->
  (independent : TraceIndependent name key world error value keyEq whole) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  (emptyPlan : EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary)))) ->
  (selectedOutsidePlan : ActorOutsideDeletionPlan selected
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary)))) ->
  (ownerOutsidePlan : ActorOutsideDeletionPlan (actionOwner action)
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary)))) ->
  (exactStep : RetainedNoEpisodeBoundaryStep name key world error value nameEq
    keyEq registered
    (advanceGenerationEnvironment @{nameEq} ordinal action live) action tag
    afterState
    (MkSystemState (worldState before)
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))))) ->
  (scopedExclusion : ScopedForeignLifecycleExclusion
    {name = name} {key = key} {world = world} {error = error} {value = value}
    {nameEq = nameEq} {keyEq = keyEq} {selected = selected}
    {registered = registered} {ordinal = ordinal} {live = live}
    {wholeFirst = wholeFirst} {wholeLast = wholeLast} {before = before}
    {survivor = survivor} {whole = whole} {action = action} boundary) ->
  ForeignRetainedEpisodeStep name key world error value nameEq keyEq selected
    registered ordinal live whole action afterState survivor
retainedForeignLifecycleFromScopedExclusion nameEq keyEq selected registered
  ordinal live action lifecycle distinct whole before afterState survivor tag
  checked occurs independent boundary emptyPlan selectedOutsidePlan
  ownerOutsidePlan exactStep scopedExclusion =
    case lifecycleOwnerPresent nameEq keyEq action lifecycle
      (MkSystemState (worldState before)
        (planTarget (completePlanResult (selectedBoundaryPlan boundary))))
      (namedAfter (retainedBoundaryNamed exactStep))
      (namedTag (retainedBoundaryNamed exactStep))
      (namedFireProjectsRaw nameEq keyEq action
        (MkSystemState (worldState before)
          (planTarget (completePlanResult (selectedBoundaryPlan boundary))))
        (retainedBoundaryNamed exactStep) (retainedBoundaryFires exactStep)) of
      (leftOwner ** leftFound) =>
        retainedForeignLifecycleFromScopedOwner nameEq keyEq selected registered
          ordinal live action lifecycle distinct whole before afterState
          survivor tag checked occurs independent boundary emptyPlan
          selectedOutsidePlan ownerOutsidePlan exactStep scopedExclusion
          leftOwner leftFound

0 scopedForeignLifecycleRetainedHead :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (global : Transitions globalFirst globalLast) ->
  (globalDiscipline : RegistrationDiscipline protocol nameEq global) ->
  (independent : TraceIndependent name key world error value keyEq global) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (selectedEpisode : ClosedEpisode name key world error value nameEq keyEq
    selected selectedPre selectedAfter) ->
  (wholeInGlobal : OccurrenceEmbedding whole global) ->
  (anchors : ScopedSelectedEpisodeLifecycleProvider name key world error value
    nameEq keyEq selected registered global selectedEpisode) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (unique : GenerationEnvironmentNamesUnique live) ->
  (stamped : GenerationEnvironmentStamped live) ->
  (action : Action name key value world error) ->
  (lifecycle : isLifecycleAction action = True) ->
  (distinct : Not (actionOwner action = selected)) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (rest : Transitions afterState (lastInstalledState selectedEpisode)) ->
  (selectedRest : InstalledTrace name key world error value nameEq keyEq
    selected rest) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) whole) ->
  (insidePrefix : Transitions (closedStartState selectedEpisode) before) ->
  (insideDecomposition : appendTransitions insidePrefix
    (MoreTransitions (Fired nameEq keyEq action tag checked) rest) =
      closedInside selectedEpisode) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  (emptyPlan : EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary)))) ->
  (retained : Not (EpisodeGenerationDeletedActor nameEq selected registered
    ordinal live action)) ->
  SelectedEpisodeRetainedHead name key world error value nameEq keyEq selected
    registered ordinal live whole action afterState survivor
scopedForeignLifecycleRetainedHead protocol nameEq keyEq selected registered
  selectedOutside global globalDiscipline independent whole selectedEpisode
  wholeInGlobal anchors ordinal live unique stamped action lifecycle distinct
  before afterState survivor tag checked rest selectedRest occurs insidePrefix
  insideDecomposition boundary emptyPlan retained =
    scopedForeignRetainedHead
      (retainedForeignLifecycleFromScopedExclusion nameEq keyEq selected
        registered ordinal live action lifecycle distinct whole before afterState
        survivor tag checked occurs
        (restrictTraceIndependent
          (\transition, occurrence => wholeInGlobal transition occurrence)
          independent)
        boundary emptyPlan
        (scopedSelectedSourceOutsidePlan nameEq selected registered live stamped
          selectedOutside boundary)
        (actorOutsidePlan (completePlanResult (selectedBoundaryPlan boundary))
          (actionOwner action)
          (retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal
            live unique action (scopedLifecycleNonInsert action lifecycle)
            (\owned => retained (DeleteRegisteredGeneration owned))))
        (scopedRetainedNoEpisodeBoundaryStep protocol nameEq keyEq selected
          registered global globalDiscipline whole wholeInGlobal ordinal live
          unique action before afterState survivor tag checked occurs boundary
          (\owned => retained (DeleteRegisteredGeneration owned)))
        (scopedLifecycleExcludesSelectedAt anchors ordinal live action lifecycle
          distinct before afterState tag checked rest selectedRest
          (wholeInGlobal (Fired nameEq keyEq action tag checked) occurs)
          insidePrefix insideDecomposition boundary))

0 scopedForeignOrchestrationRetainedHead :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (global : Transitions globalFirst globalLast) ->
  (globalDiscipline : RegistrationDiscipline protocol nameEq global) ->
  (independent : TraceIndependent name key world error value keyEq global) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (wholeInGlobal : OccurrenceEmbedding whole global) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (unique : GenerationEnvironmentNamesUnique live) ->
  (action : Action name key value world error) ->
  (orchestration : isLifecycleAction action = False) ->
  (distinct : Not (actionOwner action = selected)) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) whole) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  (retained : Not (EpisodeGenerationDeletedActor nameEq selected registered
    ordinal live action)) ->
  SelectedEpisodeRetainedHead name key world error value nameEq keyEq selected
    registered ordinal live whole action afterState survivor
scopedForeignOrchestrationRetainedHead protocol nameEq keyEq selected registered
  global globalDiscipline independent whole wholeInGlobal ordinal live unique
  action orchestration distinct before afterState survivor tag checked occurs
  boundary retained =
    scopedForeignRetainedHead
      (retainedForeignOrchestrationPreservesEpisodeBoundary nameEq keyEq selected
        registered ordinal live action orchestration distinct whole before
        afterState survivor tag checked occurs
        (restrictTraceIndependent
          (\transition, occurrence => wholeInGlobal transition occurrence)
          independent)
        boundary
        (scopedRetainedNoEpisodeBoundaryStep protocol nameEq keyEq selected
          registered global globalDiscipline whole wholeInGlobal ordinal live
          unique action before afterState survivor tag checked occurs boundary
          (\owned => retained (DeleteRegisteredGeneration owned))))

0 scopedDispatchForeignRetainedHead :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (global : Transitions globalFirst globalLast) ->
  (globalDiscipline : RegistrationDiscipline protocol nameEq global) ->
  (independent : TraceIndependent name key world error value keyEq global) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (selectedEpisode : ClosedEpisode name key world error value nameEq keyEq
    selected selectedPre selectedAfter) ->
  (wholeInGlobal : OccurrenceEmbedding whole global) ->
  (anchors : ScopedSelectedEpisodeLifecycleProvider name key world error value
    nameEq keyEq selected registered global selectedEpisode) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (unique : GenerationEnvironmentNamesUnique live) ->
  (stamped : GenerationEnvironmentStamped live) ->
  (action : Action name key value world error) ->
  (distinct : Not (actionOwner action = selected)) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (rest : Transitions afterState (lastInstalledState selectedEpisode)) ->
  (selectedRest : InstalledTrace name key world error value nameEq keyEq
    selected rest) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) whole) ->
  (insidePrefix : Transitions (closedStartState selectedEpisode) before) ->
  (insideDecomposition : appendTransitions insidePrefix
    (MoreTransitions (Fired nameEq keyEq action tag checked) rest) =
      closedInside selectedEpisode) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  (emptyPlan : EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary)))) ->
  (retained : Not (EpisodeGenerationDeletedActor nameEq selected registered
    ordinal live action)) ->
  SelectedEpisodeRetainedHead name key world error value nameEq keyEq selected
    registered ordinal live whole action afterState survivor
scopedDispatchForeignRetainedHead protocol nameEq keyEq selected registered
  selectedOutside global globalDiscipline independent whole selectedEpisode
  wholeInGlobal anchors ordinal live unique stamped
  (OInsert actor parent component) distinct before afterState survivor tag
  checked rest selectedRest occurs insidePrefix insideDecomposition boundary
  emptyPlan retained =
    scopedForeignOrchestrationRetainedHead protocol nameEq keyEq selected
      registered global globalDiscipline independent whole wholeInGlobal ordinal
      live unique (OInsert actor parent component) Refl distinct before
      afterState survivor tag checked occurs boundary retained
scopedDispatchForeignRetainedHead protocol nameEq keyEq selected registered
  selectedOutside global globalDiscipline independent whole selectedEpisode
  wholeInGlobal anchors ordinal live unique stamped (ORetire actor) distinct
  before afterState survivor tag checked rest selectedRest occurs insidePrefix
  insideDecomposition boundary emptyPlan retained =
    scopedForeignOrchestrationRetainedHead protocol nameEq keyEq selected
      registered global globalDiscipline independent whole wholeInGlobal ordinal
      live unique (ORetire actor) Refl distinct before afterState survivor tag
      checked occurs boundary retained
scopedDispatchForeignRetainedHead protocol nameEq keyEq selected registered
  selectedOutside global globalDiscipline independent whole selectedEpisode
  wholeInGlobal anchors ordinal live unique stamped (ORemove actor) distinct
  before afterState survivor tag checked rest selectedRest occurs insidePrefix
  insideDecomposition boundary emptyPlan retained =
    scopedForeignOrchestrationRetainedHead protocol nameEq keyEq selected
      registered global globalDiscipline independent whole wholeInGlobal ordinal
      live unique (ORemove actor) Refl distinct before afterState survivor tag
      checked occurs boundary retained
scopedDispatchForeignRetainedHead protocol nameEq keyEq selected registered
  selectedOutside global globalDiscipline independent whole selectedEpisode
  wholeInGlobal anchors ordinal live unique stamped (LBegin actor) distinct before
  afterState survivor tag checked rest selectedRest occurs insidePrefix
  insideDecomposition boundary emptyPlan retained =
    scopedForeignLifecycleRetainedHead protocol nameEq keyEq selected registered
      selectedOutside global globalDiscipline independent whole selectedEpisode
      wholeInGlobal anchors ordinal live unique stamped (LBegin actor) Refl
      distinct before afterState survivor tag checked rest selectedRest occurs
      insidePrefix insideDecomposition boundary emptyPlan retained
scopedDispatchForeignRetainedHead protocol nameEq keyEq selected registered
  selectedOutside global globalDiscipline independent whole selectedEpisode
  wholeInGlobal anchors ordinal live unique stamped (LAdvance actor) distinct
  before afterState survivor tag checked rest selectedRest occurs insidePrefix
  insideDecomposition boundary emptyPlan retained =
    scopedForeignLifecycleRetainedHead protocol nameEq keyEq selected registered
      selectedOutside global globalDiscipline independent whole selectedEpisode
      wholeInGlobal anchors ordinal live unique stamped (LAdvance actor) Refl
      distinct before afterState survivor tag checked rest selectedRest occurs
      insidePrefix insideDecomposition boundary emptyPlan retained
scopedDispatchForeignRetainedHead protocol nameEq keyEq selected registered
  selectedOutside global globalDiscipline independent whole selectedEpisode
  wholeInGlobal anchors ordinal live unique stamped (LDivert actor) distinct
  before afterState survivor tag checked rest selectedRest occurs insidePrefix
  insideDecomposition boundary emptyPlan retained =
    scopedForeignLifecycleRetainedHead protocol nameEq keyEq selected registered
      selectedOutside global globalDiscipline independent whole selectedEpisode
      wholeInGlobal anchors ordinal live unique stamped (LDivert actor) Refl
      distinct before afterState survivor tag checked rest selectedRest occurs
      insidePrefix insideDecomposition boundary emptyPlan retained
scopedDispatchForeignRetainedHead protocol nameEq keyEq selected registered
  selectedOutside global globalDiscipline independent whole selectedEpisode
  wholeInGlobal anchors ordinal live unique stamped (LLeave actor) distinct before
  afterState survivor tag checked rest selectedRest occurs insidePrefix
  insideDecomposition boundary emptyPlan retained =
    scopedForeignLifecycleRetainedHead protocol nameEq keyEq selected registered
      selectedOutside global globalDiscipline independent whole selectedEpisode
      wholeInGlobal anchors ordinal live unique stamped (LLeave actor) Refl
      distinct before afterState survivor tag checked rest selectedRest occurs
      insidePrefix insideDecomposition boundary emptyPlan retained
scopedDispatchForeignRetainedHead protocol nameEq keyEq selected registered
  selectedOutside global globalDiscipline independent whole selectedEpisode
  wholeInGlobal anchors ordinal live unique stamped (LUnload actor) distinct before
  afterState survivor tag checked rest selectedRest occurs insidePrefix
  insideDecomposition boundary emptyPlan retained =
    scopedForeignLifecycleRetainedHead protocol nameEq keyEq selected registered
      selectedOutside global globalDiscipline independent whole selectedEpisode
      wholeInGlobal anchors ordinal live unique stamped (LUnload actor) Refl
      distinct before afterState survivor tag checked rest selectedRest occurs
      insidePrefix insideDecomposition boundary emptyPlan retained

0 scopedDispatchSelectedRetainedHead :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  {globalFirst, globalLast : SystemState name key value world error} ->
  (global : Transitions globalFirst globalLast) ->
  (globalDiscipline : RegistrationDiscipline protocol nameEq global) ->
  {wholeFirst, wholeLast : SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (wholeInGlobal : OccurrenceEmbedding whole global) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (unique : GenerationEnvironmentNamesUnique live) ->
  (action : Action name key value world error) ->
  (0 ownerSelected : (actionOwner action = selected)) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (sourceInstalled : installedAt @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} selected before = True) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState} nameEq keyEq action tag
      checked) whole) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  (retained : Not (EpisodeGenerationDeletedActor nameEq selected registered
    ordinal live action)) ->
  SelectedEpisodeRetainedHead name key world error value nameEq keyEq selected
    registered ordinal live whole action afterState survivor
scopedDispatchSelectedRetainedHead name key world error value protocol nameEq
  keyEq selected registered global globalDiscipline whole wholeInGlobal ordinal
  live unique (OInsert actor parent component) ownerSelected before afterState
  survivor tag checked sourceInstalled occurs boundary retained =
    void
      (scopedSelectedInsertImpossible name key world error value nameEq keyEq
        actor parent component before afterState tag checked
        (replace
          {p = \observed =>
            installedAt @{nameEq} {name = name} {key = key} {value = value}
              {world = world} {error = error} observed before = True}
          (sym ownerSelected) sourceInstalled))
scopedDispatchSelectedRetainedHead name key world error value protocol nameEq
  keyEq selected registered global globalDiscipline whole wholeInGlobal ordinal
  live unique (ORetire actor) ownerSelected before afterState survivor tag
  checked sourceInstalled occurs boundary retained =
    scopedSelectedRetireOwnedHead name key world error value protocol nameEq
      keyEq selected actor ownerSelected registered global globalDiscipline whole
      wholeInGlobal ordinal live unique before afterState survivor tag checked
      occurs boundary retained
scopedDispatchSelectedRetainedHead name key world error value protocol nameEq
  keyEq selected registered global globalDiscipline whole wholeInGlobal ordinal
  live unique (ORemove actor) ownerSelected before afterState survivor tag
  checked sourceInstalled occurs boundary retained =
    void
      (removeCannotInstalled nameEq keyEq actor before afterState tag
        (checkedActionProjects nameEq keyEq
          (the (Action name key value world error) (ORemove actor)) before
          afterState tag checked)
        (replace
          {p = \observed =>
            installedAt @{nameEq} {name = name} {key = key} {value = value}
              {world = world} {error = error} observed before = True}
          (sym ownerSelected) sourceInstalled))
scopedDispatchSelectedRetainedHead name key world error value protocol nameEq
  keyEq selected registered global globalDiscipline whole wholeInGlobal ordinal
  live unique (LBegin actor) ownerSelected before afterState survivor tag checked
  sourceInstalled occurs boundary retained =
    void (retained (DeleteEpisodeGenerationLifecycle ownerSelected Refl))
scopedDispatchSelectedRetainedHead name key world error value protocol nameEq
  keyEq selected registered global globalDiscipline whole wholeInGlobal ordinal
  live unique (LAdvance actor) ownerSelected before afterState survivor tag
  checked sourceInstalled occurs boundary retained =
    void (retained (DeleteEpisodeGenerationLifecycle ownerSelected Refl))
scopedDispatchSelectedRetainedHead name key world error value protocol nameEq
  keyEq selected registered global globalDiscipline whole wholeInGlobal ordinal
  live unique (LDivert actor) ownerSelected before afterState survivor tag checked
  sourceInstalled occurs boundary retained =
    void (retained (DeleteEpisodeGenerationLifecycle ownerSelected Refl))
scopedDispatchSelectedRetainedHead name key world error value protocol nameEq
  keyEq selected registered global globalDiscipline whole wholeInGlobal ordinal
  live unique (LLeave actor) ownerSelected before afterState survivor tag checked
  sourceInstalled occurs boundary retained =
    void (retained (DeleteEpisodeGenerationLifecycle ownerSelected Refl))
scopedDispatchSelectedRetainedHead name key world error value protocol nameEq
  keyEq selected registered global globalDiscipline whole wholeInGlobal ordinal
  live unique (LUnload actor) ownerSelected before afterState survivor tag checked
  sourceInstalled occurs boundary retained =
    void (retained (DeleteEpisodeGenerationLifecycle ownerSelected Refl))

0 scopedRegisteredLifecycleImpossible :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) ->
  (lifecycle : isLifecycleAction action = True) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (noBegin : IsBeginAction action ->
    GenerationOwnedActor nameEq registered ordinal live action -> Void) ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered
    live before ->
  GenerationOwnedActor nameEq registered ordinal live action ->
  Void
scopedRegisteredLifecycleImpossible name key world error value nameEq keyEq
  registered ordinal live (OInsert actor parent component) Refl before
  afterState tag checked noBegin inactive owned impossible
scopedRegisteredLifecycleImpossible name key world error value nameEq keyEq
  registered ordinal live (ORetire actor) Refl before afterState tag checked
  noBegin inactive owned impossible
scopedRegisteredLifecycleImpossible name key world error value nameEq keyEq
  registered ordinal live (ORemove actor) Refl before afterState tag checked
  noBegin inactive owned impossible
scopedRegisteredLifecycleImpossible name key world error value nameEq keyEq
  registered ordinal live (LBegin actor) lifecycle before afterState tag checked
  noBegin inactive owned = noBegin ItIsLBegin owned
scopedRegisteredLifecycleImpossible name key world error value nameEq keyEq
  registered ordinal live (LAdvance actor) lifecycle before afterState tag
  checked noBegin inactive (generation ** (current, member)) =
    inactiveCannotAdvance nameEq keyEq actor before afterState tag
      (checkedActionProjects nameEq keyEq
        (the (Action name key value world error) (LAdvance actor)) before
        afterState tag checked)
      (inactive actor generation member current)
scopedRegisteredLifecycleImpossible name key world error value nameEq keyEq
  registered ordinal live (LDivert actor) lifecycle before afterState tag
  checked noBegin inactive (generation ** (current, member)) =
    inactiveCannotDivert nameEq keyEq actor before afterState tag
      (checkedActionProjects nameEq keyEq
        (the (Action name key value world error) (LDivert actor)) before
        afterState tag checked)
      (inactive actor generation member current)
scopedRegisteredLifecycleImpossible name key world error value nameEq keyEq
  registered ordinal live (LLeave actor) lifecycle before afterState tag checked
  noBegin inactive (generation ** (current, member)) =
    inactiveCannotLeave nameEq keyEq actor before afterState tag
      (checkedActionProjects nameEq keyEq
        (the (Action name key value world error) (LLeave actor)) before
        afterState tag checked)
      (inactive actor generation member current)
scopedRegisteredLifecycleImpossible name key world error value nameEq keyEq
  registered ordinal live (LUnload actor) lifecycle before afterState tag
  checked noBegin inactive (generation ** (current, member)) =
    inactiveCannotUnload nameEq keyEq actor before afterState tag
      (checkedActionProjects nameEq keyEq
        (the (Action name key value world error) (LUnload actor)) before
        afterState tag checked)
      (inactive actor generation member current)

0 scopedDeletedRegisteredAtLocatedStep :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (unique : GenerationEnvironmentNamesUnique live) ->
  (stamped : GenerationEnvironmentStamped live) ->
  (selectedOutside :
    (generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (action : Action name key value world error) ->
  (orchestration : isLifecycleAction action = False) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  {restFinal : SystemState name key value world error} ->
  (rest : Transitions afterState restFinal) ->
  (stepDiscipline : RegistrationStepDiscipline protocol nameEq action before
    rest) ->
  {wholeFirst, wholeLast : SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (survivor : SystemState name key value world error) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  (oldEmpty : EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan
      (completePlanResult (selectedBoundaryPlan boundary)))) ->
  (owned : GenerationOwnedActor nameEq registered ordinal live action) ->
  SelectedEpisodeReplayBoundary name key world error value nameEq keyEq selected
    registered (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal action live) whole afterState
    survivor
scopedDeletedRegisteredAtLocatedStep name key world error value protocol nameEq
  keyEq selected registered ordinal live unique stamped selectedOutside action
  orchestration before afterState tag checked rest stepDiscipline whole survivor
  boundary oldEmpty owned =
    case deletedRegisteredOrchestrationHeadPreservesEpisodeBoundary protocol
      nameEq keyEq selected registered ordinal live unique stamped
      selectedOutside action orchestration before afterState tag checked rest
      stepDiscipline whole survivor boundary oldEmpty owned of
      MkDeletedRegisteredEpisodeBoundaryStep nextBoundary nextEmpty =>
        nextBoundary

0 scopedDeletedRegisteredOrchestrationBoundary :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  {globalFirst, globalLast : SystemState name key value world error} ->
  (global : Transitions globalFirst globalLast) ->
  (globalDiscipline : RegistrationDiscipline protocol nameEq global) ->
  {wholeFirst, wholeLast : SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (wholeInGlobal : OccurrenceEmbedding whole global) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (unique : GenerationEnvironmentNamesUnique live) ->
  (stamped : GenerationEnvironmentStamped live) ->
  (selectedOutside :
    (generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (action : Action name key value world error) ->
  (orchestration : isLifecycleAction action = False) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState} nameEq keyEq action tag
      checked) whole) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  (oldEmpty : EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan
      (completePlanResult (selectedBoundaryPlan boundary)))) ->
  (owned : GenerationOwnedActor nameEq registered ordinal live action) ->
  SelectedEpisodeReplayBoundary name key world error value nameEq keyEq selected
    registered (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal action live) whole afterState
    survivor
scopedDeletedRegisteredOrchestrationBoundary name key world error value protocol
  nameEq keyEq selected registered global globalDiscipline whole wholeInGlobal
  ordinal live unique stamped selectedOutside action orchestration before
  afterState survivor tag checked occurs boundary oldEmpty owned =
    case scopedRegistrationDisciplineAtOccurrence
      (Fired nameEq keyEq action tag checked) global globalDiscipline
      (wholeInGlobal (Fired nameEq keyEq action tag checked) occurs) of
      MkScopedLocatedRegistrationStep future futureDiscipline =>
        scopedDeletedRegisteredAtLocatedStep name key world error value protocol
          nameEq keyEq selected registered ordinal live unique stamped
          selectedOutside action orchestration before afterState tag checked
          future futureDiscipline whole survivor boundary oldEmpty owned

0 scopedDispatchDeletedRegisteredHead :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  {globalFirst, globalLast : SystemState name key value world error} ->
  (global : Transitions globalFirst globalLast) ->
  (globalDiscipline : RegistrationDiscipline protocol nameEq global) ->
  {wholeFirst, wholeLast : SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (wholeInGlobal : OccurrenceEmbedding whole global) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (unique : GenerationEnvironmentNamesUnique live) ->
  (stamped : GenerationEnvironmentStamped live) ->
  (selectedOutside :
    (generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (action : Action name key value world error) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (noBegin : IsBeginAction action ->
    GenerationOwnedActor nameEq registered ordinal live action -> Void) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState} nameEq keyEq action tag
      checked) whole) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  (oldEmpty : EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan
      (completePlanResult (selectedBoundaryPlan boundary)))) ->
  (inactive : CurrentRegisteredInactiveFibers name key world error value nameEq
    registered live before) ->
  (owned : GenerationOwnedActor nameEq registered ordinal live action) ->
  SelectedEpisodeReplayBoundary name key world error value nameEq keyEq selected
    registered (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal action live) whole afterState
    survivor
scopedDispatchDeletedRegisteredHead name key world error value protocol nameEq
  keyEq selected registered global globalDiscipline whole wholeInGlobal ordinal
  live unique stamped selectedOutside (OInsert actor parent component) before
  afterState survivor tag checked noBegin occurs boundary oldEmpty inactive
  owned =
    scopedDeletedRegisteredOrchestrationBoundary name key world error value
      protocol nameEq keyEq selected registered global globalDiscipline whole
      wholeInGlobal ordinal live unique stamped selectedOutside
      (OInsert actor parent component) Refl before afterState survivor tag checked
      occurs boundary oldEmpty owned
scopedDispatchDeletedRegisteredHead name key world error value protocol nameEq
  keyEq selected registered global globalDiscipline whole wholeInGlobal ordinal
  live unique stamped selectedOutside (ORetire actor) before afterState survivor
  tag checked noBegin occurs boundary oldEmpty inactive owned =
    scopedDeletedRegisteredOrchestrationBoundary name key world error value
      protocol nameEq keyEq selected registered global globalDiscipline whole
      wholeInGlobal ordinal live unique stamped selectedOutside (ORetire actor)
      Refl before afterState survivor tag checked occurs boundary oldEmpty owned
scopedDispatchDeletedRegisteredHead name key world error value protocol nameEq
  keyEq selected registered global globalDiscipline whole wholeInGlobal ordinal
  live unique stamped selectedOutside (ORemove actor) before afterState survivor
  tag checked noBegin occurs boundary oldEmpty inactive owned =
    scopedDeletedRegisteredOrchestrationBoundary name key world error value
      protocol nameEq keyEq selected registered global globalDiscipline whole
      wholeInGlobal ordinal live unique stamped selectedOutside (ORemove actor)
      Refl before afterState survivor tag checked occurs boundary oldEmpty owned
scopedDispatchDeletedRegisteredHead name key world error value protocol nameEq
  keyEq selected registered global globalDiscipline whole wholeInGlobal ordinal
  live unique stamped selectedOutside (LBegin actor) before afterState survivor
  tag checked noBegin occurs boundary oldEmpty inactive owned =
    void (scopedRegisteredLifecycleImpossible name key world error value nameEq
      keyEq registered ordinal live (LBegin actor) Refl before afterState tag
      checked noBegin inactive owned)
scopedDispatchDeletedRegisteredHead name key world error value protocol nameEq
  keyEq selected registered global globalDiscipline whole wholeInGlobal ordinal
  live unique stamped selectedOutside (LAdvance actor) before afterState survivor
  tag checked noBegin occurs boundary oldEmpty inactive owned =
    void (scopedRegisteredLifecycleImpossible name key world error value nameEq
      keyEq registered ordinal live (LAdvance actor) Refl before afterState tag
      checked noBegin inactive owned)
scopedDispatchDeletedRegisteredHead name key world error value protocol nameEq
  keyEq selected registered global globalDiscipline whole wholeInGlobal ordinal
  live unique stamped selectedOutside (LDivert actor) before afterState survivor
  tag checked noBegin occurs boundary oldEmpty inactive owned =
    void (scopedRegisteredLifecycleImpossible name key world error value nameEq
      keyEq registered ordinal live (LDivert actor) Refl before afterState tag
      checked noBegin inactive owned)
scopedDispatchDeletedRegisteredHead name key world error value protocol nameEq
  keyEq selected registered global globalDiscipline whole wholeInGlobal ordinal
  live unique stamped selectedOutside (LLeave actor) before afterState survivor
  tag checked noBegin occurs boundary oldEmpty inactive owned =
    void (scopedRegisteredLifecycleImpossible name key world error value nameEq
      keyEq registered ordinal live (LLeave actor) Refl before afterState tag
      checked noBegin inactive owned)
scopedDispatchDeletedRegisteredHead name key world error value protocol nameEq
  keyEq selected registered global globalDiscipline whole wholeInGlobal ordinal
  live unique stamped selectedOutside (LUnload actor) before afterState survivor
  tag checked noBegin occurs boundary oldEmpty inactive owned =
    void (scopedRegisteredLifecycleImpossible name key world error value nameEq
      keyEq registered ordinal live (LUnload actor) Refl before afterState tag
      checked noBegin inactive owned)

0 scopedDispatchDeletedSelectedLifecycleHead :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (stamped : GenerationEnvironmentStamped live) ->
  (selectedOutside :
    (generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (action : Action name key value world error) ->
  (owner : actionOwner action = selected) ->
  (lifecycle : isLifecycleAction action = True) ->
  {wholeFirst, wholeLast : SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState} nameEq keyEq action tag
      checked) whole) ->
  (targetInstalled : installedAt @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} selected afterState = True) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  SelectedEpisodeReplayBoundary name key world error value nameEq keyEq selected
    registered (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal action live) whole afterState
    survivor
scopedDispatchDeletedSelectedLifecycleHead name key world error value nameEq
  keyEq selected registered ordinal live stamped selectedOutside
  (OInsert actor parent component) owner lifecycle whole before afterState
  survivor tag checked occurs targetInstalled boundary =
    void (scopedFalseNotTrue (the (False = True) lifecycle))
scopedDispatchDeletedSelectedLifecycleHead name key world error value nameEq
  keyEq selected registered ordinal live stamped selectedOutside (ORetire actor)
  owner lifecycle whole before afterState survivor tag checked occurs
  targetInstalled boundary =
    void (scopedFalseNotTrue (the (False = True) lifecycle))
scopedDispatchDeletedSelectedLifecycleHead name key world error value nameEq
  keyEq selected registered ordinal live stamped selectedOutside (ORemove actor)
  owner lifecycle whole before afterState survivor tag checked occurs
  targetInstalled boundary =
    void (scopedFalseNotTrue (the (False = True) lifecycle))
scopedDispatchDeletedSelectedLifecycleHead name key world error value nameEq
  keyEq selected registered ordinal live stamped selectedOutside (LBegin actor)
  owner lifecycle whole before afterState survivor tag checked occurs
  targetInstalled boundary =
    deletedSelectedInstalledHeadPreservesEpisodeBoundary nameEq keyEq selected
      registered ordinal live stamped selectedOutside (LBegin actor) tag before
      afterState checked owner Refl whole occurs targetInstalled survivor boundary
scopedDispatchDeletedSelectedLifecycleHead name key world error value nameEq
  keyEq selected registered ordinal live stamped selectedOutside
  (LAdvance actor) owner lifecycle whole before afterState survivor tag checked
  occurs targetInstalled boundary =
    deletedSelectedInstalledHeadPreservesEpisodeBoundary nameEq keyEq selected
      registered ordinal live stamped selectedOutside (LAdvance actor) tag before
      afterState checked owner Refl whole occurs targetInstalled survivor boundary
scopedDispatchDeletedSelectedLifecycleHead name key world error value nameEq
  keyEq selected registered ordinal live stamped selectedOutside
  (LDivert actor) owner lifecycle whole before afterState survivor tag checked
  occurs targetInstalled boundary =
    deletedSelectedInstalledHeadPreservesEpisodeBoundary nameEq keyEq selected
      registered ordinal live stamped selectedOutside (LDivert actor) tag before
      afterState checked owner Refl whole occurs targetInstalled survivor boundary
scopedDispatchDeletedSelectedLifecycleHead name key world error value nameEq
  keyEq selected registered ordinal live stamped selectedOutside (LLeave actor)
  owner lifecycle whole before afterState survivor tag checked occurs
  targetInstalled boundary =
    deletedSelectedInstalledHeadPreservesEpisodeBoundary nameEq keyEq selected
      registered ordinal live stamped selectedOutside (LLeave actor) tag before
      afterState checked owner Refl whole occurs targetInstalled survivor boundary
scopedDispatchDeletedSelectedLifecycleHead name key world error value nameEq
  keyEq selected registered ordinal live stamped selectedOutside (LUnload actor)
  owner lifecycle whole before afterState survivor tag checked occurs
  targetInstalled boundary =
    deletedSelectedInstalledHeadPreservesEpisodeBoundary nameEq keyEq selected
      registered ordinal live stamped selectedOutside (LUnload actor) tag before
      afterState checked owner Refl whole occurs targetInstalled survivor boundary

0 scopedReplayDeletedEpisodeHead :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  {globalFirst, globalLast : SystemState name key value world error} ->
  (global : Transitions globalFirst globalLast) ->
  (globalDiscipline : RegistrationDiscipline protocol nameEq global) ->
  {wholeFirst, wholeLast : SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (wholeInGlobal : OccurrenceEmbedding whole global) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (unique : GenerationEnvironmentNamesUnique live) ->
  (stamped : GenerationEnvironmentStamped live) ->
  (selectedOutside :
    (generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (action : Action name key value world error) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (sourceInstalled : installedAt @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} selected before = True) ->
  (targetInstalled : installedAt @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} selected afterState = True) ->
  {restFinal : SystemState name key value world error} ->
  (rest : Transitions afterState restFinal) ->
  (noBegin : IsBeginAction action ->
    GenerationOwnedActor nameEq registered ordinal live action -> Void) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState} nameEq keyEq action tag
      checked) whole) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  (oldEmpty : EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan
      (completePlanResult (selectedBoundaryPlan boundary)))) ->
  (inactive : CurrentRegisteredInactiveFibers name key world error value nameEq
    registered live before) ->
  EpisodeGenerationDeletedActor nameEq selected registered ordinal live action ->
  SelectedEpisodeReplayBoundary name key world error value nameEq keyEq selected
    registered (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal action live) whole afterState
    survivor
scopedReplayDeletedEpisodeHead name key world error value protocol nameEq keyEq
  selected registered global globalDiscipline whole wholeInGlobal ordinal live
  unique stamped selectedOutside action before afterState survivor tag checked
  sourceInstalled targetInstalled rest noBegin occurs boundary oldEmpty inactive
  deleted =
    case deleted of
      DeleteEpisodeGenerationLifecycle owner lifecycle =>
        scopedDispatchDeletedSelectedLifecycleHead name key world error value
          nameEq keyEq selected registered ordinal live stamped selectedOutside
          action owner lifecycle whole before afterState survivor tag checked
          occurs targetInstalled boundary
      DeleteRegisteredGeneration owned =>
        scopedDispatchDeletedRegisteredHead name key world error value protocol
          nameEq keyEq selected registered global globalDiscipline whole
          wholeInGlobal ordinal live unique stamped selectedOutside action before
          afterState survivor tag checked noBegin occurs boundary oldEmpty
          inactive owned

0 scopedReplayRetainedEpisodeHead :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  {globalFirst, globalLast : SystemState name key value world error} ->
  (global : Transitions globalFirst globalLast) ->
  (globalDiscipline : RegistrationDiscipline protocol nameEq global) ->
  (independent : TraceIndependent name key world error value keyEq global) ->
  {wholeFirst, wholeLast, selectedPre, selectedAfter :
    SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (selectedEpisode : ClosedEpisode name key world error value nameEq keyEq
    selected selectedPre selectedAfter) ->
  (wholeInGlobal : OccurrenceEmbedding whole global) ->
  (anchors : ScopedSelectedEpisodeLifecycleProvider name key world error value
    nameEq keyEq selected registered global selectedEpisode) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (unique : GenerationEnvironmentNamesUnique live) ->
  (stamped : GenerationEnvironmentStamped live) ->
  (selectedOutside :
    (generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (action : Action name key value world error) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (sourceInstalled : installedAt @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} selected before = True) ->
  (targetInstalled : installedAt @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} selected afterState = True) ->
  (rest : Transitions afterState (lastInstalledState selectedEpisode)) ->
  (selectedRest : InstalledTrace name key world error value nameEq keyEq
    selected rest) ->
  (noBegin : IsBeginAction action ->
    GenerationOwnedActor nameEq registered ordinal live action -> Void) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState} nameEq keyEq action tag
      checked) whole) ->
  (insidePrefix : Transitions (closedStartState selectedEpisode) before) ->
  (insideDecomposition : appendTransitions insidePrefix
    (MoreTransitions (Fired nameEq keyEq action tag checked) rest) =
      closedInside selectedEpisode) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  (emptyPlan : EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan
      (completePlanResult (selectedBoundaryPlan boundary)))) ->
  (inactive : CurrentRegisteredInactiveFibers name key world error value nameEq
    registered live before) ->
  (retained : Not (EpisodeGenerationDeletedActor nameEq selected registered
    ordinal live action)) ->
  SelectedEpisodeRetainedHead name key world error value nameEq keyEq selected
    registered ordinal live whole action afterState survivor
scopedReplayRetainedEpisodeHead name key world error value protocol nameEq keyEq
  selected registered global globalDiscipline independent whole selectedEpisode
  wholeInGlobal anchors ordinal live unique stamped selectedOutside action before
  afterState survivor tag checked sourceInstalled targetInstalled rest
  selectedRest noBegin occurs insidePrefix insideDecomposition boundary emptyPlan
  inactive retained =
    case decEq @{nameEq} (actionOwner action) selected of
      Yes ownerSelected =>
        scopedDispatchSelectedRetainedHead name key world error value protocol
          nameEq keyEq selected registered global globalDiscipline whole
          wholeInGlobal ordinal live unique action ownerSelected before afterState
          survivor tag checked sourceInstalled occurs boundary retained
      No ownerDistinct =>
        scopedDispatchForeignRetainedHead protocol nameEq keyEq selected
          registered selectedOutside global globalDiscipline independent whole
          selectedEpisode wholeInGlobal anchors ordinal live unique stamped action
          ownerDistinct before afterState survivor tag checked rest selectedRest
          occurs insidePrefix insideDecomposition boundary emptyPlan retained

0 scopedSelectedEpisodeLocalReplayer :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  {globalFirst, globalLast : SystemState name key value world error} ->
  (global : Transitions globalFirst globalLast) ->
  (globalDiscipline : RegistrationDiscipline protocol nameEq global) ->
  (independent : TraceIndependent name key world error value keyEq global) ->
  {wholeFirst, wholeLast, selectedPre, selectedAfter :
    SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (selectedEpisode : ClosedEpisode name key world error value nameEq keyEq
    selected selectedPre selectedAfter) ->
  (wholeInGlobal : OccurrenceEmbedding whole global) ->
  (anchors : ScopedSelectedEpisodeLifecycleProvider name key world error value
    nameEq keyEq selected registered global selectedEpisode) ->
  SelectedEpisodeLocalReplayer name key world error value nameEq keyEq selected
    registered protocol whole (closedInside selectedEpisode)
scopedSelectedEpisodeLocalReplayer name key world error value protocol nameEq
  keyEq selected registered global globalDiscipline independent whole
  selectedEpisode wholeInGlobal anchors =
    MkSelectedEpisodeLocalReplayer
      (scopedReplayDeletedEpisodeHead name key world error value protocol nameEq
        keyEq selected registered global globalDiscipline whole wholeInGlobal)
      (scopedReplayRetainedEpisodeHead name key world error value protocol nameEq
        keyEq selected registered global globalDiscipline independent whole
        selectedEpisode wholeInGlobal anchors)

0 scopedNoRegisteredAppendLeft :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  NoRegisteredEpisode nameEq registered ordinal live
    (appendTransitions left right) ->
  NoRegisteredEpisode nameEq registered ordinal live left
scopedNoRegisteredAppendLeft name key world error value nameEq registered ordinal
  live NoTransitions right noRegistered = NoRegisteredEpisodeEnd
scopedNoRegisteredAppendLeft name key world error value nameEq registered ordinal
  live (MoreTransitions transition@(Fired _ _ action tag checked) rest) right
  (NoRegisteredEpisodeStep
    (Fired _ _ action tag checked) (appendTransitions rest right) noBegin tail) =
      NoRegisteredEpisodeStep transition rest noBegin
        (scopedNoRegisteredAppendLeft name key world error value nameEq registered
          (S ordinal)
          (advanceGenerationEnvironment @{nameEq} ordinal action live) rest
          right tail)

0 scopedAppendLeftEmbedding :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  OccurrenceEmbedding left (appendTransitions left right)
scopedAppendLeftEmbedding name key world error value NoTransitions right
  transition occurs impossible
scopedAppendLeftEmbedding name key world error value
  (MoreTransitions transition rest) right transition OccursHere = OccursHere
scopedAppendLeftEmbedding name key world error value
  (MoreTransitions head rest) right transition (OccursLater later) =
    OccursLater
      (scopedAppendLeftEmbedding name key world error value rest right transition
        later)

0 scopedAppendRightEmbedding :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  OccurrenceEmbedding right (appendTransitions left right)
scopedAppendRightEmbedding name key world error value NoTransitions right
  transition occurs = occurs
scopedAppendRightEmbedding name key world error value
  (MoreTransitions head rest) right transition occurs =
    OccursLater
      (scopedAppendRightEmbedding name key world error value rest right
        transition occurs)

0 scopedTransportEmbeddingTarget :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {segmentFirst, segmentLast, wholeFirst, wholeLast :
    SystemState name key value world error} ->
  {segment : Transitions segmentFirst segmentLast} ->
  {left, right : Transitions wholeFirst wholeLast} ->
  (0 targetExact : (left = right)) ->
  OccurrenceEmbedding segment left ->
  OccurrenceEmbedding segment right
scopedTransportEmbeddingTarget name key world error value Refl embedding =
  embedding

0 scopedAppendGenerationScan :
  (name : Type) -> (nameEq : DecEq name) ->
  {key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  (middleOrdinal : Nat) -> (middleLive : GenerationEnvironment name) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq ordinal live left middleOrdinal middleLive ->
  GenerationTraceScan nameEq middleOrdinal middleLive right finalOrdinal
    finalLive ->
  GenerationTraceScan nameEq ordinal live (appendTransitions left right)
    finalOrdinal finalLive
scopedAppendGenerationScan name nameEq ordinal live left right middleOrdinal
  middleLive finalOrdinal finalLive leftScan rightScan =
    case leftScan of
      GenerationTraceScanEnd => rightScan
      GenerationTraceScanStep transition rest leftTail =>
        GenerationTraceScanStep transition (appendTransitions rest right)
          (scopedAppendGenerationScan name nameEq (S ordinal)
            (advanceGenerationEnvironment @{nameEq} ordinal
              (transitionAction transition) live)
            rest right middleOrdinal middleLive finalOrdinal finalLive leftTail
            rightScan)

record ScopedSelectedCloseReplayAppend
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (registered : List (RegistrationGeneration name))
  (ordinal : Nat) (live : GenerationEnvironment name)
  {originalFirst, closeBefore, closeAfter :
    SystemState name key value world error}
  (original : Transitions originalFirst closeBefore)
  (survivorFirst : SystemState name key value world error)
  (ready : GenerationReplayReady nameEq keyEq
    (EpisodeGenerationDeletedActor nameEq selected registered) ordinal live
    original survivorFirst)
  (target : SystemState name key value world error)
  (closing : UnloadStep nameEq keyEq selected closeBefore closeAfter) where
  constructor MkScopedSelectedCloseReplayAppend
  appendedSelectedCloseReady : GenerationReplayReady nameEq keyEq
    (EpisodeGenerationDeletedActor nameEq selected registered) ordinal live
    (appendTransitions original
      (MoreTransitions (unloadTransition closing) NoTransitions)) survivorFirst
  0 appendedSelectedCloseEnds : ReplayReadyEndsAt appendedSelectedCloseReady
    target

0 scopedAppendSelectedCloseReplay :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  {originalFirst, closeBefore, closeAfter :
    SystemState name key value world error} ->
  (original : Transitions originalFirst closeBefore) ->
  (survivorFirst : SystemState name key value world error) ->
  (ready : GenerationReplayReady nameEq keyEq
    (EpisodeGenerationDeletedActor nameEq selected registered) ordinal live
    original survivorFirst) ->
  (target : SystemState name key value world error) ->
  (ends : ReplayReadyEndsAt ready target) ->
  (closing : UnloadStep nameEq keyEq selected closeBefore closeAfter) ->
  ScopedSelectedCloseReplayAppend name key world error value nameEq keyEq
    selected registered ordinal live original survivorFirst ready target closing
scopedAppendSelectedCloseReplay name key world error value nameEq keyEq selected
  registered ordinal live original survivorFirst ready target ends closing =
    case ends of
      ReplayEndsEnd same =>
        MkScopedSelectedCloseReplayAppend
          (ReplayReadyDelete
            (the (EpisodeGenerationDeletedActor nameEq selected registered
              ordinal live
              (the (Action name key value world error) (LUnload selected)))
              (DeleteEpisodeGenerationLifecycle Refl Refl))
            ReplayReadyEnd)
          (ReplayEndsDelete
            (the (EpisodeGenerationDeletedActor nameEq selected registered
              ordinal live
              (the (Action name key value world error) (LUnload selected)))
              (DeleteEpisodeGenerationLifecycle Refl Refl))
            ReplayReadyEnd (ReplayEndsEnd same))
      ReplayEndsDelete {transition} {rest} deleted tail tailEnds =>
        MkScopedSelectedCloseReplayAppend
          (ReplayReadyDelete deleted
            (appendedSelectedCloseReady
              (scopedAppendSelectedCloseReplay name key world error value nameEq
                keyEq selected registered (S ordinal)
                (advanceGenerationEnvironment @{nameEq} ordinal
                  (transitionAction transition) live)
                rest survivorFirst tail target tailEnds closing)))
          (ReplayEndsDelete deleted
            (appendedSelectedCloseReady
              (scopedAppendSelectedCloseReplay name key world error value nameEq
                keyEq selected registered (S ordinal)
                (advanceGenerationEnvironment @{nameEq} ordinal
                  (transitionAction transition) live)
                rest survivorFirst tail target tailEnds closing))
            (appendedSelectedCloseEnds
              (scopedAppendSelectedCloseReplay name key world error value nameEq
                keyEq selected registered (S ordinal)
                (advanceGenerationEnvironment @{nameEq} ordinal
                  (transitionAction transition) live)
                rest survivorFirst tail target tailEnds closing)))
      ReplayEndsKeep {originalTransition} {rest} {survivingAfter} retained tag
        survivingTransition sameAction fires tail tailEnds =>
          MkScopedSelectedCloseReplayAppend
            (ReplayReadyKeep retained survivingAfter tag survivingTransition
              sameAction fires
              (appendedSelectedCloseReady
                (scopedAppendSelectedCloseReplay name key world error value
                  nameEq keyEq selected registered (S ordinal)
                  (advanceGenerationEnvironment @{nameEq} ordinal
                    (transitionAction originalTransition) live)
                  rest survivingAfter tail target tailEnds closing)))
            (ReplayEndsKeep retained tag survivingTransition sameAction fires
              (appendedSelectedCloseReady
                (scopedAppendSelectedCloseReplay name key world error value
                  nameEq keyEq selected registered (S ordinal)
                  (advanceGenerationEnvironment @{nameEq} ordinal
                    (transitionAction originalTransition) live)
                  rest survivingAfter tail target tailEnds closing))
              (appendedSelectedCloseEnds
                (scopedAppendSelectedCloseReplay name key world error value
                  nameEq keyEq selected registered (S ordinal)
                  (advanceGenerationEnvironment @{nameEq} ordinal
                    (transitionAction originalTransition) live)
                  rest survivingAfter tail target tailEnds closing)))

0 scopedInitialCurrentInactive :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (bounded : GenerationEnvironmentBounded ordinal live) ->
  (lower : (generation : RegistrationGeneration name) ->
    Elem generation registered ->
    LTE ordinal (generationBirthOrdinal generation)) ->
  (state : SystemState name key value world error) ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered
    live state
scopedInitialCurrentInactive name key world error value nameEq registered ordinal
  live bounded lower state actor generation member current =
    void
      (noCurrentRegisteredAtEpisodeStart registered live bounded lower actor
        generation
        (currentGenerationEntryFromLookup nameEq actor generation live current)
        member)

0 scopedInitialCurrentEmpty :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (bounded : GenerationEnvironmentBounded ordinal live) ->
  (lower : (generation : RegistrationGeneration name) ->
    Elem generation registered ->
    LTE ordinal (generationBirthOrdinal generation)) ->
  (state : SystemState name key value world error) ->
  CurrentRegisteredEmptyTables name key world error value nameEq registered live
    state
scopedInitialCurrentEmpty name key world error value nameEq registered ordinal
  live bounded lower state actor generation member current fiber found =
    void
      (noCurrentRegisteredAtEpisodeStart registered live bounded lower actor
        generation
        (currentGenerationEntryFromLookup nameEq actor generation live current)
        member)

0 scopedInsideNoRegistered :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  {preStart, afterClose : SystemState name key value world error} ->
  (episode : ClosedEpisode name key world error value nameEq keyEq selected
    preStart afterClose) ->
  NoRegisteredEpisode nameEq registered episodeStartOrdinal episodeStartLive
    (MoreTransitions (beginTransition (closedOpening episode))
      (closedTransitions episode)) ->
  NoRegisteredEpisode nameEq registered (S episodeStartOrdinal)
    episodeStartLive (closedInside episode)
scopedInsideNoRegistered name key world error value nameEq keyEq selected
  registered episodeStartOrdinal episodeStartLive episode centerNoRegistered =
    case centerNoRegistered of
      NoRegisteredEpisodeStep _ _ _ afterOpeningNoRegistered =>
        scopedNoRegisteredAppendLeft name key world error value nameEq registered
          (S episodeStartOrdinal) episodeStartLive (closedInside episode)
          (MoreTransitions (unloadTransition (closing episode)) NoTransitions)
          afterOpeningNoRegistered

0 scopedAlignedLocatedBefore :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  (consumer : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    consumer global) ->
  AlignedTransitions name key world error value nameEq keyEq
    (traceBeforeOpening episode)
scopedAlignedLocatedBefore name key world error value nameEq keyEq global aligned
  consumer episode =
    fst
      (alignedAppendSplit (traceBeforeOpening episode)
        (appendTransitions
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode episode)))
            (closedTransitions (locatedEpisode episode)))
          (traceAfterClosing episode))
        (rewrite (locatedDecomposition episode) in aligned))

0 scopedInitialSelectedBoundary :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (aligned : AlignedTransitions name key world error value nameEq keyEq global) ->
  (initialWellFormed : registryWellFormed @{nameEq} @{keyEq} initial = True) ->
  (selected : name) ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  (registered : List (RegistrationGeneration name)) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  (beforeScan : GenerationTraceScan nameEq 0 []
    (traceBeforeOpening located) episodeStartOrdinal episodeStartLive) ->
  (registeredDuring : RegisteredGenerationsDuring selected episodeStartOrdinal
    registered
    (MoreTransitions
      (beginTransition (closedOpening (locatedEpisode located)))
      (closedTransitions (locatedEpisode located)))) ->
  SelectedEpisodeReplayBoundary name key world error value nameEq keyEq selected
    registered (S episodeStartOrdinal) episodeStartLive
    (appendTransitions (closedTransitions (locatedEpisode located))
      (traceAfterClosing located))
    (closedStartState (locatedEpisode located)) (locatedPreStart located)
scopedInitialSelectedBoundary name key world error value nameEq keyEq global
  aligned initialWellFormed selected located registered episodeStartOrdinal
  episodeStartLive beforeScan registeredDuring =
    initialSelectedEpisodeBoundary nameEq keyEq selected registered
      episodeStartOrdinal episodeStartLive (traceBeforeOpening located) beforeScan
      (MoreTransitions
        (beginTransition (closedOpening (locatedEpisode located)))
        (closedTransitions (locatedEpisode located)))
      registeredDuring
      (appendTransitions (closedTransitions (locatedEpisode located))
        (traceAfterClosing located))
      (closedOpening (locatedEpisode located))
      (alignedTraceWellFormedEnd nameEq keyEq (traceBeforeOpening located)
        (scopedAlignedLocatedBefore name key world error value nameEq keyEq global
          aligned selected located)
        initialWellFormed)

0 scopedSelectedInsideEmbedding :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, finalState : SystemState name key value world error} ->
  {global : Transitions initial finalState} ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  OccurrenceEmbedding (closedInside (locatedEpisode located))
    (appendTransitions (closedTransitions (locatedEpisode located))
      (traceAfterClosing located))
scopedSelectedInsideEmbedding name key world error value nameEq keyEq selected
  located =
    scopedTransportEmbeddingTarget name key world error value
      (sym
        (appendTransitionsAssociative
          (closedInside (locatedEpisode located))
          (MoreTransitions
            (unloadTransition (closing (locatedEpisode located))) NoTransitions)
          (traceAfterClosing located)))
      (scopedAppendLeftEmbedding name key world error value
        (closedInside (locatedEpisode located))
        (MoreTransitions (unloadTransition (closing (locatedEpisode located)))
          (traceAfterClosing located)))

0 scopedInitialSelectedPlanEmpty :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  (unique : GenerationEnvironmentNamesUnique episodeStartLive) ->
  (bounded : GenerationEnvironmentBounded episodeStartOrdinal
    episodeStartLive) ->
  (lower : (generation : RegistrationGeneration name) ->
    Elem generation registered ->
    LTE episodeStartOrdinal (generationBirthOrdinal generation)) ->
  (state : SystemState name key value world error) ->
  {wholeFirst, wholeLast : SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (survivor : SystemState name key value world error) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered (S episodeStartOrdinal) episodeStartLive whole
    state survivor) ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan
      (completePlanResult (selectedBoundaryPlan boundary)))
scopedInitialSelectedPlanEmpty name key world error value nameEq keyEq selected
  registered episodeStartOrdinal episodeStartLive unique bounded lower state
  whole survivor boundary =
    completeCurrentRegisteredPlanHasEmptyTables nameEq registered
      episodeStartLive unique (worldState state) (registry state)
      (selectedBoundaryPlan boundary)
      (scopedInitialCurrentEmpty name key world error value nameEq registered
        episodeStartOrdinal episodeStartLive bounded lower state)

0 scopedAlignedLocatedInside :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (aligned : AlignedTransitions name key world error value nameEq keyEq global) ->
  (consumer : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    consumer global) ->
  AlignedTransitions name key world error value nameEq keyEq
    (closedInside (locatedEpisode episode))
scopedAlignedLocatedInside name key world error value nameEq keyEq global aligned
  consumer episode =
    fst
      (alignedAppendSplit (closedInside (locatedEpisode episode))
        (MoreTransitions
          (unloadTransition (closing (locatedEpisode episode))) NoTransitions)
        (alignedEpisodeInside (closedOpening (locatedEpisode episode))
          (closedTransitions (locatedEpisode episode))
          (alignedLocatedCenter global aligned episode)))

0 scopedSelectedInteriorFoldFromPremises :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (aligned : AlignedTransitions name key world error value nameEq keyEq global) ->
  (initialWellFormed : registryWellFormed @{nameEq} @{keyEq} initial = True) ->
  (selected : name) ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  (registered : List (RegistrationGeneration name)) ->
  (selectedOutside :
    (generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  (beforeScan : GenerationTraceScan nameEq 0 []
    (traceBeforeOpening located) episodeStartOrdinal episodeStartLive) ->
  (registeredDuring : RegisteredGenerationsDuring selected episodeStartOrdinal
    registered
    (MoreTransitions
      (beginTransition (closedOpening (locatedEpisode located)))
      (closedTransitions (locatedEpisode located)))) ->
  (noRegistered : NoRegisteredEpisode nameEq registered 0 [] global) ->
  (local : SelectedEpisodeLocalReplayer name key world error value nameEq keyEq
    selected registered protocol
    (appendTransitions (closedTransitions (locatedEpisode located))
      (traceAfterClosing located))
    (closedInside (locatedEpisode located))) ->
  SelectedEpisodeInteriorFold name key world error value nameEq keyEq selected
    registered (S episodeStartOrdinal) episodeStartLive
    (appendTransitions (closedTransitions (locatedEpisode located))
      (traceAfterClosing located))
    (closedInside (locatedEpisode located)) (locatedPreStart located)
scopedSelectedInteriorFoldFromPremises name key world error value protocol nameEq
  keyEq global aligned initialWellFormed selected located registered
  selectedOutside episodeStartOrdinal episodeStartLive beforeScan
  registeredDuring noRegistered local =
    selectedEpisodeInteriorFold protocol nameEq keyEq selected registered
      selectedOutside
      (appendTransitions (closedTransitions (locatedEpisode located))
        (traceAfterClosing located))
      (closedInside (locatedEpisode located)) local (S episodeStartOrdinal)
      episodeStartLive
      (generationTraceScanPreservesUnique nameEq beforeScan UniqueNil)
      (generationTraceScanPreservesStamped nameEq beforeScan
        emptyGenerationEnvironmentStamped)
      (closedInside (locatedEpisode located))
      (scopedAlignedLocatedInside name key world error value nameEq keyEq global
        aligned selected located)
      (closedInsideInstalled (locatedEpisode located))
      (scopedInsideNoRegistered name key world error value nameEq keyEq selected
        registered episodeStartOrdinal episodeStartLive (locatedEpisode located)
        (episodeNoRegistered
          (splitLocatedNoRegisteredSegments nameEq keyEq global selected located
            registered episodeStartOrdinal episodeStartLive beforeScan
            noRegistered)))
      (scopedSelectedInsideEmbedding name key world error value nameEq keyEq
        selected located)
      NoTransitions Refl (locatedPreStart located)
      (scopedInitialSelectedBoundary name key world error value nameEq keyEq
        global aligned initialWellFormed selected located registered
        episodeStartOrdinal episodeStartLive beforeScan registeredDuring)
      (scopedInitialCurrentInactive name key world error value nameEq registered
        episodeStartOrdinal episodeStartLive
        (generationScanPreservesBounded nameEq () (traceBeforeOpening located)
          beforeScan)
        (registeredDuringBirthLowerBound registeredDuring)
        (closedStartState (locatedEpisode located)))
      (scopedInitialCurrentEmpty name key world error value nameEq registered
        episodeStartOrdinal episodeStartLive
        (generationScanPreservesBounded nameEq () (traceBeforeOpening located)
          beforeScan)
        (registeredDuringBirthLowerBound registeredDuring)
        (closedStartState (locatedEpisode located)))
      (scopedInitialSelectedPlanEmpty name key world error value nameEq keyEq
        selected registered episodeStartOrdinal episodeStartLive
        (generationTraceScanPreservesUnique nameEq beforeScan UniqueNil)
        (generationScanPreservesBounded nameEq () (traceBeforeOpening located)
          beforeScan)
        (registeredDuringBirthLowerBound registeredDuring)
        (closedStartState (locatedEpisode located))
        (appendTransitions (closedTransitions (locatedEpisode located))
          (traceAfterClosing located))
        (locatedPreStart located)
        (scopedInitialSelectedBoundary name key world error value nameEq keyEq
          global aligned initialWellFormed selected located registered
          episodeStartOrdinal episodeStartLive beforeScan registeredDuring))

0 scopedAssembleSelectedClosedFold :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (selectedOutside :
    (generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  {preStart, afterClose, wholeLast :
    SystemState name key value world error} ->
  (episode : ClosedEpisode name key world error value nameEq keyEq selected
    preStart afterClose) ->
  (whole : Transitions (closedStartState episode) wholeLast) ->
  (interior : SelectedEpisodeInteriorFold name key world error value nameEq keyEq
    selected registered (S episodeStartOrdinal) episodeStartLive whole
    (closedInside episode) preStart) ->
  (finalUnique : GenerationEnvironmentNamesUnique (interiorFinalLive interior)) ->
  (finalStamped : GenerationEnvironmentStamped (interiorFinalLive interior)) ->
  (finalInactive : CurrentRegisteredInactiveFibers name key world error value
    nameEq registered (interiorFinalLive interior) (lastInstalledState episode)) ->
  (finalEmpty : CurrentRegisteredEmptyTables name key world error value nameEq
    registered (interiorFinalLive interior) (lastInstalledState episode)) ->
  (finalPlanEmpty : EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan
      (completePlanResult (selectedBoundaryPlan (interiorBoundary interior))))) ->
  SelectedClosedEpisodeFold name key world error value nameEq keyEq selected
    registered episodeStartOrdinal episodeStartLive episode whole
scopedAssembleSelectedClosedFold name key world error value nameEq keyEq selected
  registered selectedOutside episodeStartOrdinal episodeStartLive episode whole
  interior finalUnique finalStamped finalInactive finalEmpty finalPlanEmpty =
    MkSelectedClosedEpisodeFold (S (interiorFinalOrdinal interior))
      (interiorFinalLive interior) (interiorFinalSurvivor interior)
      (GenerationTraceScanStep (beginTransition (closedOpening episode))
        (closedTransitions episode)
        (scopedAppendGenerationScan name nameEq (S episodeStartOrdinal)
          episodeStartLive (closedInside episode)
          (MoreTransitions (unloadTransition (closing episode)) NoTransitions)
          (interiorFinalOrdinal interior) (interiorFinalLive interior)
          (S (interiorFinalOrdinal interior)) (interiorFinalLive interior)
          (interiorScan interior)
          (GenerationTraceScanStep (unloadTransition (closing episode))
            NoTransitions GenerationTraceScanEnd)))
      (ReplayReadyDelete
        (the (EpisodeGenerationDeletedActor nameEq selected registered
          episodeStartOrdinal episodeStartLive
          (the (Action name key value world error) (LBegin selected)))
          (DeleteEpisodeGenerationLifecycle Refl Refl))
        (appendedSelectedCloseReady
          (scopedAppendSelectedCloseReplay name key world error value nameEq
            keyEq selected registered (S episodeStartOrdinal) episodeStartLive
            (closedInside episode) preStart (interiorReady interior)
            (interiorFinalSurvivor interior) (interiorReadyEnds interior)
            (closing episode))))
      (ReplayEndsDelete
        (the (EpisodeGenerationDeletedActor nameEq selected registered
          episodeStartOrdinal episodeStartLive
          (the (Action name key value world error) (LBegin selected)))
          (DeleteEpisodeGenerationLifecycle Refl Refl))
        (appendedSelectedCloseReady
          (scopedAppendSelectedCloseReplay name key world error value nameEq
            keyEq selected registered (S episodeStartOrdinal) episodeStartLive
            (closedInside episode) preStart (interiorReady interior)
            (interiorFinalSurvivor interior) (interiorReadyEnds interior)
            (closing episode)))
        (appendedSelectedCloseEnds
          (scopedAppendSelectedCloseReplay name key world error value nameEq
            keyEq selected registered (S episodeStartOrdinal) episodeStartLive
            (closedInside episode) preStart (interiorReady interior)
            (interiorFinalSurvivor interior) (interiorReadyEnds interior)
            (closing episode))))
      finalUnique finalStamped
      (selectedUnloadClosesPostBoundary nameEq keyEq selected registered
        (interiorFinalOrdinal interior) (interiorFinalLive interior) finalUnique
        finalStamped selectedOutside whole (lastInstalledState episode)
        afterClose (interiorFinalSurvivor interior) (closing episode)
        (interiorBoundary interior) finalPlanEmpty finalInactive finalEmpty)

0 scopedSelectedClosedFoldFromInterior :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (aligned : AlignedTransitions name key world error value nameEq keyEq global) ->
  (selected : name) ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  (registered : List (RegistrationGeneration name)) ->
  (selectedOutside :
    (generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  (beforeScan : GenerationTraceScan nameEq 0 []
    (traceBeforeOpening located) episodeStartOrdinal episodeStartLive) ->
  (registeredDuring : RegisteredGenerationsDuring selected episodeStartOrdinal
    registered
    (MoreTransitions
      (beginTransition (closedOpening (locatedEpisode located)))
      (closedTransitions (locatedEpisode located)))) ->
  (noRegistered : NoRegisteredEpisode nameEq registered 0 [] global) ->
  (interior : SelectedEpisodeInteriorFold name key world error value nameEq keyEq
    selected registered (S episodeStartOrdinal) episodeStartLive
    (appendTransitions (closedTransitions (locatedEpisode located))
      (traceAfterClosing located))
    (closedInside (locatedEpisode located)) (locatedPreStart located)) ->
  SelectedClosedEpisodeFold name key world error value nameEq keyEq selected
    registered episodeStartOrdinal episodeStartLive (locatedEpisode located)
    (appendTransitions (closedTransitions (locatedEpisode located))
      (traceAfterClosing located))
scopedSelectedClosedFoldFromInterior name key world error value nameEq keyEq
  global aligned selected located registered selectedOutside episodeStartOrdinal
  episodeStartLive beforeScan registeredDuring noRegistered interior =
    scopedAssembleSelectedClosedFold name key world error value nameEq keyEq
      selected registered selectedOutside episodeStartOrdinal episodeStartLive
      (locatedEpisode located)
      (appendTransitions (closedTransitions (locatedEpisode located))
        (traceAfterClosing located))
      interior
      (generationTraceScanPreservesUnique nameEq (interiorScan interior)
        (generationTraceScanPreservesUnique nameEq beforeScan UniqueNil))
      (generationTraceScanPreservesStamped nameEq (interiorScan interior)
        (generationTraceScanPreservesStamped nameEq beforeScan
          emptyGenerationEnvironmentStamped))
      (currentRegisteredInactiveTrace nameEq keyEq registered
        (S episodeStartOrdinal) episodeStartLive
        (generationTraceScanPreservesUnique nameEq beforeScan UniqueNil)
        (closedInside (locatedEpisode located)) (interiorFinalOrdinal interior)
        (interiorFinalLive interior) (interiorScan interior)
        (scopedAlignedLocatedInside name key world error value nameEq keyEq global
          aligned selected located)
        (scopedInsideNoRegistered name key world error value nameEq keyEq selected
          registered episodeStartOrdinal episodeStartLive
          (locatedEpisode located)
          (episodeNoRegistered
            (splitLocatedNoRegisteredSegments nameEq keyEq global selected
              located registered episodeStartOrdinal episodeStartLive beforeScan
              noRegistered)))
        (scopedInitialCurrentInactive name key world error value nameEq registered
          episodeStartOrdinal episodeStartLive
          (generationScanPreservesBounded nameEq () (traceBeforeOpening located)
            beforeScan)
          (registeredDuringBirthLowerBound registeredDuring)
          (closedStartState (locatedEpisode located))))
      (currentRegisteredEmptyTableTrace nameEq keyEq registered
        (S episodeStartOrdinal) episodeStartLive
        (generationTraceScanPreservesUnique nameEq beforeScan UniqueNil)
        (closedInside (locatedEpisode located)) (interiorFinalOrdinal interior)
        (interiorFinalLive interior) (interiorScan interior)
        (scopedAlignedLocatedInside name key world error value nameEq keyEq global
          aligned selected located)
        (scopedInsideNoRegistered name key world error value nameEq keyEq selected
          registered episodeStartOrdinal episodeStartLive
          (locatedEpisode located)
          (episodeNoRegistered
            (splitLocatedNoRegisteredSegments nameEq keyEq global selected
              located registered episodeStartOrdinal episodeStartLive beforeScan
              noRegistered)))
        (scopedInitialCurrentInactive name key world error value nameEq registered
          episodeStartOrdinal episodeStartLive
          (generationScanPreservesBounded nameEq () (traceBeforeOpening located)
            beforeScan)
          (registeredDuringBirthLowerBound registeredDuring)
          (closedStartState (locatedEpisode located)))
        (scopedInitialCurrentEmpty name key world error value nameEq registered
          episodeStartOrdinal episodeStartLive
          (generationScanPreservesBounded nameEq () (traceBeforeOpening located)
            beforeScan)
          (registeredDuringBirthLowerBound registeredDuring)
          (closedStartState (locatedEpisode located))))
      (completeCurrentRegisteredPlanHasEmptyTables nameEq registered
        (interiorFinalLive interior)
        (generationTraceScanPreservesUnique nameEq (interiorScan interior)
          (generationTraceScanPreservesUnique nameEq beforeScan UniqueNil))
        (worldState (lastInstalledState (locatedEpisode located)))
        (registry (lastInstalledState (locatedEpisode located)))
        (selectedBoundaryPlan (interiorBoundary interior))
        (currentRegisteredEmptyTableTrace nameEq keyEq registered
          (S episodeStartOrdinal) episodeStartLive
          (generationTraceScanPreservesUnique nameEq beforeScan UniqueNil)
          (closedInside (locatedEpisode located)) (interiorFinalOrdinal interior)
          (interiorFinalLive interior) (interiorScan interior)
          (scopedAlignedLocatedInside name key world error value nameEq keyEq
            global aligned selected located)
          (scopedInsideNoRegistered name key world error value nameEq keyEq
            selected registered episodeStartOrdinal episodeStartLive
            (locatedEpisode located)
            (episodeNoRegistered
              (splitLocatedNoRegisteredSegments nameEq keyEq global selected
                located registered episodeStartOrdinal episodeStartLive
                beforeScan noRegistered)))
          (scopedInitialCurrentInactive name key world error value nameEq
            registered episodeStartOrdinal episodeStartLive
            (generationScanPreservesBounded nameEq ()
              (traceBeforeOpening located) beforeScan)
            (registeredDuringBirthLowerBound registeredDuring)
            (closedStartState (locatedEpisode located)))
          (scopedInitialCurrentEmpty name key world error value nameEq registered
            episodeStartOrdinal episodeStartLive
            (generationScanPreservesBounded nameEq ()
              (traceBeforeOpening located) beforeScan)
            (registeredDuringBirthLowerBound registeredDuring)
            (closedStartState (locatedEpisode located)))))

0 scopedLifecycleOccursInClosedPrefix :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, finalState, before, afterState :
    SystemState name key value world error} ->
  {global : Transitions initial finalState} ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (insidePrefix : Transitions
    (closedStartState (locatedEpisode located)) before) ->
  (rest : Transitions afterState
    (lastInstalledState (locatedEpisode located))) ->
  (insideDecomposition : appendTransitions insidePrefix
    (MoreTransitions
      (Fired {before = before} {afterState = afterState}
        nameEq keyEq action tag checked) rest) =
      closedInside (locatedEpisode located)) ->
  OccursIn
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked)
    (appendTransitions (traceBeforeOpening located)
      (MoreTransitions
        (beginTransition (closedOpening (locatedEpisode located)))
        (closedTransitions (locatedEpisode located))))
scopedLifecycleOccursInClosedPrefix name key world error value nameEq keyEq
  selected located action tag checked insidePrefix rest insideDecomposition =
    appendRightOccursScoped (traceBeforeOpening located)
      (MoreTransitions
        (beginTransition (closedOpening (locatedEpisode located)))
        (closedTransitions (locatedEpisode located)))
      (OccursLater
        (appendLeftOccursScoped (closedInside (locatedEpisode located))
          (MoreTransitions
            (unloadTransition (closing (locatedEpisode located))) NoTransitions)
          (transportOccursScoped insideDecomposition
            (appendRightOccursScoped insidePrefix
              (MoreTransitions
                (Fired {before = before} {afterState = afterState}
                  nameEq keyEq action tag checked)
                rest)
              OccursHere))))

0 scopedClosedPrefixDecomposition :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, finalState : SystemState name key value world error} ->
  {global : Transitions initial finalState} ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  appendTransitions
    (appendTransitions (traceBeforeOpening located)
      (MoreTransitions
        (beginTransition (closedOpening (locatedEpisode located)))
        (closedTransitions (locatedEpisode located))))
    (traceAfterClosing located) = global
scopedClosedPrefixDecomposition name key world error value nameEq keyEq selected
  located =
    trans
      (appendTransitionsAssociative (traceBeforeOpening located)
        (MoreTransitions
          (beginTransition (closedOpening (locatedEpisode located)))
          (closedTransitions (locatedEpisode located)))
        (traceAfterClosing located))
      (locatedDecomposition located)

0 scopedAlignedClosedPrefix :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (aligned : AlignedTransitions name key world error value nameEq keyEq global) ->
  (selected : name) ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  AlignedTransitions name key world error value nameEq keyEq
    (appendTransitions (traceBeforeOpening located)
      (MoreTransitions
        (beginTransition (closedOpening (locatedEpisode located)))
        (closedTransitions (locatedEpisode located))))
scopedAlignedClosedPrefix name key world error value nameEq keyEq global aligned
  selected located =
    fst
      (alignedAppendSplit
        (appendTransitions (traceBeforeOpening located)
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode located)))
            (closedTransitions (locatedEpisode located))))
        (traceAfterClosing located)
        (rewrite
          (scopedClosedPrefixDecomposition name key world error value nameEq
            keyEq selected located)
          in aligned))

0 scopedSelectedAfterCloseUninstalled :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {preStart, afterClose : SystemState name key value world error} ->
  (episode : ClosedEpisode name key world error value nameEq keyEq selected
    preStart afterClose) ->
  installedAt @{nameEq} selected afterClose = False
scopedSelectedAfterCloseUninstalled name key world error value nameEq keyEq
  selected episode =
    case lUnloadBoundary nameEq keyEq selected (lastInstalledState episode)
      afterClose LUnloadTag
      (checkedActionProjects nameEq keyEq (LUnload selected)
        (lastInstalledState episode) afterClose LUnloadTag
        (unloadEquation (closing episode))) of
      (tagShape, sourceTrue, targetFalse) => targetFalse

0 scopedExtendFirstClosing :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  FirstClosingResult name key world error value nameEq keyEq actor left ->
  FirstClosingResult name key world error value nameEq keyEq actor
    (appendTransitions left right)
scopedExtendFirstClosing name key world error value nameEq keyEq actor left right
  (MkFirstClosingResult closeBefore closeAfter beforeClosing installedBefore
    closing afterClosing decomposition) =
      MkFirstClosingResult closeBefore closeAfter beforeClosing installedBefore
        closing (appendTransitions afterClosing right)
        (trans
          (sym
            (appendTransitionsAssociative beforeClosing
              (MoreTransitions (unloadTransition closing) afterClosing) right))
          (cong (\trace => appendTransitions trace right) decomposition))

0 scopedLifecycleNonBeginSourceInstalled :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (lifecycle : isLifecycleAction action = True) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (notBegin : Not (action = LBegin (actionOwner action))) ->
  installedAt @{nameEq} (actionOwner action) before = True
scopedLifecycleNonBeginSourceInstalled name key world error value nameEq keyEq
  (OInsert actor parent component) Refl before afterState tag checked notBegin
    impossible
scopedLifecycleNonBeginSourceInstalled name key world error value nameEq keyEq
  (ORetire actor) Refl before afterState tag checked notBegin impossible
scopedLifecycleNonBeginSourceInstalled name key world error value nameEq keyEq
  (ORemove actor) Refl before afterState tag checked notBegin impossible
scopedLifecycleNonBeginSourceInstalled name key world error value nameEq keyEq
  (LBegin actor) lifecycle before afterState tag checked notBegin =
    void (notBegin Refl)
scopedLifecycleNonBeginSourceInstalled name key world error value nameEq keyEq
  (LAdvance actor) lifecycle before afterState tag checked notBegin =
    lAdvanceStartsInstalled nameEq keyEq actor before afterState tag
      (checkedActionProjects nameEq keyEq (LAdvance actor) before afterState tag
        checked)
scopedLifecycleNonBeginSourceInstalled name key world error value nameEq keyEq
  (LDivert actor) lifecycle before afterState tag checked notBegin =
    fst
      (lDivertInstalled nameEq keyEq actor before afterState
        (replace
          {p = \observed => applyAction @{nameEq} @{keyEq} (LDivert actor)
            before = Just (observed, afterState)}
          (successfulLDivertTag nameEq keyEq actor before afterState tag
            (checkedActionProjects nameEq keyEq (LDivert actor) before
              afterState tag checked))
          (checkedActionProjects nameEq keyEq (LDivert actor) before afterState
            tag checked)))
scopedLifecycleNonBeginSourceInstalled name key world error value nameEq keyEq
  (LLeave actor) lifecycle before afterState tag checked notBegin =
    fst
      (lLeaveInstalled nameEq keyEq actor before afterState tag
        (checkedActionProjects nameEq keyEq (LLeave actor) before afterState tag
          checked))
scopedLifecycleNonBeginSourceInstalled name key world error value nameEq keyEq
  (LUnload actor) lifecycle before afterState tag checked notBegin =
    fst
      (snd
        (lUnloadBoundary nameEq keyEq actor before afterState tag
          (checkedActionProjects nameEq keyEq (LUnload actor) before afterState
            tag checked)))

||| O9 is the separately gateable enriched Lemma-72 adapter.  Its explicit
||| dependency premise is scoped to the selected registration generation and
||| activation interval; the refuted raw-name-global predicate is not accepted.
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
  (0 noDependent : NoDependentClosingEpisodeForGeneration
    {nameEq = nameEq} {keyEq = keyEq} {global = trace}
    (selectedActor candidate) (selectedStartOrdinal candidate)
    (selectedStartLive candidate) (selectedEpisode candidate)) ->
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

||| Private decision procedure used only to make reflexivity constructive.
||| Root O-Retire/O-Remove classification is state-sensitive, so action shape
||| alone is insufficient.
0 localLifecycleCannotBeRoot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  (transition : Transition before afterState) ->
  isLifecycleAction (transitionAction transition) = True ->
  RootOrchestrationStep nameEq transition -> Void
localLifecycleCannotBeRoot nameEq transition lifecycle (RootInsertStep action) =
  case trans (sym (cong isLifecycleAction action)) lifecycle of Refl impossible
localLifecycleCannotBeRoot nameEq transition lifecycle
  (RootRetireStep fiber found parent action) =
    case trans (sym (cong isLifecycleAction action)) lifecycle of Refl impossible
localLifecycleCannotBeRoot nameEq transition lifecycle
  (RootRemoveStep fiber found parent action) =
    case trans (sym (cong isLifecycleAction action)) lifecycle of Refl impossible

0 localChildInsertCannotBeRoot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  {child, parent : name} ->
  {component : Component key value world error} ->
  (nameEq : DecEq name) ->
  (transition : Transition before afterState) ->
  transitionAction transition = OInsert child (ChildOf parent) component ->
  RootOrchestrationStep nameEq transition -> Void
localChildInsertCannotBeRoot nameEq transition childAction (RootInsertStep rootAction) =
  case trans (sym childAction) rootAction of Refl impossible
localChildInsertCannotBeRoot nameEq transition childAction
  (RootRetireStep fiber found parent rootAction) =
    case trans (sym childAction) rootAction of Refl impossible
localChildInsertCannotBeRoot nameEq transition childAction
  (RootRemoveStep fiber found parent rootAction) =
    case trans (sym childAction) rootAction of Refl impossible

0 localMissingRetireCannotBeRoot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  {child : name} ->
  (nameEq : DecEq name) ->
  (transition : Transition before afterState) ->
  transitionAction transition = ORetire child ->
  lookupFiber @{nameEq} child (registry before) =
    the (Maybe (Fiber name key value world error)) Nothing ->
  RootOrchestrationStep nameEq transition -> Void
localMissingRetireCannotBeRoot nameEq transition childAction missing
  (RootInsertStep rootAction) =
    case trans (sym childAction) rootAction of Refl impossible
localMissingRetireCannotBeRoot nameEq transition childAction missing
  (RootRetireStep rootFiber rootFound rootParent rootAction) =
    case trans (sym childAction) rootAction of
      Refl => case trans (sym missing) rootFound of Refl impossible
localMissingRetireCannotBeRoot nameEq transition childAction missing
  (RootRemoveStep rootFiber rootFound rootParent rootAction) =
    case trans (sym childAction) rootAction of Refl impossible

0 localChildRetireCannotBeRoot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  {child, parent : name} ->
  (nameEq : DecEq name) ->
  (transition : Transition before afterState) ->
  transitionAction transition = ORetire child ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} child (registry before) = Just fiber ->
  fiberParent fiber = ChildOf parent ->
  RootOrchestrationStep nameEq transition -> Void
localChildRetireCannotBeRoot nameEq transition childAction fiber childFound
  childParent (RootInsertStep rootAction) =
    case trans (sym childAction) rootAction of Refl impossible
localChildRetireCannotBeRoot nameEq transition childAction fiber childFound
  childParent (RootRetireStep rootFiber rootFound rootParent rootAction) =
    case trans (sym childAction) rootAction of
      Refl =>
        let sameFiber = justInjective (trans (sym childFound) rootFound)
            roleConflict : (ChildOf parent = Root)
            roleConflict = trans (sym childParent)
              (trans (cong fiberParent sameFiber) rootParent)
        in case roleConflict of Refl impossible
localChildRetireCannotBeRoot nameEq transition childAction fiber childFound
  childParent (RootRemoveStep rootFiber rootFound rootParent rootAction) =
    case trans (sym childAction) rootAction of Refl impossible

0 localMissingRemoveCannotBeRoot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  {child : name} ->
  (nameEq : DecEq name) ->
  (transition : Transition before afterState) ->
  transitionAction transition = ORemove child ->
  lookupFiber @{nameEq} child (registry before) =
    the (Maybe (Fiber name key value world error)) Nothing ->
  RootOrchestrationStep nameEq transition -> Void
localMissingRemoveCannotBeRoot nameEq transition childAction missing
  (RootInsertStep rootAction) =
    case trans (sym childAction) rootAction of Refl impossible
localMissingRemoveCannotBeRoot nameEq transition childAction missing
  (RootRetireStep rootFiber rootFound rootParent rootAction) =
    case trans (sym childAction) rootAction of Refl impossible
localMissingRemoveCannotBeRoot nameEq transition childAction missing
  (RootRemoveStep rootFiber rootFound rootParent rootAction) =
    case trans (sym childAction) rootAction of
      Refl => case trans (sym missing) rootFound of Refl impossible

0 localChildRemoveCannotBeRoot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  {child, parent : name} ->
  (nameEq : DecEq name) ->
  (transition : Transition before afterState) ->
  transitionAction transition = ORemove child ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} child (registry before) = Just fiber ->
  fiberParent fiber = ChildOf parent ->
  RootOrchestrationStep nameEq transition -> Void
localChildRemoveCannotBeRoot nameEq transition childAction fiber childFound
  childParent (RootInsertStep rootAction) =
    case trans (sym childAction) rootAction of Refl impossible
localChildRemoveCannotBeRoot nameEq transition childAction fiber childFound
  childParent (RootRetireStep rootFiber rootFound rootParent rootAction) =
    case trans (sym childAction) rootAction of Refl impossible
localChildRemoveCannotBeRoot nameEq transition childAction fiber childFound
  childParent (RootRemoveStep rootFiber rootFound rootParent rootAction) =
    case trans (sym childAction) rootAction of
      Refl =>
        let sameFiber = justInjective (trans (sym childFound) rootFound)
            roleConflict : (ChildOf parent = Root)
            roleConflict = trans (sym childParent)
              (trans (cong fiberParent sameFiber) rootParent)
        in case roleConflict of Refl impossible

0 decideRetireRoot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  {child : name} ->
  (nameEq : DecEq name) ->
  (transition : Transition before afterState) ->
  transitionAction transition = ORetire child ->
  Dec (RootOrchestrationStep nameEq transition)
decideRetireRoot {before = MkSystemState ambient fibers} nameEq transition action
  with (lookupFiber @{nameEq} child fibers) proof found
  decideRetireRoot nameEq transition action | Nothing =
    No (localMissingRetireCannotBeRoot nameEq transition action found)
  decideRetireRoot nameEq transition action | Just fiber
    with (fiberParent fiber) proof parent
    decideRetireRoot nameEq transition action | Just fiber | Root =
      Yes (RootRetireStep fiber found parent action)
    decideRetireRoot nameEq transition action | Just fiber | ChildOf owner =
      No (localChildRetireCannotBeRoot nameEq transition action fiber found
        parent)

0 decideRemoveRoot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  {child : name} ->
  (nameEq : DecEq name) ->
  (transition : Transition before afterState) ->
  transitionAction transition = ORemove child ->
  Dec (RootOrchestrationStep nameEq transition)
decideRemoveRoot {before = MkSystemState ambient fibers} nameEq transition action
  with (lookupFiber @{nameEq} child fibers) proof found
  decideRemoveRoot nameEq transition action | Nothing =
    No (localMissingRemoveCannotBeRoot nameEq transition action found)
  decideRemoveRoot nameEq transition action | Just fiber
    with (fiberParent fiber) proof parent
    decideRemoveRoot nameEq transition action | Just fiber | Root =
      Yes (RootRemoveStep fiber found parent action)
    decideRemoveRoot nameEq transition action | Just fiber | ChildOf owner =
      No (localChildRemoveCannotBeRoot nameEq transition action fiber found
        parent)

0 rootOrchestrationDecision :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  (transition : Transition before afterState) ->
  Dec (RootOrchestrationStep nameEq transition)
rootOrchestrationDecision nameEq transition@(Fired _ _
  (OInsert child Root component) tag fires) =
    Yes (RootInsertStep Refl)
rootOrchestrationDecision nameEq transition@(Fired _ _
  (OInsert child (ChildOf parent) component) tag fires) =
    No (localChildInsertCannotBeRoot nameEq transition Refl)
rootOrchestrationDecision nameEq
  transition@(Fired _ _ (ORetire child) tag fires) =
    decideRetireRoot nameEq transition Refl
rootOrchestrationDecision nameEq
  transition@(Fired _ _ (ORemove child) tag fires) =
    decideRemoveRoot nameEq transition Refl
rootOrchestrationDecision nameEq transition@(Fired _ _ (LBegin actor) tag fires) =
  No (localLifecycleCannotBeRoot nameEq transition Refl)
rootOrchestrationDecision nameEq transition@(Fired _ _ (LAdvance actor) tag fires) =
  No (localLifecycleCannotBeRoot nameEq transition Refl)
rootOrchestrationDecision nameEq transition@(Fired _ _ (LDivert actor) tag fires) =
  No (localLifecycleCannotBeRoot nameEq transition Refl)
rootOrchestrationDecision nameEq transition@(Fired _ _ (LLeave actor) tag fires) =
  No (localLifecycleCannotBeRoot nameEq transition Refl)
rootOrchestrationDecision nameEq transition@(Fired _ _ (LUnload actor) tag fires) =
  No (localLifecycleCannotBeRoot nameEq transition Refl)

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
sameExternalOrchestrationReflexiveSpike nameEq NoTransitions =
  SameExternalOrchestrationEnd
sameExternalOrchestrationReflexiveSpike nameEq
  (MoreTransitions transition rest) with
    (rootOrchestrationDecision nameEq transition)
  sameExternalOrchestrationReflexiveSpike nameEq
    (MoreTransitions transition rest) | Yes external =
      MatchExternalInput (transitionAction transition) transition rest external
        transition rest external Refl Refl
        (sameExternalOrchestrationReflexiveSpike nameEq rest)
  sameExternalOrchestrationReflexiveSpike nameEq
    (MoreTransitions transition rest) | No internal =
      SkipLeftInternal transition rest internal
        (SkipRightInternal transition rest internal
          (sameExternalOrchestrationReflexiveSpike nameEq rest))

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
sameExternalOrchestrationTransitiveSpike nameEq first second =
  compose first second
  where
  0 compose :
    SameExternalOrchestration {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq leftTrace middleTrace ->
    SameExternalOrchestration {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq middleTrace rightTrace ->
    SameExternalOrchestration {name = name} {key = key} {world = world}
      {error = error} {value = value} nameEq leftTrace rightTrace
  compose SameExternalOrchestrationEnd SameExternalOrchestrationEnd =
    SameExternalOrchestrationEnd
  compose (SkipLeftInternal transition rest internal remaining) rightRelation =
    SkipLeftInternal transition rest internal (compose remaining rightRelation)
  compose leftRelation
    (SkipRightInternal transition rest internal remaining) =
      SkipRightInternal transition rest internal (compose leftRelation remaining)
  compose (SkipRightInternal transition rest internal remaining)
    (SkipLeftInternal transition rest alsoInternal rightRelation) =
      compose remaining rightRelation
  compose (SkipRightInternal transition rest internal remaining)
    (MatchExternalInput action transition rest external rightTransition rightRest
      rightExternal transitionAction rightAction rightRelation) =
        void (internal external)
  compose
    (MatchExternalInput action leftTransition leftRest leftExternal
      middleTransition middleRest middleExternal leftAction middleAction
      leftRelation)
    (SkipLeftInternal middleTransition middleRest internal rightRelation) =
      void (internal middleExternal)
  compose
    (MatchExternalInput action leftTransition leftRest leftExternal
      middleTransition middleRest middleExternal leftAction middleAction
      leftRelation)
    (MatchExternalInput rightActionName middleTransition middleRest
      secondMiddleExternal rightTransition rightRest rightExternal
      secondMiddleAction rightAction rightRelation) =
        MatchExternalInput action leftTransition leftRest leftExternal
          rightTransition rightRest rightExternal leftAction
          (trans rightAction (trans (sym secondMiddleAction) middleAction))
          (compose leftRelation rightRelation)

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
traceIndependentAfterDeletionReplaySpike {keyEq} result correspondence
  independent =
    traceIndependentAfterRelationalReplaySpike keyEq correspondence independent

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
        trace (replayAligned (chainReplayCapital premises)) in
    case selectMaximalClosingEpisodeSpike nameEq keyEq protocol initial finalState
      trace premises scan of
      NoMaximalClosingEpisode empty =>
        ClosingFree (emptyScanIsClosingFree scan empty)
      SelectedMaximalClosingEpisode candidate selected =>
        HasClosingStep candidate
          (enrichDeletionChainStepSpike nameEq keyEq protocol trace premises
            candidate (selectedNoDependentClose candidate))

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

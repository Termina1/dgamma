module DGamma.CP5ConfluenceDeletionChainSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionTheorem
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorClassify
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorTrace
import DGamma.CP4ParentSafety
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
  scopedSelectedGeneration : RegistrationGeneration name
  0 scopedSelectedCurrent : lookupCurrentGeneration @{nameEq} selected
    selectedStartLive = Just scopedSelectedGeneration
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

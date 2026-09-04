module DGamma.CP5ConfluenceDeletionChainSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionTheorem
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorClassify
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorTrace
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

module DGamma.CP5O20GlobalActivationHistorySpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20ActivationPositionStepSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Every ordinary native index advance preserves ALL activation counters.
||| Begin changes the live activation key but not accumulated position counts;
||| Unload/Remove likewise retain counts indexed by their HISTORICAL keys.
export
0 o20OrdinaryIndexKeepsActivationCounts :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (action : Action name key value world error) -> (index : RegistrationIndexState name) ->
  (indexedSurvivingChildCounts (advanceRegistrationIndex @{nameEq} ordinal action index) =
    indexedSurvivingChildCounts index)
o20OrdinaryIndexKeepsActivationCounts nameEq ordinal (OInsert actor Root component)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20OrdinaryIndexKeepsActivationCounts nameEq ordinal (OInsert actor (ChildOf parent) component)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20OrdinaryIndexKeepsActivationCounts nameEq ordinal (ORetire actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20OrdinaryIndexKeepsActivationCounts nameEq ordinal (ORemove actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20OrdinaryIndexKeepsActivationCounts nameEq ordinal (LBegin actor)
  (MkRegistrationIndexState live activations counts deleted) =
    case the (found : Maybe (RegistrationGeneration name) **
      (lookupCurrentGeneration @{nameEq} actor live = found))
      (lookupCurrentGeneration @{nameEq} actor live ** Refl) of
      (Nothing ** exact) => rewrite exact in Refl
      (Just generation ** exact) => rewrite exact in Refl
o20OrdinaryIndexKeepsActivationCounts nameEq ordinal (LAdvance actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20OrdinaryIndexKeepsActivationCounts nameEq ordinal (LDivert actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20OrdinaryIndexKeepsActivationCounts nameEq ordinal (LLeave actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20OrdinaryIndexKeepsActivationCounts nameEq ordinal (LUnload actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl

||| Exact unilateral native scan WITH its chronological retained-event word.
||| Every source edge is explicit. Deleted births retain the actual later
||| closing certificate and consume no event position. This is a derived
||| projection type, not a new premise/field on any accepted canonical capital.
||| The corresponding frozen side-scan is private and has no event-word index.
public export
data O20NativeActivationScan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (ordinal : Nat) -> (index : RegistrationIndexState name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> (finalIndex : RegistrationIndexState name) ->
  List (RegistrationEvent name key world error value) -> Type where
  O20ActivationScanEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {ordinal : Nat} -> {index : RegistrationIndexState name} ->
    {state : SystemState name key value world error} ->
    O20NativeActivationScan nameEq ordinal index (the (Transitions state state) NoTransitions) index []
  O20ActivationScanOrdinary :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {ordinal : Nat} -> {index, finalIndex : RegistrationIndexState name} ->
    {first, middle, finalState : SystemState name key value world error} ->
    {events : List (RegistrationEvent name key world error value)} ->
    (action : Action name key value world error) -> (edge : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    (0 shape : (transitionAction edge = action)) ->
    (0 ordinary : (isGeneratedRegistrationAction action = False)) ->
    (0 later : O20NativeActivationScan nameEq (S ordinal)
      (advanceRegistrationIndex @{nameEq} ordinal action index) rest finalIndex events) ->
    O20NativeActivationScan nameEq ordinal index (MoreTransitions edge rest) finalIndex events
  O20ActivationScanDeleted :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {ordinal : Nat} -> {index, finalIndex : RegistrationIndexState name} ->
    {first, middle, finalState : SystemState name key value world error} ->
    {events : List (RegistrationEvent name key world error value)} ->
    {child, parent : name} -> {component : Component key value world error} ->
    (edge : Transition first middle) -> (rest : Transitions middle finalState) ->
    (0 shape : (transitionAction edge = OInsert child (ChildOf parent) component)) ->
    (0 deleted : DeletedClosingRegistration
      (registrationEventAt @{nameEq} ordinal index child parent component) rest) ->
    (0 later : O20NativeActivationScan nameEq (S ordinal)
      (advanceDeletedRegistrationIndex @{nameEq} ordinal child parent component index) rest finalIndex events) ->
    O20NativeActivationScan nameEq ordinal index (MoreTransitions edge rest) finalIndex events
  O20ActivationScanRetained :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {ordinal : Nat} -> {index, finalIndex : RegistrationIndexState name} ->
    {first, middle, finalState : SystemState name key value world error} ->
    {events : List (RegistrationEvent name key world error value)} ->
    {child, parent : name} -> {component : Component key value world error} ->
    (edge : Transition first middle) -> (rest : Transitions middle finalState) ->
    (0 shape : (transitionAction edge = OInsert child (ChildOf parent) component)) ->
    (0 retained : SurvivingRegistration
      (registrationEventAt @{nameEq} ordinal index child parent component) rest) ->
    (0 later : O20NativeActivationScan nameEq (S ordinal)
      (advanceSurvivingRegistrationIndex @{nameEq} ordinal child parent component index) rest finalIndex events) ->
    O20NativeActivationScan nameEq ordinal index (MoreTransitions edge rest) finalIndex
      (registrationEventAt @{nameEq} ordinal index child parent component :: events)

||| PRODUCE the complete left native event history from the actual accepted
||| asynchronous correspondence. No history, target position, prefix cut or
||| event equality is supplied. Both queue/matching directions and each real
||| deleted birth are traversed, retaining exact physical source coordinates.
public export
0 o20LeftNativeActivationHistory :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {mapping : RegistrationGenerationBijection name} ->
  {leftOrdinal, rightOrdinal : Nat} ->
  {leftIndex, rightIndex, leftFinalIndex, rightFinalIndex : RegistrationIndexState name} ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  {pendingLeft, pendingRight : List (RegistrationEvent name key world error value)} ->
  RegistrationTraceCorrespondence nameEq mapping leftOrdinal leftIndex left leftFinalIndex
    rightOrdinal rightIndex right rightFinalIndex pendingLeft pendingRight ->
  (events : List (RegistrationEvent name key world error value) **
    O20NativeActivationScan nameEq leftOrdinal leftIndex left leftFinalIndex events)
o20LeftNativeActivationHistory RegistrationCorrespondenceEnd = ([] ** O20ActivationScanEnd)
o20LeftNativeActivationHistory (SkipLeftNonRegistration action edge rest shape ordinary later) =
  case o20LeftNativeActivationHistory later of
    (events ** scan) => (events ** O20ActivationScanOrdinary action edge rest shape ordinary scan)
o20LeftNativeActivationHistory (DiscardLeftDeletedRegistration edge rest shape deleted later) =
  case o20LeftNativeActivationHistory later of
    (events ** scan) => (events ** O20ActivationScanDeleted edge rest shape deleted scan)
o20LeftNativeActivationHistory {nameEq} {leftOrdinal} {leftIndex}
  (QueueLeftGeneratedRegistration {child} {parent} {component} edge rest shape retained later) =
    case o20LeftNativeActivationHistory later of
      (events ** scan) => (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent component :: events **
        O20ActivationScanRetained edge rest shape retained scan)
o20LeftNativeActivationHistory {nameEq} {leftOrdinal} {leftIndex}
  (MatchLeftWithPendingRight {child} {parent} {component} edge rest shape retained earlierEvents event laterEvents matched later) =
    case o20LeftNativeActivationHistory later of
      (events ** scan) => (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent component :: events **
        O20ActivationScanRetained edge rest shape retained scan)
o20LeftNativeActivationHistory (SkipRightNonRegistration action edge rest shape ordinary later) =
  o20LeftNativeActivationHistory later
o20LeftNativeActivationHistory (DiscardRightDeletedRegistration edge rest shape deleted later) =
  o20LeftNativeActivationHistory later
o20LeftNativeActivationHistory (QueueRightGeneratedRegistration edge rest shape retained later) =
  o20LeftNativeActivationHistory later
o20LeftNativeActivationHistory (MatchRightWithPendingLeft edge rest shape retained earlierEvents event laterEvents matched later) =
  o20LeftNativeActivationHistory later

||| Executable replay of ONLY retained activation events. The historical
||| generation-and-Begin key, not the raw parent or global edge ordinal,
||| selects each counter. Ordinary/deleted source edges are absent from this
||| word because the native scanner authenticates them separately.
public export
o20ReplayRetainedEventCounts :
  {0 name, key, world, error : Type} -> {0 value : key -> Type} ->
  (nameEq : DecEq name) -> List (RegistrationEvent name key world error value) ->
  List (RegistrationActivation name, Nat) -> List (RegistrationActivation name, Nat)
o20ReplayRetainedEventCounts nameEq [] counts = counts
o20ReplayRetainedEventCounts nameEq (event :: later) counts =
  case eventParentActivation event of
    Nothing => o20ReplayRetainedEventCounts nameEq later counts
    Just activation => o20ReplayRetainedEventCounts nameEq later
      (incrementChildrenBornInActivation @{nameEq} activation counts)

||| GLOBAL counter equation for the complete native classified word. This
||| turns R202's local updates into a whole-history induction. Each discarded
||| birth contributes zero; each actual retained birth contributes one update
||| at its observed activation. No target counter or chronological equality is
||| assumed. Transport between exchanged canonical words remains separate.
export
0 o20NativeActivationCounts :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (ordinal : Nat) -> (index : RegistrationIndexState name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> (finalIndex : RegistrationIndexState name) ->
  (events : List (RegistrationEvent name key world error value)) ->
  O20NativeActivationScan nameEq ordinal index trace finalIndex events ->
  (indexedSurvivingChildCounts finalIndex =
    o20ReplayRetainedEventCounts nameEq events (indexedSurvivingChildCounts index))
o20NativeActivationCounts nameEq ordinal (MkRegistrationIndexState live activations counts deleted)
  trace finalIndex events scan = case scan of
    O20ActivationScanEnd => Refl
    O20ActivationScanOrdinary action edge rest shape ordinary later =>
      trans (o20NativeActivationCounts nameEq (S ordinal) (advanceRegistrationIndex @{nameEq} ordinal action (MkRegistrationIndexState live activations counts deleted))
        rest finalIndex events later)
        (cong (o20ReplayRetainedEventCounts nameEq events)
          (o20OrdinaryIndexKeepsActivationCounts nameEq ordinal action (MkRegistrationIndexState live activations counts deleted)))
    O20ActivationScanDeleted {child} {parent} {component} edge rest shape discarded later =>
      trans (o20NativeActivationCounts nameEq (S ordinal) (advanceDeletedRegistrationIndex @{nameEq} ordinal child parent component (MkRegistrationIndexState live activations counts deleted))
        rest finalIndex events later)
        (cong (o20ReplayRetainedEventCounts nameEq events)
          (snd (o20DeletedBirthKeepsActivationPosition nameEq ordinal child parent component (MkRegistrationIndexState live activations counts deleted))))
    O20ActivationScanRetained {child} {parent} {component} {events = laterEvents} edge rest shape retained later =>
      rewrite survivingActivationPresent retained in
        trans (o20NativeActivationCounts nameEq (S ordinal) (advanceSurvivingRegistrationIndex @{nameEq} ordinal child parent component (MkRegistrationIndexState live activations counts deleted))
          rest finalIndex laterEvents later)
          (cong (o20ReplayRetainedEventCounts nameEq laterEvents)
            (snd (o20SurvivingBirthActivationUpdate nameEq ordinal child parent component (MkRegistrationIndexState live activations counts deleted)
              (survivingActivation retained) (survivingActivationPresent retained))))

||| ALL chronological event positions, not only the final count. At each
||| retained event, its position is read from the counter produced by every
||| earlier retained event. The next event sees exactly one additional update.
public export
0 o20ChronologicalPositions :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> List (RegistrationEvent name key world error value) ->
  List (RegistrationActivation name, Nat) -> Type
o20ChronologicalPositions nameEq [] counts = ()
o20ChronologicalPositions nameEq (event :: later) counts =
  case eventParentActivation event of
    Nothing => (eventChildPosition event = Z, o20ChronologicalPositions nameEq later counts)
    Just activation =>
      (eventChildPosition event = childrenBornInActivation @{nameEq} activation counts,
       o20ChronologicalPositions nameEq later (incrementChildrenBornInActivation @{nameEq} activation counts))

||| PRODUCE all prefix-position equations by induction on the full native
||| scanner. Native deleted births and ordinary edges preserve the running
||| counts; the retained case authenticates its own source activation and
||| increments it. No prefix position, final position or target index is input.
export
0 o20NativeChronologicalPositions :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (ordinal : Nat) -> (index : RegistrationIndexState name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> (finalIndex : RegistrationIndexState name) ->
  (events : List (RegistrationEvent name key world error value)) ->
  O20NativeActivationScan nameEq ordinal index trace finalIndex events ->
  o20ChronologicalPositions nameEq events (indexedSurvivingChildCounts index)
o20NativeChronologicalPositions nameEq ordinal (MkRegistrationIndexState live activations counts deleted)
  trace finalIndex events scan = case scan of
    O20ActivationScanEnd => ()
    O20ActivationScanOrdinary action edge rest shape ordinary later =>
      replace {p = o20ChronologicalPositions nameEq events}
        (o20OrdinaryIndexKeepsActivationCounts nameEq ordinal action (MkRegistrationIndexState live activations counts deleted))
        (o20NativeChronologicalPositions nameEq (S ordinal)
          (advanceRegistrationIndex @{nameEq} ordinal action (MkRegistrationIndexState live activations counts deleted))
          rest finalIndex events later)
    O20ActivationScanDeleted {child} {parent} {component} edge rest shape discarded later =>
      replace {p = o20ChronologicalPositions nameEq events}
        (snd (o20DeletedBirthKeepsActivationPosition nameEq ordinal child parent component (MkRegistrationIndexState live activations counts deleted)))
        (o20NativeChronologicalPositions nameEq (S ordinal)
          (advanceDeletedRegistrationIndex @{nameEq} ordinal child parent component (MkRegistrationIndexState live activations counts deleted))
          rest finalIndex events later)
    O20ActivationScanRetained {child} {parent} {component} {events = laterEvents} edge rest shape retained later =>
      rewrite survivingActivationPresent retained in
        (Refl, replace {p = o20ChronologicalPositions nameEq laterEvents}
          (snd (o20SurvivingBirthActivationUpdate nameEq ordinal child parent component
            (MkRegistrationIndexState live activations counts deleted) (survivingActivation retained)
            (survivingActivationPresent retained)))
          (o20NativeChronologicalPositions nameEq (S ordinal)
            (advanceSurvivingRegistrationIndex @{nameEq} ordinal child parent component (MkRegistrationIndexState live activations counts deleted))
            rest finalIndex laterEvents later))

||| PRODUCE BOTH original native activation histories, every prefix position,
||| and both complete counter equations from one actual accepted bilateral
||| scanner. There are no supplied histories or counter/position equations.
||| These are registration scanner histories, NOT paired runtime occurrence
||| stages, and NOT transport through deletion/sorting or an ALL-name cut.
public export
0 o20AcceptedActivationHistories :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  (leftEvents : List (RegistrationEvent name key world error value) **
    (rightEvents : List (RegistrationEvent name key world error value) **
      (O20NativeActivationScan nameEq Z emptyRegistrationIndex left (leftFinalIndex registrations) leftEvents,
       O20NativeActivationScan nameEq Z emptyRegistrationIndex right (rightFinalIndex registrations) rightEvents,
       o20ChronologicalPositions nameEq leftEvents [],
       o20ChronologicalPositions nameEq rightEvents [],
       indexedSurvivingChildCounts (leftFinalIndex registrations) = o20ReplayRetainedEventCounts nameEq leftEvents [],
       indexedSurvivingChildCounts (rightFinalIndex registrations) = o20ReplayRetainedEventCounts nameEq rightEvents [])))
o20AcceptedActivationHistories nameEq left right mapping registrations =
  case o20LeftNativeActivationHistory (generationTraceCorrespondence registrations) of
    (leftEvents ** leftScan) =>
      case rightHistory (generationTraceCorrespondence registrations) of
        (rightEvents ** rightScan) =>
          (leftEvents ** (rightEvents ** (leftScan, rightScan,
            o20NativeChronologicalPositions nameEq Z emptyRegistrationIndex left (leftFinalIndex registrations) leftEvents leftScan,
            o20NativeChronologicalPositions nameEq Z emptyRegistrationIndex right (rightFinalIndex registrations) rightEvents rightScan,
            o20NativeActivationCounts nameEq Z emptyRegistrationIndex left (leftFinalIndex registrations) leftEvents leftScan,
            o20NativeActivationCounts nameEq Z emptyRegistrationIndex right (rightFinalIndex registrations) rightEvents rightScan)))
  where
    0 rightHistory :
      {name, key, world, error : Type} -> {value : key -> Type} ->
      {nameEq : DecEq name} -> {mapping : RegistrationGenerationBijection name} ->
      {leftOrdinal, rightOrdinal : Nat} ->
      {leftIndex, rightIndex, leftFinalIndex, rightFinalIndex : RegistrationIndexState name} ->
      {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
      {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
      {pendingLeft, pendingRight : List (RegistrationEvent name key world error value)} ->
      RegistrationTraceCorrespondence nameEq mapping leftOrdinal leftIndex left leftFinalIndex
        rightOrdinal rightIndex right rightFinalIndex pendingLeft pendingRight ->
      (events : List (RegistrationEvent name key world error value) **
        O20NativeActivationScan nameEq rightOrdinal rightIndex right rightFinalIndex events)
    rightHistory RegistrationCorrespondenceEnd = ([] ** O20ActivationScanEnd)
    rightHistory (SkipRightNonRegistration action edge rest shape ordinary later) =
      case rightHistory later of
        (events ** scan) => (events ** O20ActivationScanOrdinary action edge rest shape ordinary scan)
    rightHistory (DiscardRightDeletedRegistration edge rest shape deleted later) =
      case rightHistory later of
        (events ** scan) => (events ** O20ActivationScanDeleted edge rest shape deleted scan)
    rightHistory {nameEq} {rightOrdinal} {rightIndex}
      (QueueRightGeneratedRegistration {child} {parent} {component} edge rest shape retained later) =
        case rightHistory later of
          (events ** scan) => (registrationEventAt @{nameEq} rightOrdinal rightIndex child parent component :: events **
            O20ActivationScanRetained edge rest shape retained scan)
    rightHistory {nameEq} {rightOrdinal} {rightIndex}
      (MatchRightWithPendingLeft {child} {parent} {component} edge rest shape retained earlierEvents event laterEvents matched later) =
        case rightHistory later of
          (events ** scan) => (registrationEventAt @{nameEq} rightOrdinal rightIndex child parent component :: events **
            O20ActivationScanRetained edge rest shape retained scan)
    rightHistory (SkipLeftNonRegistration action edge rest shape ordinary later) = rightHistory later
    rightHistory (DiscardLeftDeletedRegistration edge rest shape deleted later) = rightHistory later
    rightHistory (QueueLeftGeneratedRegistration edge rest shape retained later) = rightHistory later
    rightHistory (MatchLeftWithPendingRight edge rest shape retained earlierEvents event laterEvents matched later) = rightHistory later

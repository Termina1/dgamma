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

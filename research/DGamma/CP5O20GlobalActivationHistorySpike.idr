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

module DGamma.L2R11LocatedCut

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R10MoveCutObservation
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| A decoded physical source/action query, preserving native occurrence,
||| actual source identity and physical ordinal. No adjacency is asserted yet.
public export
record LocatedSourceAction
  (name, key, world, error : Type) (value : key -> Type)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState)
  (source : SystemState name key value world error)
  (action : Action name key value world error) (ordinal : Nat) where
  constructor MkLocatedSourceAction
  occurrence : LocatedActionOccurrence action trace
  0 exactOrdinal : locatedActionOrdinal occurrence = ordinal
  0 exactSource : actionBeforeState occurrence = source

||| Extend a decoded native occurrence through one physical head. Source
||| identity is unchanged and the ordinal increments by exactly one.
export
0 locatedSourceThroughHead : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (source : SystemState name key value world error) ->
  (action : Action name key value world error) -> (ordinal : Nat) ->
  LocatedSourceAction name key world error value rest source action ordinal ->
  LocatedSourceAction name key world error value (MoreTransitions step rest) source action (S ordinal)
locatedSourceThroughHead step rest source action ordinal (MkLocatedSourceAction located exactOrdinal exactSource) =
  MkLocatedSourceAction
    (MkLocatedActionOccurrence (actionBeforeState located) (actionAfterState located)
      (MoreTransitions step (beforeActionOccurrence located)) (locatedTransition located)
      (afterActionOccurrence located) (locatedAction located)
      (cong (MoreTransitions step) (actionOccurrenceDecomposition located)))
    (cong S exactOrdinal) exactSource

||| An empty physical source/action word has no located query at any index.
export
0 sourceQueryEmpty : {item : Type} -> (ordinal : Nat) -> (wanted : item) ->
  (0 equation : head' (drop ordinal []) = Just wanted) -> Void
sourceQueryEmpty Z wanted equation = absurd equation
sourceQueryEmpty (S ordinal) wanted equation = absurd equation

||| Eliminate only the queried ordinal. The tail continuation is structural
||| recursion, not a supplied locator oracle. Pair equality is transported.
export
0 locateSourceAtStep : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (later : AvailabilityTrace name key world error value rest) ->
  (0 tailDecoder : (position : Nat) -> (wantedSource : SystemState name key value world error) ->
    (wantedAction : Action name key value world error) ->
    (0 found : head' (drop position (trailSourceActions later)) = Just (wantedSource, wantedAction)) ->
    LocatedSourceAction name key world error value rest wantedSource wantedAction position) ->
  (ordinal : Nat) -> (source : SystemState name key value world error) ->
  (action : Action name key value world error) ->
  (0 equation : head' (drop ordinal ((first, transitionAction step) :: trailSourceActions later)) = Just (source, action)) ->
  LocatedSourceAction name key world error value (MoreTransitions step rest) source action ordinal
locateSourceAtStep {name} {key} {world} {error} {value} {first} {middle}
  step rest later tailDecoder Z source action equation =
  replace {p = \pair => LocatedSourceAction name key world error value (MoreTransitions step rest) (fst pair) (snd pair) Z}
    (injective equation)
    (MkLocatedSourceAction
      (MkLocatedActionOccurrence first middle NoTransitions step rest Refl Refl) Refl Refl)
locateSourceAtStep step rest later tailDecoder (S ordinal) source action equation =
  locatedSourceThroughHead step rest source action ordinal (tailDecoder ordinal source action equation)

||| GENERAL native located occurrence decoder for the actual source word.
||| The result produces both physical ordinal and native source identity.
export
0 locateSourceAction : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (ordinal : Nat) -> (source : SystemState name key value world error) ->
  (action : Action name key value world error) ->
  (0 equation : head' (drop ordinal (trailSourceActions trail)) = Just (source, action)) ->
  LocatedSourceAction name key world error value trace source action ordinal
locateSourceAction (AvailabilityEnd state) ordinal source action equation =
  absurd (sourceQueryEmpty ordinal (source, action) equation)
locateSourceAction (AvailabilityStep before (Fired ne ke head tag checked) rest later)
  ordinal source action equation =
  locateSourceAtStep (Fired ne ke head tag checked) rest later (locateSourceAction later)
    ordinal source action equation

||| The ACTUAL selected-square request now produces its native located
||| predecessor, not merely a source/action list observation. This does not
||| yet prove adjacency to the catalog birth or existence of a crossing square.
export
0 selectedCutLocated : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (cut : SelectedSquareCut name key world error value nameEq keyEq trail) ->
  LocatedSourceAction name key world error value trace (cutSource cut) (cutAction cut)
    (pred (catalogOrdinal (cutEntry cut)))
selectedCutLocated nameEq keyEq trail cut =
  locateSourceAction trail (pred (catalogOrdinal (cutEntry cut))) (cutSource cut) (cutAction cut)
    (predecessorSourceEquation cut)

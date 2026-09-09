module DGamma.L2R13TerminalMove

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R5CurrentCut
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R6Iteration
import DGamma.L2R8NativeWords
import DGamma.L2R12DistanceFrame
import Data.Nat
import DGamma.L2R11ClassifierSquare
import DGamma.L2R13InsertExtensional
import DGamma.L2R2CheckedSnapshot
import DGamma.L2R4InsertReplay
import DGamma.L2R5Extensional
import DGamma.L2R5ExtensionalRetire
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Executable two-edge native trail. All source states and dictionaries
||| are explicit; the checked equations remain erased.
public export
nativePairTrail : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (first, middle, last : SystemState name key value world error) ->
  (leftAction, rightAction : Action name key value world error) -> (leftTag, rightTag : RuleTag) ->
  (0 left : checkedApplyAction @{nameEq} @{keyEq} leftAction first = Just (leftTag, middle)) ->
  (0 right : checkedApplyAction @{nameEq} @{keyEq} rightAction middle = Just (rightTag, last)) ->
  AvailabilityTrace name key world error value
    (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq leftAction leftTag left)
      (MoreTransitions (Fired {before = middle} {afterState = last} nameEq keyEq rightAction rightTag right) NoTransitions))
nativePairTrail nameEq keyEq first middle last leftAction rightAction leftTag rightTag left right =
  AvailabilityStep first (Fired {before = first} {afterState = middle} nameEq keyEq leftAction leftTag left)
    (MoreTransitions (Fired {before = middle} {afterState = last} nameEq keyEq rightAction rightTag right) NoTransitions)
    (AvailabilityStep middle (Fired {before = middle} {afterState = last} nameEq keyEq rightAction rightTag right)
      NoTransitions (AvailabilityEnd last))

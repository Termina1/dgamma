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

||| GENUINE local terminal-square move producer. Both whole native traces,
||| physical occurrences/adjacency, action words, current cuts, endpoint and
||| exact decrement are DERIVED from the square and native scan frames.
||| This local theorem has NO suffix. It is not GeneralAdmittedMoveExistence:
||| phase/NeverRetired/uniqueness and global frame existence remain its domain
||| obligations; none is silently dropped from that unchanged global type.
||| Public because downstream consumers reduce its computed record fields.
public export
0 terminalSquareAdmittedMove : {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (root : name) ->
  (component : Component key value world error) ->
  (source, oldMiddle, oldFinal : SystemState name key value world error) ->
  (action : Action name key value world error) -> (crossTag : RuleTag) ->
  (before : Transitions initial source) ->
  (prefixTrail : AvailabilityTrace name key world error value before) ->
  (0 oldChecked : checkedApplyAction @{nameEq} @{keyEq} action source = Just (crossTag, oldMiddle)) ->
  (0 oldRoot : checkedApplyAction @{nameEq} @{keyEq} (OInsert root Root component) oldMiddle = Just (OInsertTag, oldFinal)) ->
  (square : ClassifierSquare name key world error value nameEq keyEq root component source action crossTag oldFinal) ->
  (0 forced : ForcedOnTrace nameEq keyEq (appendAvailability prefixTrail (nativePairTrail nameEq keyEq source oldMiddle oldFinal action (OInsert root Root component) crossTag OInsertTag oldChecked oldRoot)) (S (length (nativeActionWord prefixTrail)))) ->
  (target, untouched : Nat) -> (0 bounded : LTE target (length (nativeActionWord prefixTrail))) ->
  (0 oldFrame : totalDistance nameEq keyEq (appendAvailability prefixTrail (nativePairTrail nameEq keyEq source oldMiddle oldFinal action (OInsert root Root component) crossTag OInsertTag oldChecked oldRoot)) = minus (S (length (nativeActionWord prefixTrail))) target + untouched) ->
  (0 newFrame : totalDistance nameEq keyEq (appendAvailability prefixTrail (nativePairTrail nameEq keyEq source (squareMiddle square) (squareFinal square) (OInsert root Root component) action OInsertTag crossTag (earlyChecked square) (laterChecked square))) = minus (length (nativeActionWord prefixTrail)) target + untouched) ->
  AdmittedDistanceMove name key world error value nameEq keyEq (appendAvailability prefixTrail (nativePairTrail nameEq keyEq source oldMiddle oldFinal action (OInsert root Root component) crossTag OInsertTag oldChecked oldRoot)) (appendAvailability prefixTrail (nativePairTrail nameEq keyEq source (squareMiddle square) (squareFinal square) (OInsert root Root component) action OInsertTag crossTag (earlyChecked square) (laterChecked square)))
terminalSquareAdmittedMove nameEq keyEq root component source oldMiddle oldFinal action crossTag
  before prefixTrail oldChecked oldRoot square forced target untouched bounded oldFrame newFrame =
  MkAdmittedDistanceMove root component (nativeActionWord prefixTrail) action []
    (MkLocatedActionOccurrence source oldMiddle before (Fired {before = source} {afterState = oldMiddle} nameEq keyEq action crossTag oldChecked) (MoreTransitions (Fired {before = oldMiddle} {afterState = oldFinal} nameEq keyEq (OInsert root Root component) OInsertTag oldRoot) NoTransitions) Refl Refl)
    (MkLocatedActionOccurrence source (squareMiddle square) before (Fired {before = source} {afterState = squareMiddle square} nameEq keyEq (OInsert root Root component) OInsertTag (earlyChecked square)) (MoreTransitions (Fired {before = squareMiddle square} {afterState = squareFinal square} nameEq keyEq action crossTag (laterChecked square)) NoTransitions) Refl Refl)
    (sym (nativeWordCount prefixTrail)) (sym (nativeWordCount prefixTrail)) (squareAdmitted square)
    forced (nativeWordAppend prefixTrail (nativePairTrail nameEq keyEq source oldMiddle oldFinal action (OInsert root Root component) crossTag OInsertTag oldChecked oldRoot)) (nativeWordAppend prefixTrail (nativePairTrail nameEq keyEq source (squareMiddle square) (squareFinal square) (OInsert root Root component) action OInsertTag crossTag (earlyChecked square) (laterChecked square)))
    (checkedRootCurrentAvailable nameEq keyEq root component oldMiddle oldFinal OInsertTag oldRoot)
    (squareCurrentCut square)
    (totalDistance nameEq keyEq (appendAvailability prefixTrail (nativePairTrail nameEq keyEq source oldMiddle oldFinal action (OInsert root Root component) crossTag OInsertTag oldChecked oldRoot))) (totalDistance nameEq keyEq (appendAvailability prefixTrail (nativePairTrail nameEq keyEq source (squareMiddle square) (squareFinal square) (OInsert root Root component) action OInsertTag crossTag (earlyChecked square) (laterChecked square)))) Refl Refl
    (totalDistanceOneLeftFromFrame nameEq keyEq (appendAvailability prefixTrail (nativePairTrail nameEq keyEq source oldMiddle oldFinal action (OInsert root Root component) crossTag OInsertTag oldChecked oldRoot)) (appendAvailability prefixTrail (nativePairTrail nameEq keyEq source (squareMiddle square) (squareFinal square) (OInsert root Root component) action OInsertTag crossTag (earlyChecked square) (laterChecked square)))
      (length (nativeActionWord prefixTrail)) target untouched bounded oldFrame newFrame)
    (squareEndpoint square)

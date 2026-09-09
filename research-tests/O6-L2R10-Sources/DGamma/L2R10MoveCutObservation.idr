module DGamma.L2R10MoveCutObservation

import Prelude.Types
import Prelude.Interfaces
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R7CatalogBirth
import DGamma.L2R8DistanceSearch
import DGamma.L2R9ControlClass
import DGamma.L2R9PredecessorClass
import DGamma.L2R9NativeSelection
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core
import Decidable.Decidable

%default total
%unbound_implicits off

||| Actual source/action word, preserving every physical transition position.
||| This is executable data, not a caller-supplied predecessor/catalog oracle.
public export
trailSourceActions : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 initial, finalState : SystemState name key value world error} ->
  {0 trace : Transitions initial finalState} ->
  AvailabilityTrace name key world error value trace ->
  List (SystemState name key value world error, Action name key value world error)
trailSourceActions (AvailabilityEnd state) = []
trailSourceActions (AvailabilityStep source (Fired ne ke action tag checked) rest later) =
  (source, action) :: trailSourceActions later

||| Typed native square REQUEST, not a square/move. The actual first-positive
||| catalog item, exact predecessor data position, source/action classifier,
||| and actual early-root checked evaluator result are observed together.
||| Local/missing/root predecessor cases and failed early applicability remain
||| visible. No field assumes an admitted crossing, replay edge, or distance
||| decrement. The source/action-word occurrence decoder is still separate.
public export
record SelectedSquareCut
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {0 initial, finalState : SystemState name key value world error}
  {0 trace : Transitions initial finalState}
  (0 trail : AvailabilityTrace name key world error value trace) where
  constructor MkSelectedSquareCut
  cutEntry : RootCatalogEntry name key world error value
  earlierEntries : List (RootCatalogEntry name key world error value)
  laterEntries : List (RootCatalogEntry name key world error value)
  positivePredecessor : Nat
  cutSource : SystemState name key value world error
  cutAction : Action name key value world error
  cutClass : PredecessorClass nameEq (catalogRoot cutEntry) cutSource cutAction
  earlyRootResult : Maybe (RuleTag, SystemState name key value world error)
  0 earlyRootEquation : checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (OInsert (catalogRoot cutEntry) Root (catalogComponent cutEntry)) cutSource = earlyRootResult
  0 selectedMember : Elem cutEntry (scanRootCatalog 0 trail)
  0 selectedCatalogSplit : scanRootCatalog 0 trail = earlierEntries ++ cutEntry :: laterEntries
  0 earlierDistancesZero : All (\entry => rootDistance nameEq keyEq trail (catalogOrdinal entry) = 0) earlierEntries
  0 selectedDistanceEquation : rootDistance nameEq keyEq trail (catalogOrdinal cutEntry) = S positivePredecessor
  0 predecessorSourceEquation : head' (drop (pred (catalogOrdinal cutEntry)) (trailSourceActions trail)) = Just (cutSource, cutAction)
  0 selectedNativeBirth : CatalogBirthAt name key world error value cutEntry 0 trace

||| Eliminate the already observed source/action PAIR once. Source classifier,
||| native early-root evaluator, and catalog-birth decoding are computed HERE.
public export
selectedCutAtPair :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 initial, finalState : SystemState name key value world error} ->
  {0 trace : Transitions initial finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (entry : RootCatalogEntry name key world error value) ->
  (before, after : List (RootCatalogEntry name key world error value)) ->
  (predecessor : Nat) ->
  (0 member : Elem entry (scanRootCatalog 0 trail)) ->
  (0 split : scanRootCatalog 0 trail = before ++ entry :: after) ->
  (0 zeros : All (\item => rootDistance nameEq keyEq trail (catalogOrdinal item) = 0) before) ->
  (0 positive : rootDistance nameEq keyEq trail (catalogOrdinal entry) = S predecessor) ->
  (observed : (SystemState name key value world error, Action name key value world error)) ->
  (0 equation : head' (drop (pred (catalogOrdinal entry)) (trailSourceActions trail)) = Just observed) ->
  Maybe (SelectedSquareCut name key world error value nameEq keyEq trail)
selectedCutAtPair {name} {key} {world} {error} {value} nameEq keyEq trail entry before after predecessor member split zeros positive (source, action) equation =
  Just (MkSelectedSquareCut entry before after predecessor source action
    (classifyPredecessor nameEq (catalogRoot entry) source action)
    (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
      (OInsert (catalogRoot entry) Root (catalogComponent entry)) source)
    Refl member split zeros positive equation (scanCatalogBirth 0 trail entry member))

||| Eliminate ONLY the explicit predecessor-data Maybe. Nothing is retained
||| honestly; no native predecessor existence or move is supplied by fiat.
public export
selectedCutAtLookup :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 initial, finalState : SystemState name key value world error} ->
  {0 trace : Transitions initial finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (entry : RootCatalogEntry name key world error value) ->
  (before, after : List (RootCatalogEntry name key world error value)) ->
  (predecessor : Nat) ->
  (0 member : Elem entry (scanRootCatalog 0 trail)) ->
  (0 split : scanRootCatalog 0 trail = before ++ entry :: after) ->
  (0 zeros : All (\item => rootDistance nameEq keyEq trail (catalogOrdinal item) = 0) before) ->
  (0 positive : rootDistance nameEq keyEq trail (catalogOrdinal entry) = S predecessor) ->
  (observed : Maybe (SystemState name key value world error, Action name key value world error)) ->
  (0 equation : head' (drop (pred (catalogOrdinal entry)) (trailSourceActions trail)) = observed) ->
  Maybe (SelectedSquareCut name key world error value nameEq keyEq trail)
selectedCutAtLookup nameEq keyEq trail entry before after predecessor member split zeros positive Nothing equation = Nothing
selectedCutAtLookup nameEq keyEq trail entry before after predecessor member split zeros positive (Just observed) equation =
  selectedCutAtPair nameEq keyEq trail entry before after predecessor member split zeros positive observed equation

||| Consume the explicitly observed ACTUAL first-positive search. Earlier
||| zero distances, catalog split, and positive equation remain in the result.
public export
selectedCutAtSearch :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 initial, finalState : SystemState name key value world error} ->
  {0 trace : Transitions initial finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (distance : RootCatalogEntry name key world error value -> Nat) ->
  (items : List (RootCatalogEntry name key world error value)) ->
  (0 distanceEquation : (\entry => rootDistance nameEq keyEq trail (catalogOrdinal entry)) = distance) ->
  (0 catalogEquation : scanRootCatalog 0 trail = items) ->
  (observed : DistanceSearch distance items) ->
  (0 equation : searchDistance distance items = observed) ->
  Maybe (SelectedSquareCut name key world error value nameEq keyEq trail)
selectedCutAtSearch nameEq keyEq trail distance items distanceEquation catalogEquation (AllDistancesZero zeros) equation = Nothing
selectedCutAtSearch nameEq keyEq trail distance items distanceEquation catalogEquation (FoundFirstPositive entry before after predecessor member split zeros positive) equation =
  selectedCutAtLookup nameEq keyEq trail entry before after predecessor
    (replace {p = Elem entry} (sym catalogEquation) member)
    (trans catalogEquation split)
    (replace {p = \fn => All (\item => fn item = 0) before} (sym distanceEquation) zeros)
    (trans (cong (\fn => fn entry) distanceEquation) positive)
    (head' (drop (pred (catalogOrdinal entry)) (trailSourceActions trail))) Refl

||| GENERAL executable, oracle-free square-availability REQUEST producer.
||| Selects through selectNativeDistanceRoot, reads its actual predecessor
||| position, classifies the native source/action and executes early OInsert.
||| It does NOT assume success, cross replay, endpoints, forcing or decrement;
||| hence it is not produceAdmittedDistanceMove or a terminating normalizer.
public export
observeSelectedMoveCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 initial, finalState : SystemState name key value world error} ->
  {0 trace : Transitions initial finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  Maybe (SelectedSquareCut name key world error value nameEq keyEq trail)
observeSelectedMoveCut nameEq keyEq trail =
  selectedCutAtSearch nameEq keyEq trail
    (\entry => rootDistance nameEq keyEq trail (catalogOrdinal entry)) (scanRootCatalog 0 trail) Refl Refl
    (nativeSearch (selectNativeDistanceRoot nameEq keyEq trail))
    (nativeSearchEquation (selectNativeDistanceRoot nameEq keyEq trail))

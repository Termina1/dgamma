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

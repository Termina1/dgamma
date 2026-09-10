module DGamma.L2R15GlobalFrames

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5UniqueRawNameInsertions
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R6FrontNormal
import DGamma.L2R6Phase
import DGamma.L2R6Iteration
import DGamma.L2R8NativeWords
import DGamma.L2R11ClassifierSquare
import DGamma.L2R13TerminalMove
import DGamma.L2R13NativeSuffixFrames
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Exact OPEN global frame obligation, under the existing phase/front/
||| never-retired/uniqueness/outer-order domain, an ACTUAL native crossing
||| square and native Root/Retire suffix frames. This is a TYPE declaration,
||| NOT inhabited. Suffix-only scan equality does not prove these prefixed
||| equations: pre-existing releases and shifted birth cuts remain relevant.
||| No premise is added to GeneralAdmittedMoveExistenceUnique by this type.
public export
GlobalDistanceFramesFromNativeSuffix : {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, oldEnd, newEnd : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (root : name) ->
  (component : Component key value world error) ->
  (source, oldMiddle, oldLocalEnd : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before : Transitions initial source) ->
  (prefixTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value before) ->
  (0 oldChecked : checkedApplyAction @{nameEq} @{keyEq} action source = Just (tag, oldMiddle)) ->
  (0 oldRoot : checkedApplyAction @{nameEq} @{keyEq} (OInsert root Root component) oldMiddle = Just (OInsertTag, oldLocalEnd)) ->
  (square : ClassifierSquare name key world error value nameEq keyEq root component source action tag oldLocalEnd) ->
  (oldSuffix : Transitions oldLocalEnd oldEnd) ->
  (newSuffix : Transitions (squareFinal square) newEnd) ->
  (oldSuffixTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value oldSuffix) ->
  (newSuffixTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value newSuffix) ->
  (frames : NativeSuffixFrames nameEq keyEq oldSuffix newSuffix) -> Type
GlobalDistanceFramesFromNativeSuffix {name} {key} {world} {error} {value} {initial}
  nameEq keyEq root component source oldMiddle oldLocalEnd action tag before prefixTrail
  oldChecked oldRoot square oldSuffix newSuffix oldSuffixTrail newSuffixTrail frames =
  (0 valid : registryWellFormed @{nameEq} @{keyEq} initial = True) ->
  (0 unique : UniqueRawNameInsertions name key world error value nameEq keyEq (appendTransitions before (MoreTransitions (Fired {before = source} {afterState = oldMiddle} nameEq keyEq action tag oldChecked) (MoreTransitions (Fired {before = oldMiddle} {afterState = oldLocalEnd} nameEq keyEq (OInsert root Root component) OInsertTag oldRoot) oldSuffix)))) ->
  (0 front : FrontNormal name key world error value nameEq keyEq (appendAvailability prefixTrail (appendAvailability (nativePairTrail nameEq keyEq source oldMiddle oldLocalEnd action (OInsert root Root component) tag OInsertTag oldChecked oldRoot) oldSuffixTrail))) ->
  (0 never : ForcedRootNeverRetired name key world error value nameEq keyEq (appendAvailability prefixTrail (appendAvailability (nativePairTrail nameEq keyEq source oldMiddle oldLocalEnd action (OInsert root Root component) tag OInsertTag oldChecked oldRoot) oldSuffixTrail))) ->
  (0 phases : (entry : RootCatalogEntry name key world error value) -> Elem entry (scanRootCatalog 0 (appendAvailability prefixTrail (appendAvailability (nativePairTrail nameEq keyEq source oldMiddle oldLocalEnd action (OInsert root Root component) tag OInsertTag oldChecked oldRoot) oldSuffixTrail))) ->
    ForcedOnTrace nameEq keyEq (appendAvailability prefixTrail (appendAvailability (nativePairTrail nameEq keyEq source oldMiddle oldLocalEnd action (OInsert root Root component) tag OInsertTag oldChecked oldRoot) oldSuffixTrail)) (catalogOrdinal entry) -> ForcedRootPhase name key world error value nameEq keyEq (appendAvailability prefixTrail (appendAvailability (nativePairTrail nameEq keyEq source oldMiddle oldLocalEnd action (OInsert root Root component) tag OInsertTag oldChecked oldRoot) oldSuffixTrail)) entry) ->
  (0 forced : ForcedOnTrace nameEq keyEq (appendAvailability prefixTrail (appendAvailability (nativePairTrail nameEq keyEq source oldMiddle oldLocalEnd action (OInsert root Root component) tag OInsertTag oldChecked oldRoot) oldSuffixTrail)) (S (length (nativeActionWord prefixTrail)))) ->
  (0 earlierPlaced : (entry : RootCatalogEntry name key world error value) -> Elem entry (scanRootCatalog 0 (appendAvailability prefixTrail (appendAvailability (nativePairTrail nameEq keyEq source oldMiddle oldLocalEnd action (OInsert root Root component) tag OInsertTag oldChecked oldRoot) oldSuffixTrail))) ->
    LT (catalogOrdinal entry) (S (length (nativeActionWord prefixTrail))) -> ForcedOnTrace nameEq keyEq (appendAvailability prefixTrail (appendAvailability (nativePairTrail nameEq keyEq source oldMiddle oldLocalEnd action (OInsert root Root component) tag OInsertTag oldChecked oldRoot) oldSuffixTrail)) (catalogOrdinal entry) ->
    rootDistance nameEq keyEq (appendAvailability prefixTrail (appendAvailability (nativePairTrail nameEq keyEq source oldMiddle oldLocalEnd action (OInsert root Root component) tag OInsertTag oldChecked oldRoot) oldSuffixTrail)) (catalogOrdinal entry) = 0) ->
  (target : Nat) ->
  (0 targetEquation : targetPosition nameEq keyEq (appendAvailability prefixTrail (appendAvailability (nativePairTrail nameEq keyEq source oldMiddle oldLocalEnd action (OInsert root Root component) tag OInsertTag oldChecked oldRoot) oldSuffixTrail)) (S (length (nativeActionWord prefixTrail))) = target) ->
  (0 bounded : LTE target (length (nativeActionWord prefixTrail))) ->
  (untouched : Nat **
    (totalDistance nameEq keyEq (appendAvailability prefixTrail (appendAvailability (nativePairTrail nameEq keyEq source oldMiddle oldLocalEnd action (OInsert root Root component) tag OInsertTag oldChecked oldRoot) oldSuffixTrail)) = minus (S (length (nativeActionWord prefixTrail))) target + untouched,
     totalDistance nameEq keyEq (appendAvailability prefixTrail (appendAvailability (nativePairTrail nameEq keyEq source (squareMiddle square) (squareFinal square) (OInsert root Root component) action OInsertTag tag (earlyChecked square) (laterChecked square)) newSuffixTrail)) = minus (length (nativeActionWord prefixTrail)) target + untouched))

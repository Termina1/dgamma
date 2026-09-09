module DGamma.L2R6Anchors

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3Attached
import DGamma.L2R3AttachedGap
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Observed maximum removal-ending cut; Nothing means no release. Ordinals
||| remain current-trace positions, NOT stable identities across a swap.
public export
lastReleaseCut : List Nat -> Maybe Nat
lastReleaseCut [] = Nothing
lastReleaseCut (ordinal :: later) = Just (S (foldl max ordinal later))

||| Maximum of actual key-release scans for catalog roots at or before this
||| root in orchestration order. An unseeded barrier inherits earlier releases;
||| a later key release raises the anchor. Non-forced prefixes return Nothing.
public export
anchorOf : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  DecEq name -> DecEq key -> AvailabilityTrace name key world error value trace -> Nat -> Maybe Nat
anchorOf nameEq keyEq trail ordinal = lastReleaseCut (concatMap
  (\entry => scanReleaseOrdinals nameEq keyEq (catalogComponent entry) 0 (catalogOrdinal entry) trail)
  (filter (\entry => catalogOrdinal entry <= ordinal) (scanRootCatalog 0 trail)))

||| Observed anchor and its exact maximum input, alongside the SAME root's
||| KeyForcedAt observation. No maximal-element/occurrence decoder or stable
||| original-release transport theorem is hidden in these equations.
public export
record AnchorAssignment
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {0 first, finalState : SystemState name key value world error}
  {0 trace : Transitions first finalState}
  (trail : AvailabilityTrace name key world error value trace)
  (entry : RootCatalogEntry name key world error value) where
  constructor MkAnchorAssignment
  anchorKeyObservation : KeyForcedAt name key world error value nameEq keyEq trail entry
  anchorReleaseOrdinals : List Nat
  0 anchorReleaseEquation : anchorReleaseOrdinals = concatMap
    (\seed => scanReleaseOrdinals nameEq keyEq (catalogComponent seed) 0 (catalogOrdinal seed) trail)
    (filter (\seed => catalogOrdinal seed <= catalogOrdinal entry) (scanRootCatalog 0 trail))
  assignedAnchorObserved : Maybe Nat
  0 assignedMaximumEquation : lastReleaseCut anchorReleaseOrdinals = assignedAnchorObserved
  0 assignedAnchorEquation : anchorOf nameEq keyEq trail (catalogOrdinal entry) = assignedAnchorObserved

||| Single-constructor assignment observations from the actual trace. Key
||| witness and maximum use the same catalog item and release-scan definition.
public export
anchorAssignment : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (entry : RootCatalogEntry name key world error value) ->
  (0 member : Elem entry (scanRootCatalog 0 trail)) ->
  AnchorAssignment name key world error value nameEq keyEq trail entry
anchorAssignment nameEq keyEq trail entry member = MkAnchorAssignment
  (keyForcedAt nameEq keyEq trail entry member)
  (concatMap (\seed => scanReleaseOrdinals nameEq keyEq (catalogComponent seed) 0 (catalogOrdinal seed) trail)
    (filter (\seed => catalogOrdinal seed <= catalogOrdinal entry) (scanRootCatalog 0 trail))) Refl
  (anchorOf nameEq keyEq trail (catalogOrdinal entry)) Refl Refl

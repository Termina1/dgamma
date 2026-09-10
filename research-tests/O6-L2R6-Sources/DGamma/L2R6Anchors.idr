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
  DecEq name -> DecEq key -> DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace -> Nat -> Maybe Nat
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
  (trail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace)
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
  (trail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace) ->
  (entry : RootCatalogEntry name key world error value) ->
  (0 member : Elem entry (scanRootCatalog 0 trail)) ->
  AnchorAssignment name key world error value nameEq keyEq trail entry
anchorAssignment nameEq keyEq trail entry member = MkAnchorAssignment
  (keyForcedAt nameEq keyEq trail entry member)
  (concatMap (\seed => scanReleaseOrdinals nameEq keyEq (catalogComponent seed) 0 (catalogOrdinal seed) trail)
    (filter (\seed => catalogOrdinal seed <= catalogOrdinal entry) (scanRootCatalog 0 trail))) Refl
  (anchorOf nameEq keyEq trail (catalogOrdinal entry)) Refl Refl

||| Catalog roots sharing this observed release anchor, retaining their actual
||| external orchestration order. Nothing-anchored non-forced roots reject.
public export
placedRootsAt : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  DecEq name -> DecEq key -> DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace -> Nat ->
  List (RootCatalogEntry name key world error value)
placedRootsAt nameEq keyEq trail anchor = filter
  (\entry => anchorOf nameEq keyEq trail (catalogOrdinal entry) == Just anchor) (scanRootCatalog 0 trail)

||| Connector between the generated same-anchor catalog and ONE actual
||| OrderedForcedRootBundle (inside placedMember). Its complete catalog equals
||| all same-anchor roots in order; its starting interval is exactly the
||| observed release-ending cut, immediately after that member's actor core.
||| This record states placement, not a general producer for arbitrary traces.
public export
record PlacedBundle
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {first, finalState : SystemState name key value world error}
  {trace : Transitions first finalState}
  (trail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace) (anchor : Nat) where
  constructor MkPlacedBundle
  representativeAction : Action name key value world error
  representativeOrdinal : Nat
  placedMember : DGamma.L2R3AttachedGap.AttachedBundleOccurrence name key world error value nameEq keyEq trace representativeAction representativeOrdinal
  placedBundleTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value (memberBundle placedMember)
  0 placedImmediatelyAfterRelease : bundleOffset placedMember = anchor
  0 placedCatalogExact : scanRootCatalog (bundleOffset placedMember) placedBundleTrail = placedRootsAt nameEq keyEq trail anchor

||| Forced-root target: max(anchor plus same-anchor rank, one past the latest
||| earlier different-anchor/non-forced root birth). External order forbids
||| crossing that earlier birth. In the phase/front/never-retired domain,
||| controls are at the front; same-anchor roots use outer orchestration order.
public export
targetPosition : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  DecEq name -> DecEq key -> DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace -> Nat -> Nat
targetPosition nameEq keyEq trail ordinal = max
  (fromMaybe 0 (anchorOf nameEq keyEq trail ordinal) +
    length (filter (\earlier => catalogOrdinal earlier < ordinal &&
      anchorOf nameEq keyEq trail (catalogOrdinal earlier) == anchorOf nameEq keyEq trail ordinal)
      (scanRootCatalog 0 trail)))
  (fromMaybe 0 (lastReleaseCut (map catalogOrdinal
    (filter (\earlier => catalogOrdinal earlier < ordinal &&
      not (anchorOf nameEq keyEq trail (catalogOrdinal earlier) == anchorOf nameEq keyEq trail ordinal))
      (scanRootCatalog 0 trail)))))

||| Physical cut minus ordered target, charging only anchored roots. Nat
||| subtraction saturates: zero alone is NOT a placement theorem without
||| the separate current-cut/target-order and structural coverage invariants.
public export
rootDistance : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  DecEq name -> DecEq key -> DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace -> Nat -> Nat
rootDistance nameEq keyEq trail ordinal = if isJust (anchorOf nameEq keyEq trail ordinal)
  then minus ordinal (targetPosition nameEq keyEq trail ordinal) else 0

||| Sum of physical distances over the actual generated birth catalog; no
||| caller-supplied annotations, root list, distance or target is accepted.
public export
totalDistance : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  DecEq name -> DecEq key -> DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace -> Nat
totalDistance nameEq keyEq trail = sum
  (map (\entry => rootDistance nameEq keyEq trail (catalogOrdinal entry)) (scanRootCatalog 0 trail))

||| Explicit Nat observations/equations for one root and the complete actual
||| trace. This contains neither a positive-distance move nor a zero-NF proof.
public export
record DistanceObservation
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {0 first, finalState : SystemState name key value world error}
  {0 trace : Transitions first finalState}
  (trail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace) (ordinal : Nat) where
  constructor MkDistanceObservation
  targetObserved : Nat
  0 targetEquation : targetPosition nameEq keyEq trail ordinal = targetObserved
  distanceObserved : Nat
  0 distanceEquation : rootDistance nameEq keyEq trail ordinal = distanceObserved
  totalObserved : Nat
  0 totalEquation : totalDistance nameEq keyEq trail = totalObserved

||| Total single-constructor producer; observed Nats are calculated, never
||| supplied as distance/zero premises by callers.
public export
distanceObservation : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace) -> (ordinal : Nat) ->
  DistanceObservation name key world error value nameEq keyEq trail ordinal
distanceObservation nameEq keyEq trail ordinal = MkDistanceObservation
  (targetPosition nameEq keyEq trail ordinal) Refl
  (rootDistance nameEq keyEq trail ordinal) Refl
  (totalDistance nameEq keyEq trail) Refl

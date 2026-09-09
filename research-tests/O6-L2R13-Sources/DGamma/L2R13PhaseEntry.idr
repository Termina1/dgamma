module DGamma.L2R13PhaseEntry

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.EqOrd
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R7Classifier
import DGamma.L2R7ObservedAny
import DGamma.L2R7PlacedCoverage
import DGamma.L2R13ForcedAnchor
import DGamma.L2R8OriginMembership
import DGamma.L2R7CatalogBirth
import DGamma.L2R10PhaseScan
import DGamma.L2R12PhaseAccepted
import Data.Bool
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Simultaneously PRODUCE the forced anchor, its accepted native seed and
||| the actual forced-root birth FROM scanCatalogBirth. This is NOT yet the
||| contiguous core/release/lifecycle decoder of ForcedRootPhase.
export
0 produceForcedPhaseEntry : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (entry : RootCatalogEntry name key world error value) ->
  (0 member : Elem entry (scanRootCatalog 0 trail)) ->
  (0 accepted : phaseScanOk nameEq keyEq trail = True) ->
  (0 classified : any (\seed => catalogOrdinal seed <= catalogOrdinal entry &&
    keyForcedOrdinal nameEq keyEq trail (catalogOrdinal seed)) (scanRootCatalog 0 trail) = True) ->
  (anchor : Nat ** (anchorOf nameEq keyEq trail (catalogOrdinal entry) = Just anchor,
    AnyHit (phaseAnchorSeedCheck nameEq keyEq trail entry anchor) (scanRootCatalog 0 trail),
    CatalogBirthAt name key world error value entry 0 trace))
produceForcedPhaseEntry nameEq keyEq trail entry member accepted classified =
  (fst (forcedAnchorJust nameEq keyEq trail (catalogOrdinal entry) True classified Refl) **
    (snd (forcedAnchorJust nameEq keyEq trail (catalogOrdinal entry) True classified Refl),
     phaseSeedAtAnchor nameEq keyEq trail entry
       (fst (forcedAnchorJust nameEq keyEq trail (catalogOrdinal entry) True classified Refl))
       (snd (forcedAnchorJust nameEq keyEq trail (catalogOrdinal entry) True classified Refl)) member accepted,
     scanCatalogBirth 0 trail entry member))

||| An observed maximum anchor carries its actual scan index and is one
||| past that index. This exposes physical-count arithmetic, NOT a located
||| core or a proof that every release is below the folded maximum.
export
0 phaseMaximumIndex : (items : List Nat) -> (anchor : Nat) ->
  (0 equation : lastReleaseCut items = Just anchor) ->
  (Elem (pred anchor) items, S (pred anchor) = anchor)
phaseMaximumIndex [] anchor equation = absurd equation
phaseMaximumIndex (head :: rest) anchor equation =
  (originMaximumMember (head :: rest) (Just (pred anchor))
     (cong (map pred) equation) (pred anchor) Refl,
   replace {p = \cut => S (pred cut) = cut} (injective equation) Refl)

||| Native scan acceptance transports the produced anchor into a count bound
||| before the AUTHENTIC root birth. The maximum release index is produced
||| alongside that bound. Contiguous interval/lifecycle localization is open.
export
0 phaseAnchorCountBound : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (entry : RootCatalogEntry name key world error value) -> (anchor : Nat) ->
  (0 equation : anchorOf nameEq keyEq trail (catalogOrdinal entry) = Just anchor) ->
  (0 member : Elem entry (scanRootCatalog 0 trail)) ->
  (0 accepted : phaseScanOk nameEq keyEq trail = True) ->
  (LTE anchor (catalogOrdinal entry),
   Elem (pred anchor) (concatMap
     (\seed => scanReleaseOrdinals nameEq keyEq (catalogComponent seed) 0 (catalogOrdinal seed) trail)
     (filter (\seed => catalogOrdinal seed <= catalogOrdinal entry) (scanRootCatalog 0 trail))),
   S (pred anchor) = anchor)
phaseAnchorCountBound nameEq keyEq trail entry anchor equation member accepted =
  (lteReflectsLTE anchor (catalogOrdinal entry)
    (trans (sym (leToLte anchor (catalogOrdinal entry)))
      (boolAndLeft (anchor <= catalogOrdinal entry)
        (any (phaseAnchorSeedCheck nameEq keyEq trail entry anchor) (scanRootCatalog 0 trail))
        (replace {p = \observed => maybe True (\cut => cut <= catalogOrdinal entry &&
          any (phaseAnchorSeedCheck nameEq keyEq trail entry cut) (scanRootCatalog 0 trail)) observed = True}
          equation (phaseScanEntryAccepted nameEq keyEq trail entry member accepted)))),
   phaseMaximumIndex (concatMap
     (\seed => scanReleaseOrdinals nameEq keyEq (catalogComponent seed) 0 (catalogOrdinal seed) trail)
     (filter (\seed => catalogOrdinal seed <= catalogOrdinal entry) (scanRootCatalog 0 trail))) anchor equation)

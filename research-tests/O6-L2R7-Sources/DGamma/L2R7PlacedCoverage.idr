module DGamma.L2R7PlacedCoverage

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3Attached
import DGamma.L2R3AttachedGap
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R7CatalogBirth
import Data.List
import Data.List.Elem
import Data.Nat
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Upgrade a genuine decoded bundle birth to a FULL global attached-bundle
||| occurrence. Reuse the same located block, core and bundle; construct the
||| new occurrence and physical bounds with exact count transport.
export
0 placedBirthFromDecoded : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  {trail : AvailabilityTrace name key world error value trace} -> {anchor : Nat} ->
  (placed : PlacedBundle name key world error value nameEq keyEq trail anchor) ->
  (entry : RootCatalogEntry name key world error value) ->
  (birth : CatalogBirthAt name key world error value entry (bundleOffset (placedMember placed)) (memberBundle (placedMember placed))) ->
  AttachedBundleOccurrence name key world error value nameEq keyEq trace
    (OInsert (catalogRoot entry) Root (catalogComponent entry)) (catalogOrdinal entry)
placedBirthFromDecoded placed entry birth = MkAttachedBundleOccurrence
  (bundleActor (placedMember placed)) (containingBlock (placedMember placed))
  (coreEnd (placedMember placed)) (memberCore (placedMember placed)) (memberExtended (placedMember placed))
  (memberBundle (placedMember placed)) (memberForced (placedMember placed)) (memberSplit (placedMember placed))
  (catalogBirthOccurrence birth) (bundleOffset (placedMember placed)) (offsetExact (placedMember placed)) (catalogBirthOrdinal birth)
  (replace {p = \position => LTE (bundleOffset (placedMember placed)) position} (sym (catalogBirthOrdinal birth))
    (lteAddRight (bundleOffset (placedMember placed))))
  (replace {p = \position => LT position (bundleOffset (placedMember placed) + transitionCount (memberBundle (placedMember placed)))}
    (sym (catalogBirthOrdinal birth))
    (rewrite plusSuccRightSucc (bundleOffset (placedMember placed)) (locatedActionOrdinal (catalogBirthOccurrence birth)) in
      plusLteMonotoneLeft (bundleOffset (placedMember placed)) (S (locatedActionOrdinal (catalogBirthOccurrence birth)))
        (transitionCount (memberBundle (placedMember placed))) (locatedBirthBound (catalogBirthOccurrence birth))))

||| GENERAL PlacedBundle catalog-equality -> actual occurrence coverage.
||| The occurrence is produced by scanCatalogBirth, never supplied as a
||| rootInBundle callback or taken from the representative's own birth.
export
0 placedCatalogCoverage : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  {trail : AvailabilityTrace name key world error value trace} -> {anchor : Nat} ->
  (placed : PlacedBundle name key world error value nameEq keyEq trail anchor) ->
  (entry : RootCatalogEntry name key world error value) ->
  (0 member : Elem entry (placedRootsAt nameEq keyEq trail anchor)) ->
  AttachedBundleOccurrence name key world error value nameEq keyEq trace
    (OInsert (catalogRoot entry) Root (catalogComponent entry)) (catalogOrdinal entry)
placedCatalogCoverage placed entry member = placedBirthFromDecoded placed entry
  (scanCatalogBirth (bundleOffset (placedMember placed)) (placedBundleTrail placed) entry
    (replace {p = Elem entry} (sym (placedCatalogExact placed)) member))

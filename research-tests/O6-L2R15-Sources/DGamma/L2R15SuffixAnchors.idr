module DGamma.L2R15SuffixAnchors

import Builtin
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
import DGamma.L2R13NativeSuffixFrames
import DGamma.L2R15SuffixScans
import DGamma.L2R15ScanCongruence
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Anchor and key-forcing scans of the ACTUAL framed suffixes agree, from
||| native catalog and release transport. This is not a whole-run anchor
||| transport when a preceding crossing moves release ordinals or root cuts.
export
0 nativeSuffixAnchorKey : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {oldFirst, oldFinal, newFirst, newFinal : SystemState name key value world error} ->
  {oldTrace : Transitions oldFirst oldFinal} -> {newTrace : Transitions newFirst newFinal} ->
  (frames : NativeSuffixFrames nameEq keyEq oldTrace newTrace) ->
  (oldTrail : AvailabilityTrace name key world error value oldTrace) ->
  (newTrail : AvailabilityTrace name key world error value newTrace) -> (ordinal : Nat) ->
  (anchorOf nameEq keyEq oldTrail ordinal = anchorOf nameEq keyEq newTrail ordinal,
   keyForcedOrdinal nameEq keyEq oldTrail ordinal = keyForcedOrdinal nameEq keyEq newTrail ordinal)
nativeSuffixAnchorKey nameEq keyEq frames oldTrail newTrail ordinal =
  (trans (cong (\items => lastReleaseCut (concatMap
      (\seed => scanReleaseOrdinals nameEq keyEq (catalogComponent seed) 0 (catalogOrdinal seed) oldTrail)
      (filter (\seed => catalogOrdinal seed <= ordinal) items)))
      (nativeSuffixCatalog nameEq keyEq frames oldTrail newTrail 0))
    (cong lastReleaseCut (scanFoldPointwise
      (\acc, seed => acc ++ scanReleaseOrdinals nameEq keyEq (catalogComponent seed) 0 (catalogOrdinal seed) oldTrail)
      (\acc, seed => acc ++ scanReleaseOrdinals nameEq keyEq (catalogComponent seed) 0 (catalogOrdinal seed) newTrail)
      (\acc, seed => cong (acc ++) (nativeSuffixReleases nameEq keyEq frames oldTrail newTrail (catalogComponent seed) 0 (catalogOrdinal seed)))
      (filter (\seed => catalogOrdinal seed <= ordinal) (scanRootCatalog 0 newTrail)) [])),
   trans (cong (\items => any (\seed => catalogOrdinal seed == ordinal &&
      not (null (scanReleaseOrdinals nameEq keyEq (catalogComponent seed) 0 (catalogOrdinal seed) oldTrail))) items)
      (nativeSuffixCatalog nameEq keyEq frames oldTrail newTrail 0))
    (scanFoldPointwise
      (\acc, seed => acc || (catalogOrdinal seed == ordinal && not (null (scanReleaseOrdinals nameEq keyEq (catalogComponent seed) 0 (catalogOrdinal seed) oldTrail))))
      (\acc, seed => acc || (catalogOrdinal seed == ordinal && not (null (scanReleaseOrdinals nameEq keyEq (catalogComponent seed) 0 (catalogOrdinal seed) newTrail))))
      (\acc, seed => cong (\scanned => acc || (catalogOrdinal seed == ordinal && not (null scanned)))
        (nativeSuffixReleases nameEq keyEq frames oldTrail newTrail (catalogComponent seed) 0 (catalogOrdinal seed)))
      (scanRootCatalog 0 newTrail) False))

||| Exact suffix target transport includes BOTH same-anchor rank and the
||| external-order floor. No anchor-only simplification drops the floor.
||| The prefixed swapped-pair target transport is still a separate residue.
export
0 nativeSuffixTarget : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {oldFirst, oldFinal, newFirst, newFinal : SystemState name key value world error} ->
  {oldTrace : Transitions oldFirst oldFinal} -> {newTrace : Transitions newFirst newFinal} ->
  (frames : NativeSuffixFrames nameEq keyEq oldTrace newTrace) ->
  (oldTrail : AvailabilityTrace name key world error value oldTrace) ->
  (newTrail : AvailabilityTrace name key world error value newTrace) -> (ordinal : Nat) ->
  targetPosition nameEq keyEq oldTrail ordinal = targetPosition nameEq keyEq newTrail ordinal
nativeSuffixTarget nameEq keyEq frames oldTrail newTrail ordinal =
  cong2 max
    (cong2 (+) (cong (fromMaybe 0) (fst (nativeSuffixAnchorKey nameEq keyEq frames oldTrail newTrail ordinal)))
      (cong length (trans (cong (filter (\earlier => catalogOrdinal earlier < ordinal && anchorOf nameEq keyEq oldTrail (catalogOrdinal earlier) == anchorOf nameEq keyEq oldTrail ordinal)) (nativeSuffixCatalog nameEq keyEq frames oldTrail newTrail 0))
          (scanFilterPointwise (\earlier => catalogOrdinal earlier < ordinal && anchorOf nameEq keyEq oldTrail (catalogOrdinal earlier) == anchorOf nameEq keyEq oldTrail ordinal) (\earlier => catalogOrdinal earlier < ordinal && anchorOf nameEq keyEq newTrail (catalogOrdinal earlier) == anchorOf nameEq keyEq newTrail ordinal)
            (\earlier => cong2 (\left, right => catalogOrdinal earlier < ordinal && left == right)
              (fst (nativeSuffixAnchorKey nameEq keyEq frames oldTrail newTrail (catalogOrdinal earlier))) (fst (nativeSuffixAnchorKey nameEq keyEq frames oldTrail newTrail ordinal)))
            (scanRootCatalog 0 newTrail)))))
    (cong (\items => fromMaybe 0 (lastReleaseCut (map catalogOrdinal items))) (trans (cong (filter (\earlier => catalogOrdinal earlier < ordinal && not (anchorOf nameEq keyEq oldTrail (catalogOrdinal earlier) == anchorOf nameEq keyEq oldTrail ordinal))) (nativeSuffixCatalog nameEq keyEq frames oldTrail newTrail 0))
          (scanFilterPointwise (\earlier => catalogOrdinal earlier < ordinal && not (anchorOf nameEq keyEq oldTrail (catalogOrdinal earlier) == anchorOf nameEq keyEq oldTrail ordinal)) (\earlier => catalogOrdinal earlier < ordinal && not (anchorOf nameEq keyEq newTrail (catalogOrdinal earlier) == anchorOf nameEq keyEq newTrail ordinal))
            (\earlier => cong2 (\left, right => catalogOrdinal earlier < ordinal && not (left == right))
              (fst (nativeSuffixAnchorKey nameEq keyEq frames oldTrail newTrail (catalogOrdinal earlier))) (fst (nativeSuffixAnchorKey nameEq keyEq frames oldTrail newTrail ordinal)))
            (scanRootCatalog 0 newTrail))))

||| Eliminate the observed anchor-presence guard BEFORE transporting the
||| native distance. Target equality is relevant only in the anchored branch.
export
0 nativeDistanceAtAnchorGuard : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {oldFirst, oldFinal, newFirst, newFinal : SystemState name key value world error} ->
  {oldTrace : Transitions oldFirst oldFinal} -> {newTrace : Transitions newFirst newFinal} ->
  (oldTrail : AvailabilityTrace name key world error value oldTrace) ->
  (newTrail : AvailabilityTrace name key world error value newTrace) -> (ordinal : Nat) ->
  (seen : Bool) ->
  (0 oldGuard : isJust (anchorOf nameEq keyEq oldTrail ordinal) = seen) ->
  (0 newGuard : isJust (anchorOf nameEq keyEq newTrail ordinal) = seen) ->
  (0 target : targetPosition nameEq keyEq oldTrail ordinal = targetPosition nameEq keyEq newTrail ordinal) ->
  rootDistance nameEq keyEq oldTrail ordinal = rootDistance nameEq keyEq newTrail ordinal
nativeDistanceAtAnchorGuard nameEq keyEq oldTrail newTrail ordinal True oldGuard newGuard target =
  rewrite oldGuard in rewrite newGuard in cong (minus ordinal) target
nativeDistanceAtAnchorGuard nameEq keyEq oldTrail newTrail ordinal False oldGuard newGuard target =
  rewrite oldGuard in rewrite newGuard in Refl

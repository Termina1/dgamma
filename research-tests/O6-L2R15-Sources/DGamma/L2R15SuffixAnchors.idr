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

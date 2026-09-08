module DGamma.CP5O19CartesianNumericSpike

import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O19CartesianSitePlanSpike
import Data.List
import Data.List.Elem
import Data.Nat

%default total
%unbound_implicits off

||| Pull one final ordinal through an explicit actual site word, backwards
||| through the transpositions. This is the pointwise composed source map.
public export
o19SitesPull : List Nat -> Nat -> Nat
o19SitesPull [] position = position
o19SitesPull (point :: rest) position = fst (adjacentSwapOrdinalExhaustive point (o19SitesPull rest position))

||| Site concatenation composes ordinal pulls, pointwise and without
||| function extensionality or an independently chosen origin map.
export
0 o19SitesPullAppend : (first, second : List Nat) -> (position : Nat) ->
  (o19SitesPull (first ++ second) position = o19SitesPull first (o19SitesPull second position))
o19SitesPullAppend [] second position = Refl
o19SitesPullAppend (point :: rest) second position =
  cong (\source => fst (adjacentSwapOrdinalExhaustive point source)) (o19SitesPullAppend rest second position)

||| Execute two site words sequentially: the second consumes the ACTUAL
||| composed first-word pull. This is exact origin-list concatenation.
export
0 o19OriginsAtSitesAppend : (originalMap : Nat -> Nat) -> (first, second : List Nat) ->
  (o19OriginsAtSites originalMap (first ++ second) =
    o19OriginsAtSites originalMap first ++ o19OriginsAtSites (\position => originalMap (o19SitesPull first position)) second)
o19OriginsAtSitesAppend originalMap [] second = Refl
o19OriginsAtSitesAppend originalMap (point :: rest) second =
  cong ((originalMap point, originalMap (S point)) ::)
    (o19OriginsAtSitesAppend (\position => originalMap (fst (adjacentSwapOrdinalExhaustive point position))) rest second)

||| Closed-form ordinal pull for one right node rotated before width left
||| nodes at start. Prefix positions are fixed; the interval rotates right.
||| This simple executable form is proved equal to actual row sites below.
public export
o19RowPull : Nat -> Nat -> Nat -> Nat
o19RowPull Z Z position = position
o19RowPull Z (S width) Z = S width
o19RowPull Z (S width) (S Z) = Z
o19RowPull Z (S width) (S (S position)) = S (o19RowPull Z width (S position))
o19RowPull (S start) width Z = Z
o19RowPull (S start) width (S position) = S (o19RowPull start width position)

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

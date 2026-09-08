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

||| A zero-width row is pointwise identity, including every outside ordinal.
export
0 o19RowPullZero : (start, position : Nat) -> (o19RowPull start Z position = position)
o19RowPullZero Z position = Refl
o19RowPullZero (S start) Z = Refl
o19RowPullZero (S start) (S position) = cong S (o19RowPullZero start position)

||| One genuine adjacent ordinal transposition extends the smaller rotated
||| row. The proof consumes the exhaustive sealed relation, not a guessed
||| scalar evaluator equation, and inspects natural/region constructors.
export
0 o19RowPullStep : (start, width, position, source : Nat) ->
  AdjacentSwapOrdinalRelation start position source ->
  (o19RowPull (S start) width source = o19RowPull start (S width) position)
o19RowPullStep start width position _ (AdjacentPrefixOrdinal earlier) =
  case start of
    Z => void (uninhabited earlier)
    S previous => case position of
      Z => Refl
      S after => cong S (o19RowPullStep previous width after after (AdjacentPrefixOrdinal (fromLteSucc earlier)))
o19RowPullStep start width _ _ AdjacentMovedRightOrdinal =
  case start of
    Z => case width of
      Z => Refl
      S remaining => Refl
    S previous => cong S (o19RowPullStep previous width previous (S previous) AdjacentMovedRightOrdinal)
o19RowPullStep start width _ _ AdjacentMovedLeftOrdinal =
  case start of
    Z => Refl
    S previous => cong S (o19RowPullStep previous width (S previous) previous AdjacentMovedLeftOrdinal)
o19RowPullStep start width position _ (AdjacentSuffixOrdinal later) =
  case start of
    Z => case position of
      Z => void (uninhabited later)
      S Z => void (uninhabited (fromLteSucc later))
      S (S after) => Refl
    S previous => case position of
      Z => void (uninhabited later)
      S after => cong S (o19RowPullStep previous width after after (AdjacentSuffixOrdinal (fromLteSucc later)))

||| The exact descending row site word has the executable closed-form
||| rotation pull, at EVERY ordinal. This handles repeated labels and all
||| outside positions without any action-based or cardinality inference.
export
0 o19RowSitesPull : (start, width, position : Nat) ->
  (o19SitesPull (o19RowSites start width) position = o19RowPull start width position)
o19RowSitesPull start Z position = sym (o19RowPullZero start position)
o19RowSitesPull start (S width) position =
  trans (o19SitesPullAppend (o19RowSites (S start) width) [start] position)
    (trans (o19RowSitesPull (S start) width (fst (adjacentSwapOrdinalExhaustive start position)))
      (o19RowPullStep start width position (fst (adjacentSwapOrdinalExhaustive start position))
        (snd (adjacentSwapOrdinalExhaustive start position))))

||| Descending source pairs for a row. The right source is the original
||| end of the left interval. No whole Cartesian coverage is asserted here.
public export
o19RowPairs : Nat -> Nat -> List (Nat, Nat)
o19RowPairs start Z = []
o19RowPairs start (S width) = o19RowPairs (S start) width ++ [(start, start + S width)]

||| The ordinal immediately before a rotated row is unchanged.
export
0 o19RowPullBeforeEdge : (start, width : Nat) -> (o19RowPull (S start) width start = start)
o19RowPullBeforeEdge Z width = Refl
o19RowPullBeforeEdge (S start) width = cong S (o19RowPullBeforeEdge start width)

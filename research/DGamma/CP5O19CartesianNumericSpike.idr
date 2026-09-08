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

||| The moved-right node's source ordinal is the actual row interval end.
export
0 o19RowPullAtStart : (start, width : Nat) -> (o19RowPull start width start = start + width)
o19RowPullAtStart Z Z = Refl
o19RowPullAtStart Z (S width) = Refl
o19RowPullAtStart (S start) width = cong S (o19RowPullAtStart start width)

||| Exact source-coordinate list of the descending row sites, under ANY
||| original coordinate map. This derives the pair list from actual numeric
||| execution, not from cardinality or an assumed offset equation.
export
0 o19RowOriginPairs : (originalMap : Nat -> Nat) -> (start, width : Nat) ->
  (o19OriginsAtSites originalMap (o19RowSites start width) =
    map (\pair => (originalMap (fst pair), originalMap (snd pair))) (o19RowPairs start width))
o19RowOriginPairs originalMap start Z = Refl
o19RowOriginPairs originalMap start (S width) =
  trans (o19OriginsAtSitesAppend originalMap (o19RowSites (S start) width) [start])
    (trans (cong2 (++) (o19RowOriginPairs originalMap (S start) width)
      (cong (\pair => [pair])
        (cong2 MkPair
          (cong originalMap (trans (o19RowSitesPull (S start) width start) (o19RowPullBeforeEdge start width)))
          (cong originalMap (trans (o19RowSitesPull (S start) width (S start))
            (trans (o19RowPullAtStart (S start) width) (plusSuccRightSucc start width)))))))
      (sym (mapAppend (\pair => (originalMap (fst pair), originalMap (snd pair)))
        (o19RowPairs (S start) width) [(start, start + S width)])))

||| Inside the shifted left interval, the row pull recovers the original
||| left coordinate. The actual bound is consumed, not inferred from labels.
export
0 o19RowPullInside : (start, width, index : Nat) -> LTE (S index) width ->
  (o19RowPull start width (start + S index) = start + index)
o19RowPullInside start width index bound =
  case start of
    Z => case width of
      Z => void (uninhabited bound)
      S remaining => case index of
        Z => Refl
        S later => cong S (o19RowPullInside Z remaining later (fromLteSucc bound))
    S earlier => cong S (o19RowPullInside earlier width index bound)

||| Every coordinate beyond the rotated interval is fixed, with its exact
||| offset retained for the remaining right-column band.
export
0 o19RowPullBeyond : (start, width, index : Nat) ->
  (o19RowPull start width ((start + S width) + index) = (start + S width) + index)
o19RowPullBeyond Z Z index = Refl
o19RowPullBeyond Z (S width) index = cong S (o19RowPullBeyond Z width index)
o19RowPullBeyond (S start) width index = cong S (o19RowPullBeyond start width index)

||| Descending contiguous left coordinates against one fixed right source.
public export
o19FixedRowPairs : Nat -> Nat -> Nat -> List (Nat, Nat)
o19FixedRowPairs leftSource rightSource Z = []
o19FixedRowPairs leftSource rightSource (S width) =
  o19FixedRowPairs (S leftSource) rightSource width ++ [(leftSource, rightSource)]

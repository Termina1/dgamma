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

||| Identify the actual numeric row's right coordinate with its fixed source
||| end, including the successor/addition alignment at every left position.
export
0 o19RowPairsFixed : (start, width : Nat) ->
  (o19RowPairs start width = o19FixedRowPairs start (start + width) width)
o19RowPairsFixed start Z = Refl
o19RowPairsFixed start (S width) =
  cong (\pairs => pairs ++ [(start, start + S width)])
    (trans (o19RowPairsFixed (S start) width)
      (cong (\rightSource => o19FixedRowPairs (S start) rightSource width) (plusSuccRightSucc start width)))

||| Cartesian coordinates in the ACTUAL column order: descending left
||| rows, advancing original right coordinates. Certification follows later.
public export
o19GridPairs : Nat -> Nat -> Nat -> Nat -> List (Nat, Nat)
o19GridPairs leftSource rightSource width Z = []
o19GridPairs leftSource rightSource width (S height) =
  o19FixedRowPairs leftSource rightSource width ++ o19GridPairs leftSource (S rightSource) width height

||| Map the two coordinates separately using actual bounded left-band and
||| right-point equations. The bounded law is restricted structurally, so
||| no value outside the certified source interval is assumed.
export
0 o19FixedRowPairsMap : (leftMap, rightMap : Nat -> Nat) ->
  (sourceLeft, sourceRight, targetLeft, targetRight, width : Nat) ->
  (0 leftExact : (index : Nat) -> LTE (S index) width -> (leftMap (sourceLeft + index) = targetLeft + index)) ->
  (0 rightExact : rightMap sourceRight = targetRight) ->
  (map (\pair => (leftMap (fst pair), rightMap (snd pair))) (o19FixedRowPairs sourceLeft sourceRight width) =
    o19FixedRowPairs targetLeft targetRight width)
o19FixedRowPairsMap leftMap rightMap sourceLeft sourceRight targetLeft targetRight Z leftExact rightExact = Refl
o19FixedRowPairsMap leftMap rightMap sourceLeft sourceRight targetLeft targetRight (S width) leftExact rightExact =
  trans (mapAppend (\pair => (leftMap (fst pair), rightMap (snd pair)))
    (o19FixedRowPairs (S sourceLeft) sourceRight width) [(sourceLeft, sourceRight)])
    (cong2 (++)
      (o19FixedRowPairsMap leftMap rightMap (S sourceLeft) sourceRight (S targetLeft) targetRight width
        (\index, bound => trans (cong leftMap (plusSuccRightSucc sourceLeft index))
          (trans (leftExact (S index) (LTESucc bound)) (sym (plusSuccRightSucc targetLeft index)))) rightExact)
      (cong (\pair => [pair]) (cong2 MkPair
        (trans (cong leftMap (sym (plusZeroRightNeutral sourceLeft)))
          (trans (leftExact Z (LTESucc LTEZero)) (plusZeroRightNeutral targetLeft))) rightExact)))

||| Derive one numeric row's original pairs from its current left band and
||| actual right point. These are internal map invariants, not O19 inputs.
export
0 o19RowOriginFixed : (originalMap : Nat -> Nat) -> (start, width, leftSource, rightSource : Nat) ->
  (0 leftExact : (index : Nat) -> LTE (S index) width -> (originalMap (start + index) = leftSource + index)) ->
  (0 rightExact : originalMap (start + width) = rightSource) ->
  (o19OriginsAtSites originalMap (o19RowSites start width) = o19FixedRowPairs leftSource rightSource width)
o19RowOriginFixed originalMap start width leftSource rightSource leftExact rightExact =
  trans (o19RowOriginPairs originalMap start width)
    (trans (cong (map (\pair => (originalMap (fst pair), originalMap (snd pair)))) (o19RowPairsFixed start width))
      (o19FixedRowPairsMap originalMap originalMap start (start + width) leftSource rightSource width leftExact rightExact))

||| BOTH exact source-coordinate bands survive one whole row rotation.
||| The remaining right band advances by one; the left origins stay fixed.
||| All equations are produced from the actual inside/beyond pull laws.
export
0 o19RowBandsAfter : (originalMap : Nat -> Nat) -> (start, width, height, leftSource, rightSource : Nat) ->
  (0 leftExact : (index : Nat) -> LTE (S index) width -> (originalMap (start + index) = leftSource + index)) ->
  (0 rightExact : (index : Nat) -> LTE (S index) (S height) -> (originalMap ((start + width) + index) = rightSource + index)) ->
  (((index : Nat) -> LTE (S index) width ->
      (originalMap (o19RowPull start width ((S start) + index)) = leftSource + index)),
   ((index : Nat) -> LTE (S index) height ->
      (originalMap (o19RowPull start width (((S start) + width) + index)) = (S rightSource) + index)))
o19RowBandsAfter originalMap start width height leftSource rightSource leftExact rightExact =
  (\index, bound => trans
    (cong originalMap (trans (cong (o19RowPull start width) (plusSuccRightSucc start index)) (o19RowPullInside start width index bound)))
    (leftExact index bound),
   \index, bound => trans
    (cong originalMap
      (trans (cong (o19RowPull start width) (cong (\base => base + index) (plusSuccRightSucc start width)))
        (trans (o19RowPullBeyond start width index)
          (trans (cong (\base => base + index) (sym (plusSuccRightSucc start width)))
            (plusSuccRightSucc (start + width) index)))))
    (trans (rightExact (S index) (LTESucc bound)) (sym (plusSuccRightSucc rightSource index))))

||| Pointwise map equality suffices for numeric origin-list equality. No
||| function equality, extensionality axiom, or extra site premise is used.
export
0 o19OriginsAtSitesPointwise : (firstMap, secondMap : Nat -> Nat) ->
  (0 exact : (position : Nat) -> firstMap position = secondMap position) -> (sites : List Nat) ->
  (o19OriginsAtSites firstMap sites = o19OriginsAtSites secondMap sites)
o19OriginsAtSitesPointwise firstMap secondMap exact [] = Refl
o19OriginsAtSitesPointwise firstMap secondMap exact (point :: rest) =
  cong2 (::) (cong2 MkPair (exact point) (exact (S point)))
    (o19OriginsAtSitesPointwise
      (\position => firstMap (fst (adjacentSwapOrdinalExhaustive point position)))
      (\position => secondMap (fst (adjacentSwapOrdinalExhaustive point position)))
      (\position => exact (fst (adjacentSwapOrdinalExhaustive point position))) rest)

||| FULL numeric Cartesian equality from the TWO bounded current-map
||| bands. Every row pair and every next band is produced by the actual
||| rotation; height induction yields the explicit grid enumeration.
export
0 o19NumericColumnGrid : (originalMap : Nat -> Nat) -> (start, width, height, leftSource, rightSource : Nat) ->
  (0 leftExact : (index : Nat) -> LTE (S index) width -> (originalMap (start + index) = leftSource + index)) ->
  (0 rightExact : (index : Nat) -> LTE (S index) height -> (originalMap ((start + width) + index) = rightSource + index)) ->
  (o19OriginsAtSites originalMap (o19ColumnSites start width height) = o19GridPairs leftSource rightSource width height)
o19NumericColumnGrid originalMap start width Z leftSource rightSource leftExact rightExact = Refl
o19NumericColumnGrid originalMap start width (S height) leftSource rightSource leftExact rightExact =
  trans (o19OriginsAtSitesAppend originalMap (o19RowSites start width) (o19ColumnSites (S start) width height))
    (cong2 (++)
      (o19RowOriginFixed originalMap start width leftSource rightSource leftExact
        (trans (cong originalMap (sym (plusZeroRightNeutral (start + width))))
          (trans (rightExact Z (LTESucc LTEZero)) (plusZeroRightNeutral rightSource))))
      (trans
        (o19OriginsAtSitesPointwise
          (\position => originalMap (o19SitesPull (o19RowSites start width) position))
          (\position => originalMap (o19RowPull start width position))
          (\position => cong originalMap (o19RowSitesPull start width position))
          (o19ColumnSites (S start) width height))
        (o19NumericColumnGrid (\position => originalMap (o19RowPull start width position)) (S start) width height leftSource (S rightSource)
          (fst (o19RowBandsAfter originalMap start width height leftSource rightSource leftExact rightExact))
          (snd (o19RowBandsAfter originalMap start width height leftSource rightSource leftExact rightExact)))))

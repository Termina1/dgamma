module DGamma.CP5O19GridCertificationSpike

import DGamma.Coeffects
import DGamma.CP5O19CartesianNumericSpike
import Data.List
import Data.List.Elem
import Data.Nat

%default total
%unbound_implicits off

||| Eliminate actual append membership directly, without producing a nested
||| sum/existential view. This is the row/column certification boundary.
export
0 o19ElemAppendCases : {item : Type} -> {point : item} -> {result : Type} ->
  (first, second : List item) ->
  (Elem point first -> result) -> (Elem point second -> result) ->
  Elem point (first ++ second) -> result
o19ElemAppendCases [] second inFirst inSecond member = inSecond member
o19ElemAppendCases (head :: rest) second inFirst inSecond Here = inFirst Here
o19ElemAppendCases (head :: rest) second inFirst inSecond (There member) =
  o19ElemAppendCases rest second (\later => inFirst (There later)) inSecond member

||| Both append injections, proved on the actual first-list spine.
export
0 o19ElemAppendInjections : {item : Type} -> {point : item} ->
  (first, second : List item) ->
  ((Elem point first -> Elem point (first ++ second)),
   (Elem point second -> Elem point (first ++ second)))
o19ElemAppendInjections [] second = (\member => void (uninhabited member), id)
o19ElemAppendInjections (head :: rest) second =
  (\member => case member of
    Here => Here
    There later => There (fst (o19ElemAppendInjections rest second) later),
   \member => There (snd (o19ElemAppendInjections rest second) member))

||| Concatenate unique lists only with an actual disjoint-membership proof.
export
0 o19UniqueAppend : {item : Type} -> (first, second : List item) ->
  UniqueKeys first -> UniqueKeys second ->
  ((point : item) -> Elem point first -> Not (Elem point second)) ->
  UniqueKeys (first ++ second)
o19UniqueAppend [] second UniqueNil secondUnique disjoint = secondUnique
o19UniqueAppend (head :: rest) second (UniqueCons absent restUnique) secondUnique disjoint =
  UniqueCons
    (o19ElemAppendCases rest second absent (disjoint head Here))
    (o19UniqueAppend rest second restUnique secondUnique
      (\point, member => disjoint point (There member)))

||| Every bounded left coordinate occurs in the fixed-right descending row.
export
0 o19FixedRowComplete : (leftSource, rightSource, width, index : Nat) ->
  LTE (S index) width ->
  Elem (leftSource + index, rightSource) (o19FixedRowPairs leftSource rightSource width)
o19FixedRowComplete leftSource rightSource Z index bound = void (uninhabited bound)
o19FixedRowComplete leftSource rightSource (S width) Z bound =
  replace {p = \point => Elem (point, rightSource) (o19FixedRowPairs leftSource rightSource (S width))}
    (sym (plusZeroRightNeutral leftSource))
    (snd (o19ElemAppendInjections (o19FixedRowPairs (S leftSource) rightSource width) [(leftSource, rightSource)]) Here)
o19FixedRowComplete leftSource rightSource (S width) (S index) bound =
  replace {p = \point => Elem (point, rightSource) (o19FixedRowPairs leftSource rightSource (S width))}
    (plusSuccRightSucc leftSource index)
    (fst (o19ElemAppendInjections (o19FixedRowPairs (S leftSource) rightSource width) [(leftSource, rightSource)])
      (o19FixedRowComplete (S leftSource) rightSource width index (fromLteSucc bound)))

||| Actual row membership gives BOTH left bounds and the exact fixed right
||| coordinate. No conclusion is drawn from cardinality or action labels.
export
0 o19FixedRowBounds : (leftSource, rightSource, width, leftPosition, rightPosition : Nat) ->
  Elem (leftPosition, rightPosition) (o19FixedRowPairs leftSource rightSource width) ->
  (LTE leftSource leftPosition,
   (LTE (S leftPosition) (leftSource + width), (rightPosition = rightSource)))
o19FixedRowBounds leftSource rightSource Z leftPosition rightPosition member = void (uninhabited member)
o19FixedRowBounds leftSource rightSource (S width) leftPosition rightPosition member =
  o19ElemAppendCases (o19FixedRowPairs (S leftSource) rightSource width) [(leftSource, rightSource)]
    (\earlier =>
      (lteSuccLeft (fst (o19FixedRowBounds (S leftSource) rightSource width leftPosition rightPosition earlier)),
       (replace {p = LTE (S leftPosition)} (plusSuccRightSucc leftSource width)
          (fst (snd (o19FixedRowBounds (S leftSource) rightSource width leftPosition rightPosition earlier))),
        snd (snd (o19FixedRowBounds (S leftSource) rightSource width leftPosition rightPosition earlier)))))
    (\last => case last of
      Here => (reflexive,
        (replace {p = LTE (S leftSource)} (plusSuccRightSucc leftSource width)
          (LTESucc (lteAddRight leftSource)), Refl))
      There absent => void (uninhabited absent)) member

||| Every fixed-right row has unique PAIRS: its final left coordinate is
||| strictly below every coordinate in the recursive row.
export
0 o19FixedRowUnique : (leftSource, rightSource, width : Nat) ->
  UniqueKeys (o19FixedRowPairs leftSource rightSource width)
o19FixedRowUnique leftSource rightSource Z = UniqueNil
o19FixedRowUnique leftSource rightSource (S width) =
  o19UniqueAppend (o19FixedRowPairs (S leftSource) rightSource width) [(leftSource, rightSource)]
    (o19FixedRowUnique (S leftSource) rightSource width)
    (UniqueCons (\member => uninhabited member) UniqueNil)
    (\pair, earlier, last => case last of
      Here => succNotLTEpred (fst (o19FixedRowBounds (S leftSource) rightSource width leftSource rightSource earlier))
      There absent => void (uninhabited absent))

||| Every bounded Cartesian pair occurs, by the actual right-coordinate
||| column induction and fixed-row membership, not by product cardinality.
export
0 o19GridComplete : (leftSource, rightSource, width, height, leftIndex, rightIndex : Nat) ->
  LTE (S leftIndex) width -> LTE (S rightIndex) height ->
  Elem (leftSource + leftIndex, rightSource + rightIndex) (o19GridPairs leftSource rightSource width height)
o19GridComplete leftSource rightSource width Z leftIndex rightIndex leftBound rightBound = void (uninhabited rightBound)
o19GridComplete leftSource rightSource width (S height) leftIndex Z leftBound rightBound =
  replace {p = \point => Elem (leftSource + leftIndex, point) (o19GridPairs leftSource rightSource width (S height))}
    (sym (plusZeroRightNeutral rightSource))
    (fst (o19ElemAppendInjections (o19FixedRowPairs leftSource rightSource width) (o19GridPairs leftSource (S rightSource) width height))
      (o19FixedRowComplete leftSource rightSource width leftIndex leftBound))
o19GridComplete leftSource rightSource width (S height) leftIndex (S rightIndex) leftBound rightBound =
  replace {p = \point => Elem (leftSource + leftIndex, point) (o19GridPairs leftSource rightSource width (S height))}
    (plusSuccRightSucc rightSource rightIndex)
    (snd (o19ElemAppendInjections (o19FixedRowPairs leftSource rightSource width) (o19GridPairs leftSource (S rightSource) width height))
      (o19GridComplete leftSource (S rightSource) width height leftIndex rightIndex leftBound (fromLteSucc rightBound)))

||| Every actual grid member lies in BOTH shifted half-open intervals.
||| The lower right bound is also the disjointness invariant for columns.
export
0 o19GridBounds : (leftSource, rightSource, width, height, leftPosition, rightPosition : Nat) ->
  Elem (leftPosition, rightPosition) (o19GridPairs leftSource rightSource width height) ->
  ((LTE leftSource leftPosition, LTE (S leftPosition) (leftSource + width)),
   (LTE rightSource rightPosition, LTE (S rightPosition) (rightSource + height)))
o19GridBounds leftSource rightSource width Z leftPosition rightPosition member = void (uninhabited member)
o19GridBounds leftSource rightSource width (S height) leftPosition rightPosition member =
  o19ElemAppendCases (o19FixedRowPairs leftSource rightSource width) (o19GridPairs leftSource (S rightSource) width height)
    (\row =>
      ((fst (o19FixedRowBounds leftSource rightSource width leftPosition rightPosition row),
        fst (snd (o19FixedRowBounds leftSource rightSource width leftPosition rightPosition row))),
       replace {p = \point => (LTE rightSource point, LTE (S point) (rightSource + S height))}
         (sym (snd (snd (o19FixedRowBounds leftSource rightSource width leftPosition rightPosition row))))
         (reflexive, replace {p = LTE (S rightSource)} (plusSuccRightSucc rightSource height) (LTESucc (lteAddRight rightSource)))))
    (\columns =>
      (fst (o19GridBounds leftSource (S rightSource) width height leftPosition rightPosition columns),
       (lteSuccLeft (fst (snd (o19GridBounds leftSource (S rightSource) width height leftPosition rightPosition columns))),
        replace {p = LTE (S rightPosition)} (plusSuccRightSucc rightSource height)
          (snd (snd (o19GridBounds leftSource (S rightSource) width height leftPosition rightPosition columns)))))) member

||| Pair uniqueness for the complete grid. The current row's exact right
||| coordinate is strictly below every remaining column's lower right bound.
export
0 o19GridUnique : (leftSource, rightSource, width, height : Nat) ->
  UniqueKeys (o19GridPairs leftSource rightSource width height)
o19GridUnique leftSource rightSource width Z = UniqueNil
o19GridUnique leftSource rightSource width (S height) =
  o19UniqueAppend (o19FixedRowPairs leftSource rightSource width) (o19GridPairs leftSource (S rightSource) width height)
    (o19FixedRowUnique leftSource rightSource width)
    (o19GridUnique leftSource (S rightSource) width height)
    (\(leftPosition, rightPosition), row, columns =>
      succNotLTEpred
        (replace {p = LTE (S rightSource)}
          (snd (snd (o19FixedRowBounds leftSource rightSource width leftPosition rightPosition row)))
          (fst (snd (o19GridBounds leftSource (S rightSource) width height leftPosition rightPosition columns)))))

||| Exactly the three local-grid fields required by WholeBlockSwapDerivation.
||| The list is the AUTHENTIC numeric grid, not a caller-selected enumeration.
public export
record O19GridCertificate (width, height : Nat) where
  constructor MkO19GridCertificate
  0 gridEveryPair : (leftPosition, rightPosition : Nat) ->
    LTE (S leftPosition) width -> LTE (S rightPosition) height ->
    Elem (leftPosition, rightPosition) (o19GridPairs Z Z width height)
  0 gridEveryMember : (leftPosition, rightPosition : Nat) ->
    Elem (leftPosition, rightPosition) (o19GridPairs Z Z width height) ->
    (LTE (S leftPosition) width, LTE (S rightPosition) height)
  0 gridPairsUnique : UniqueKeys (o19GridPairs Z Z width height)

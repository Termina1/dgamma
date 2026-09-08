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

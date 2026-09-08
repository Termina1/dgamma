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

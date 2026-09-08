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

module DGamma.L2R15ScanCongruence

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Data.List

%default total
%unbound_implicits off

||| Pointwise native accumulator transport, without function extensionality.
||| Covers the ACTUAL library any/concatMap folds used by phase scans.
export
0 scanFoldPointwise : {item, accumulator : Type} ->
  (oldStep, newStep : accumulator -> item -> accumulator) ->
  (0 same : (acc : accumulator) -> (entry : item) -> oldStep acc entry = newStep acc entry) ->
  (items : List item) -> (start : accumulator) ->
  foldl oldStep start items = foldl newStep start items
scanFoldPointwise oldStep newStep same [] start = Refl
scanFoldPointwise oldStep newStep same (entry :: items) start =
  trans (cong (\next => foldl oldStep next items) (same start entry))
    (scanFoldPointwise oldStep newStep same items (newStep start entry))

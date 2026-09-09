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

||| Pointwise map transport for native catalog distance contributions.
export
0 scanMapPointwise : {item, result : Type} -> (oldMap, newMap : item -> result) ->
  (0 same : (entry : item) -> oldMap entry = newMap entry) -> (items : List item) ->
  map oldMap items = map newMap items
scanMapPointwise oldMap newMap same [] = Refl
scanMapPointwise oldMap newMap same (entry :: items) =
  cong2 (::) (same entry) (scanMapPointwise oldMap newMap same items)

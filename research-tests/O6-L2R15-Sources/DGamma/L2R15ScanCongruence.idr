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

||| Native filter transport only AFTER observing its head Bool. Both
||| predicates are tied to that observation; the tail equation is structural.
export
0 scanFilterAtGuard : {item : Type} -> (oldTest, newTest : item -> Bool) ->
  (entry : item) -> (items : List item) -> (seen : Bool) ->
  (0 oldHead : oldTest entry = seen) -> (0 newHead : newTest entry = seen) ->
  (0 tail : filter oldTest items = filter newTest items) ->
  filter oldTest (entry :: items) = filter newTest (entry :: items)
scanFilterAtGuard oldTest newTest entry items True oldHead newHead tail =
  rewrite oldHead in rewrite newHead in cong (entry ::) tail
scanFilterAtGuard oldTest newTest entry items False oldHead newHead tail =
  rewrite oldHead in rewrite newHead in tail

||| Pointwise native filter transport via the observed-head bridge. The
||| parent proof recurses only on the list and supplies the guard equation.
export
0 scanFilterPointwise : {item : Type} -> (oldTest, newTest : item -> Bool) ->
  (0 same : (entry : item) -> oldTest entry = newTest entry) -> (items : List item) ->
  filter oldTest items = filter newTest items
scanFilterPointwise oldTest newTest same [] = Refl
scanFilterPointwise oldTest newTest same (entry :: items) =
  scanFilterAtGuard oldTest newTest entry items (newTest entry) (same entry) Refl
    (scanFilterPointwise oldTest newTest same items)

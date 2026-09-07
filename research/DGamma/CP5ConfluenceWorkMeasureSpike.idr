module DGamma.CP5ConfluenceWorkMeasureSpike

import Data.List
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Contribution of one pair in the whole fixed-rank ownership word.
public export
rankCrossing : Nat -> Nat -> Nat
rankCrossing Z right = Z
rankCrossing (S left) Z = 1
rankCrossing (S left) (S right) = rankCrossing left right

||| All inversions, not a debt that resets when the selected actor changes.
public export
rankInversions : List Nat -> Nat
rankInversions [] = Z
rankInversions (actor :: later) =
  sum (map (rankCrossing actor) later) + rankInversions later

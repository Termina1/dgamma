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
  foldr (+) Z (map (rankCrossing actor) later) + rankInversions later

||| Readable reassociation used for every unaffected third-node contribution.
export
0 rankPlusSwap : (a, b, c : Nat) -> a + (b + c) = b + (a + c)
rankPlusSwap a b c =
  trans (plusAssociative a b c)
    (trans (cong (\combined => combined + c) (plusCommutative a b))
      (sym (plusAssociative b a c)))

||| An inversion cannot also be an inversion in the opposite orientation.
export
0 rankCrossingAsymmetric :
  (left, right : Nat) -> rankCrossing left right = 1 ->
  rankCrossing right left = Z
rankCrossingAsymmetric Z right crossed = absurd crossed
rankCrossingAsymmetric (S left) Z crossed = Refl
rankCrossingAsymmetric (S left) (S right) crossed =
  rankCrossingAsymmetric left right crossed

||| Swapping a descending head pair removes exactly one global inversion.
export
0 rankHeadInversionDrop :
  (left, right : Nat) -> (suffix : List Nat) ->
  rankCrossing left right = 1 ->
  rankInversions (left :: right :: suffix) =
    S (rankInversions (right :: left :: suffix))
rankHeadInversionDrop left right suffix crossed =
  rewrite crossed in
  rewrite rankCrossingAsymmetric left right crossed in
    cong S (rankPlusSwap (foldr (+) Z (map (rankCrossing left) suffix))
      (foldr (+) Z (map (rankCrossing right) suffix)) (rankInversions suffix))

||| A concrete adjacent choice and its global measure are constructed together.
||| No arbitrary smaller word can inhabit this packet: the target is the exact
||| transposition at the stored source decomposition.
public export
record RankedAdjacentProgress (source : List Nat) where
  constructor MkRankedAdjacentProgress
  rankedPrefix : List Nat
  rankedLeft : Nat
  rankedRight : Nat
  rankedSuffix : List Nat
  0 rankedSourceExact : source = rankedPrefix ++ rankedLeft :: rankedRight :: rankedSuffix
  0 rankedWeightsExact : (pivot : Nat) ->
    foldr (+) Z (map (rankCrossing pivot) source) =
    foldr (+) Z (map (rankCrossing pivot)
      (rankedPrefix ++ rankedRight :: rankedLeft :: rankedSuffix))
  0 rankedGlobalDecrease : rankInversions source =
    S (rankInversions (rankedPrefix ++ rankedRight :: rankedLeft :: rankedSuffix))

||| Primitive ordering-first choice; the only input is the local rank descent.
export
rankHeadProgress :
  (left, right : Nat) -> (suffix : List Nat) ->
  (0 crossed : rankCrossing left right = 1) ->
  RankedAdjacentProgress (left :: right :: suffix)
rankHeadProgress left right suffix crossed =
  MkRankedAdjacentProgress [] left right suffix Refl
    (\pivot => rankPlusSwap (rankCrossing pivot left) (rankCrossing pivot right)
      (foldr (+) Z (map (rankCrossing pivot) suffix)))
    (rankHeadInversionDrop left right suffix crossed)

||| Lift the choice through an untouched head while extending the GLOBAL proof.
export
rankLiftProgress :
  (head : Nat) -> (source : List Nat) -> RankedAdjacentProgress source ->
  RankedAdjacentProgress (head :: source)
rankLiftProgress head source
  (MkRankedAdjacentProgress prior left right suffix exact weights decreased) =
    MkRankedAdjacentProgress (head :: prior) left right suffix
      (cong (head ::) exact)
      (\pivot => cong (rankCrossing pivot head +) (weights pivot))
      (rewrite weights head in
       rewrite decreased in
         sym (plusSuccRightSucc
           (foldr (+) Z (map (rankCrossing head) (prior ++ right :: left :: suffix)))
           (rankInversions (prior ++ right :: left :: suffix))))

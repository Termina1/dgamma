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

||| Select the first rank descent while building its global decrease packet.
||| Nothing is a blocked/no-descent observation, not a canonical-form proof.
export
rankSelectProgress : (source : List Nat) -> Maybe (RankedAdjacentProgress source)
rankSelectProgress [] = Nothing
rankSelectProgress [single] = Nothing
rankSelectProgress (left :: right :: suffix) =
  case decEq (rankCrossing left right) 1 of
    Yes crossed => Just (rankHeadProgress left right suffix crossed)
    No notDescending => map (rankLiftProgress left (right :: suffix))
      (rankSelectProgress (right :: suffix))

||| A genuine local R175 transposition within exactly one owned segment.
||| Earlier barriers/segments are retained structurally, not discarded by a
||| scalar smaller-measure premise. The target is indexed by the stored choice.
public export
data SegmentedRankProgress : List (List Nat) -> List (List Nat) -> Type where
  FirstRankSegment :
    {sourceHead : List Nat} ->
    (0 later : List (List Nat)) -> (0 progress : RankedAdjacentProgress sourceHead) ->
    SegmentedRankProgress (sourceHead :: later)
      ((rankedPrefix progress ++ rankedRight progress :: rankedLeft progress :: rankedSuffix progress) :: later)
  LaterRankSegment :
    {source, target : List (List Nat)} ->
    (0 untouched : List Nat) -> (0 later : SegmentedRankProgress source target) ->
    SegmentedRankProgress (untouched :: source) (untouched :: target)

||| A local segment choice strictly decreases the WHOLE segmented sum, even
||| behind arbitrarily many unchanged barriers and earlier owned segments.
export
0 segmentedRankProgressDrops :
  {source, target : List (List Nat)} -> (SegmentedRankProgress source target) ->
  (foldr (+) Z (map rankInversions source) = S (foldr (+) Z (map rankInversions target)))
segmentedRankProgressDrops (FirstRankSegment later progress) =
  cong (\count => count + foldr (+) Z (map rankInversions later)) (rankedGlobalDecrease progress)
segmentedRankProgressDrops (LaterRankSegment {target} untouched later) =
  trans (cong (rankInversions untouched +) (segmentedRankProgressDrops later))
    (sym (plusSuccRightSucc (rankInversions untouched) (foldr (+) Z (map rankInversions target))))

||| The lifted target equation is proved where the opaque producer is owned.
||| Consumers use this equation instead of unfolding a proof-bearing packet.
export
0 rankLiftTargetExact :
  (head : Nat) -> (source : List Nat) -> (progress : RankedAdjacentProgress source) ->
  ((rankedPrefix (rankLiftProgress head source progress) ++
      rankedRight (rankLiftProgress head source progress) ::
      rankedLeft (rankLiftProgress head source progress) ::
      rankedSuffix (rankLiftProgress head source progress)) =
   (head :: (rankedPrefix progress ++ rankedRight progress :: rankedLeft progress :: rankedSuffix progress)))
rankLiftTargetExact head source
  (MkRankedAdjacentProgress prior left right suffix exact weights decreased) = Refl

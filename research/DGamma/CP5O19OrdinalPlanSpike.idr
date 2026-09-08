module DGamma.CP5O19OrdinalPlanSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5UniqueRawNameOrdinalCapital
import DGamma.CP5O19AdjacentReplayProducerSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| The sealed numeric adjacent transposition is its own inverse. This is
||| ordinal-only, so equal action labels never identify distinct occurrences.
export
0 o19AdjacentOrdinalSymmetric :
  {point, target, source : Nat} -> AdjacentSwapOrdinalRelation point target source ->
  AdjacentSwapOrdinalRelation point source target
o19AdjacentOrdinalSymmetric (AdjacentPrefixOrdinal earlier) = AdjacentPrefixOrdinal earlier
o19AdjacentOrdinalSymmetric AdjacentMovedRightOrdinal = AdjacentMovedLeftOrdinal
o19AdjacentOrdinalSymmetric AdjacentMovedLeftOrdinal = AdjacentMovedRightOrdinal
o19AdjacentOrdinalSymmetric (AdjacentSuffixOrdinal later) = AdjacentSuffixOrdinal later

||| An ACTUAL sealed node's origin ordinal agrees with the executable
||| four-region classifier. Source-position uniqueness is not action equality.
export
0 o19AdjacentSourceOrdinalExact :
  (point, target, source : Nat) -> AdjacentSwapOrdinalRelation point target source ->
  (source = fst (adjacentSwapOrdinalExhaustive point target))
o19AdjacentSourceOrdinalExact point target source relation =
  uniqueAdjacentOrdinalInjective point source (fst (adjacentSwapOrdinalExhaustive point target)) target target
    (o19AdjacentOrdinalSymmetric relation)
    (o19AdjacentOrdinalSymmetric (snd (adjacentSwapOrdinalExhaustive point target))) Refl

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

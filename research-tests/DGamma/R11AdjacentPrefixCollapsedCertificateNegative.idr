module DGamma.R11AdjacentPrefixCollapsedCertificateNegative

import DGamma.CP5ConfluenceLocalDiamondSpike
import Data.Nat

%default total

||| Expected failure: a malicious certificate cannot label a strict-prefix
||| target with a different/collapsed source ordinal.
public export
0 collapsedPrefixCannotInhabitOrdinalCertificate :
  LT targetOrdinal prefixCount ->
  Not (sourceOrdinal = targetOrdinal) ->
  AdjacentSwapOrdinalRelation prefixCount targetOrdinal sourceOrdinal
collapsedPrefixCannotInhabitOrdinalCertificate before distinct =
  AdjacentPrefixOrdinal before

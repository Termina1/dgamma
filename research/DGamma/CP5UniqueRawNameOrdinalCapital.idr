module DGamma.CP5UniqueRawNameOrdinalCapital

import DGamma.CP5ConfluenceLocalDiamondSpike
import Data.Nat

%default total
%unbound_implicits off

||| The sealed all-action adjacent ordinal relation cannot collapse positions.
export
0 uniqueAdjacentOrdinalInjective :
  (point, leftTarget, rightTarget, leftSource, rightSource : Nat) ->
  AdjacentSwapOrdinalRelation point leftTarget leftSource ->
  AdjacentSwapOrdinalRelation point rightTarget rightSource ->
  (leftSource = rightSource) -> (leftTarget = rightTarget)
uniqueAdjacentOrdinalInjective point _ _ _ _ (AdjacentPrefixOrdinal leftBefore) (AdjacentPrefixOrdinal rightBefore) same =
  same
uniqueAdjacentOrdinalInjective point _ _ _ _ (AdjacentPrefixOrdinal leftBefore) AdjacentMovedRightOrdinal same =
  void (adjacentPrefixNotMovedLeft (replace {p = \position => LT position point} same leftBefore))
uniqueAdjacentOrdinalInjective point _ _ _ _ (AdjacentPrefixOrdinal leftBefore) AdjacentMovedLeftOrdinal same =
  void (adjacentPrefixNotMovedRight (replace {p = \position => LT position point} same leftBefore))
uniqueAdjacentOrdinalInjective point _ _ _ _ (AdjacentPrefixOrdinal leftBefore) (AdjacentSuffixOrdinal rightAfter) same =
  same
uniqueAdjacentOrdinalInjective point _ _ _ _ AdjacentMovedRightOrdinal (AdjacentPrefixOrdinal rightBefore) same =
  void (adjacentPrefixNotMovedLeft (replace {p = \position => LT position point} (sym same) rightBefore))
uniqueAdjacentOrdinalInjective point _ _ _ _ AdjacentMovedRightOrdinal AdjacentMovedRightOrdinal same =
  Refl
uniqueAdjacentOrdinalInjective point _ _ _ _ AdjacentMovedRightOrdinal AdjacentMovedLeftOrdinal same =
  void (succNotLTEpred (replace {p = LTE (S point)} same reflexive))
uniqueAdjacentOrdinalInjective point _ _ _ _ AdjacentMovedRightOrdinal (AdjacentSuffixOrdinal rightAfter) same =
  void (adjacentMovedLeftNotSuffix (replace {p = LTE (S (S point))} (sym same) rightAfter))
uniqueAdjacentOrdinalInjective point _ _ _ _ AdjacentMovedLeftOrdinal (AdjacentPrefixOrdinal rightBefore) same =
  void (adjacentPrefixNotMovedRight (replace {p = \position => LT position point} (sym same) rightBefore))
uniqueAdjacentOrdinalInjective point _ _ _ _ AdjacentMovedLeftOrdinal AdjacentMovedRightOrdinal same =
  void (succNotLTEpred (replace {p = LTE (S point)} (sym same) reflexive))
uniqueAdjacentOrdinalInjective point _ _ _ _ AdjacentMovedLeftOrdinal AdjacentMovedLeftOrdinal same =
  Refl
uniqueAdjacentOrdinalInjective point _ _ _ _ AdjacentMovedLeftOrdinal (AdjacentSuffixOrdinal rightAfter) same =
  void (adjacentMovedRightNotSuffix (replace {p = LTE (S (S point))} (sym same) rightAfter))
uniqueAdjacentOrdinalInjective point _ _ _ _ (AdjacentSuffixOrdinal leftAfter) (AdjacentPrefixOrdinal rightBefore) same =
  same
uniqueAdjacentOrdinalInjective point _ _ _ _ (AdjacentSuffixOrdinal leftAfter) AdjacentMovedRightOrdinal same =
  void (adjacentMovedLeftNotSuffix (replace {p = LTE (S (S point))} same leftAfter))
uniqueAdjacentOrdinalInjective point _ _ _ _ (AdjacentSuffixOrdinal leftAfter) AdjacentMovedLeftOrdinal same =
  void (adjacentMovedRightNotSuffix (replace {p = LTE (S (S point))} same leftAfter))
uniqueAdjacentOrdinalInjective point _ _ _ _ (AdjacentSuffixOrdinal leftAfter) (AdjacentSuffixOrdinal rightAfter) same =
  same

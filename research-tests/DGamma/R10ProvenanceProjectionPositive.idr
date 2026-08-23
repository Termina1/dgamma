module DGamma.R10ProvenanceProjectionPositive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import Decidable.Equality

%default total

public export
0 actualSwapMapIsOperationalFold :
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
    original tracePrefix left right suffix diamond) ->
  swappedOccurrenceCorrespondence result =
    operationalOccurrenceCorrespondence (swappedOccurrenceFold result)
actualSwapMapIsOperationalFold result = Refl

public export
0 coreMapIsRecursiveDeletionFold :
  (core : ClosingFreeTraceCore name key world error value protocol nameEq keyEq
    original) ->
  coreOccurrenceCorrespondence core =
    closingFreeDeletionOccurrenceFold (coreDeletionDerivation core)
coreMapIsRecursiveDeletionFold core = Refl

public export
0 reductionMapIsRecursiveDeletionFold :
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  reductionOccurrenceCorrespondence reduction =
    closingFreeDeletionOccurrenceFold (reductionDeletionDerivation reduction)
reductionMapIsRecursiveDeletionFold reduction = Refl

public export
0 sortingMapIsAdjacentDerivationFold :
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq keyEq
    original ordering) ->
  sortingOccurrenceCorrespondence sorted =
    finiteDerivationOccurrenceCorrespondence (sortingAdjacentDerivation sorted)
sortingMapIsAdjacentDerivationFold sorted = Refl

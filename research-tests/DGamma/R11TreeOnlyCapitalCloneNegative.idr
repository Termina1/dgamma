module DGamma.R11TreeOnlyCapitalCloneNegative

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import Decidable.Equality

%default total

public export
0 replaceOnlyCapitalSchedule :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  (replacement : CanonicalSchedule name key world error value protocol nameEq keyEq
    original) ->
  IndependentCanonicalSchedule name key world error value protocol nameEq keyEq
    original
replaceOnlyCapitalSchedule capital replacement =
  MkIndependentCanonicalSchedule
    (capitalPremises capital)
    (capitalReduction capital)
    (capitalOrdering capital)
    (capitalSorted capital)
    (capitalSupportTransport capital)
    (capitalAccounting capital)
    replacement
    (capitalCanonicalScheduleExact capital)
    (capitalWithdrawnClassified capital)

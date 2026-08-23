module DGamma.R10SortedMapCloneNegative

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import Decidable.Equality

%default total

||| Expected failure before accounting: sorting exposes only the fold over its
||| concrete finite adjacent-swap derivation.
public export
0 replaceSortedOccurrenceMap :
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq keyEq
    original ordering) ->
  (alternate : ActionRegistrationReplayCorrespondence name key world error value
    original (sortedTrace sorted)) ->
  sortingOccurrenceCorrespondence sorted = alternate
replaceSortedOccurrenceMap sorted alternate = Refl

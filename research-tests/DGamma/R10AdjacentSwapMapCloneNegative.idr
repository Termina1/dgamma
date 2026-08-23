module DGamma.R10AdjacentSwapMapCloneNegative

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

||| Expected failure: an actual result's map is definitionally selected by its
||| exact operational suffix fold, not by `alternate`.
public export
0 replaceActualSwapOccurrenceMap :
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
    original tracePrefix left right suffix diamond) ->
  (alternate : ActionRegistrationReplayCorrespondence name key world error value
    original (swappedTrace result)) ->
  swappedOccurrenceCorrespondence result = alternate
replaceActualSwapOccurrenceMap result alternate = Refl

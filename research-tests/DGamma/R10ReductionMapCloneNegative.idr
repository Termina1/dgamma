module DGamma.R10ReductionMapCloneNegative

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import Decidable.Equality

%default total

||| Expected failure before accounting: the reduction map is a recursive-fold
||| projection, not a constructor field.
public export
0 replaceReductionOccurrenceMap :
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  (alternate : ActionRegistrationReplayCorrespondence name key world error value
    original (reducedTrace reduction)) ->
  reductionOccurrenceCorrespondence reduction = alternate
replaceReductionOccurrenceMap reduction alternate = Refl

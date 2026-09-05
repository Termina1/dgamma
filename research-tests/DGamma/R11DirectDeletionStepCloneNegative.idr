module DGamma.R11DirectDeletionStepCloneNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import Decidable.Equality

%default total

||| Expected failure at the erased operational-certificate equality: every old
||| constructor field is reused while only the runtime map is replaced.
public export
0 cloneDeletionStepWithAlternateMap :
  (step : DeletionChainStep name key world error value protocol nameEq keyEq
    trace premises candidate) ->
  (alternate : ActionRegistrationReplayCorrespondence name key world error value
    trace (survivingTrace (deletionResult step))) ->
  DeletionChainStep name key world error value protocol nameEq keyEq
    trace premises candidate
cloneDeletionStepWithAlternateMap
  (MkDeletionChainStep result producer replay occurrences exact external endpoint
    withdrawn classified accounting next shorter) alternate =
      MkDeletionChainStep result producer replay alternate exact external endpoint
        withdrawn classified accounting next shorter

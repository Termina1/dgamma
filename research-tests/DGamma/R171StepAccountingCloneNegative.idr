module DGamma.R171StepAccountingCloneNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import Decidable.Equality

%default total

||| Expected rejection: accounting may not choose a different operational origin.
public export
0 replaceStepAccounting :
  (step : DeletionChainStep name key world error value protocol nameEq keyEq trace premises candidate) ->
  (alternate : CanonicalRegistrationCorrespondence trace (survivingTrace (deletionResult step))
    (endpointWithdrawnGenerations (deletionEndpoint step))) ->
  DeletionChainStep name key world error value protocol nameEq keyEq trace premises candidate
replaceStepAccounting step alternate = { deletionRegistrationAccounting := alternate } step

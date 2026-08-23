module DGamma.R10DeletionStepMapCloneNegative

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import Decidable.Equality

%default total

||| Expected failure: O9's occurrence map is sealed to the named operational
||| deletion fold before it can enter O10's recursive derivation.
public export
0 replaceDeletionStepOccurrenceMap :
  (step : DeletionChainStep name key world error value protocol nameEq keyEq
    trace premises candidate) ->
  (alternate : ActionRegistrationReplayCorrespondence name key world error value
    trace (survivingTrace (deletionResult step))) ->
  deletionOccurrenceCorrespondence step = alternate
replaceDeletionStepOccurrenceMap step alternate = Refl

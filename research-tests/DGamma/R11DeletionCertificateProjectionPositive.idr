module DGamma.R11DeletionCertificateProjectionPositive

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import Decidable.Equality

%default total

||| The sealed O9 runtime map is exactly the operational certificate projection.
public export
0 deletionStepMapIsCertificateProjection :
  (step : DeletionChainStep name key world error value protocol nameEq keyEq
    trace premises candidate) ->
  deletionOccurrenceCorrespondence step = deletionOperationalCorrespondence
    (deletionStepOperationalOccurrenceFoldSpike nameEq keyEq protocol trace
      premises candidate (deletionResult step) (deletionProducerCapital step))
deletionStepMapIsCertificateProjection step =
  deletionOccurrenceCorrespondenceExact step

||| Every survivor occurrence receives a before/episode/after retained-position
||| embedding from the fixed operational certificate.
public export
0 deletionStepEverySurvivorEmbedded :
  (step : DeletionChainStep name key world error value protocol nameEq keyEq
    trace premises candidate) ->
  {action : Action name key value world error} ->
  (occurrence : LocatedActionOccurrence action
    (survivingTrace (deletionResult step))) ->
  DeletionSurvivingOrdinalEmbedding (deletionResult step)
    (locatedActionOrdinal occurrence)
    (locatedActionOrdinal (replayActionOrigin
      (deletionOperationalCorrespondence
        (deletionStepOperationalOccurrenceFoldSpike nameEq keyEq protocol trace
          premises candidate (deletionResult step)
          (deletionProducerCapital step))) occurrence))
deletionStepEverySurvivorEmbedded step occurrence =
  everySurvivingOccurrenceEmbedded
    (deletionStepOperationalOccurrenceFoldSpike nameEq keyEq protocol trace
      premises candidate (deletionResult step) (deletionProducerCapital step))
      occurrence

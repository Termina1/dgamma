module DGamma.R6OccurrenceFoldPositive

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike

%default total

||| External two-step fold: occurrence origins and the composed ordinal equation
||| must remain available to a consumer rather than only inside the producer.
public export
0 twoStepActionOriginExact :
  {source : Transitions sourceFirst sourceFinal} ->
  {middle : Transitions middleFirst middleFinal} ->
  {target : Transitions targetFirst targetFinal} ->
  (left : ActionRegistrationReplayCorrespondence name key world error value
    source middle) ->
  (right : ActionRegistrationReplayCorrespondence name key world error value
    middle target) ->
  {action : Action name key value world error} ->
  (occurrence : LocatedActionOccurrence action target) ->
  replayActionOrigin (composeActionRegistrationReplayCorrespondence left right)
    occurrence = replayActionOrigin left (replayActionOrigin right occurrence)
twoStepActionOriginExact left right occurrence = Refl

public export
0 twoStepGeneratedOriginExact :
  {source : Transitions sourceFirst sourceFinal} ->
  {middle : Transitions middleFirst middleFinal} ->
  {target : Transitions targetFirst targetFinal} ->
  (left : ActionRegistrationReplayCorrespondence name key world error value
    source middle) ->
  (right : ActionRegistrationReplayCorrespondence name key world error value
    middle target) ->
  {child, parent : name} -> {component : Component key value world error} ->
  (occurrence : LocatedGeneratedRegistration child parent component target) ->
  replayGeneratedRegistrationOrigin
    (composeActionRegistrationReplayCorrespondence left right) occurrence =
  replayGeneratedRegistrationOrigin left
    (replayGeneratedRegistrationOrigin right occurrence)
twoStepGeneratedOriginExact left right occurrence = Refl

public export
0 twoStepOrdinalEquationAvailable :
  {source : Transitions sourceFirst sourceFinal} ->
  {middle : Transitions middleFirst middleFinal} ->
  {target : Transitions targetFirst targetFinal} ->
  (left : ActionRegistrationReplayCorrespondence name key world error value
    source middle) ->
  (right : ActionRegistrationReplayCorrespondence name key world error value
    middle target) ->
  {child, parent : name} -> {component : Component key value world error} ->
  (occurrence : LocatedGeneratedRegistration child parent component target) ->
  generationForward
    (replayGenerationRenaming
      (composeActionRegistrationReplayCorrespondence left right))
    (registrationGeneration
      (replayGeneratedRegistrationOrigin
        (composeActionRegistrationReplayCorrespondence left right) occurrence)) =
  registrationGeneration occurrence
twoStepOrdinalEquationAvailable left right occurrence =
  replayGeneratedOrdinalPreserved
    (composeActionRegistrationReplayCorrespondence left right) occurrence

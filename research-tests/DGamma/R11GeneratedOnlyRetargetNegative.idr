module DGamma.R11GeneratedOnlyRetargetNegative

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

public export
0 retargetOnlyGeneratedHalf :
  (correspondence : ActionRegistrationReplayCorrespondence name key world error value
    source replayed) ->
  (alternateGenerated : {child, parent : name} ->
    {component : Component key value world error} ->
    LocatedGeneratedRegistration child parent component replayed ->
    LocatedGeneratedRegistration child parent component source) ->
  ActionRegistrationReplayCorrespondence name key world error value source replayed
retargetOnlyGeneratedHalf correspondence alternateGenerated =
  MkActionRegistrationReplayCorrespondence
    (replayGenerationRenaming correspondence)
    (replayActionOrigin correspondence)
    (replayActionTagPreserved correspondence)
    alternateGenerated
    (replayGeneratedActionOriginCoherent correspondence)
    (replayGeneratedOrdinalPreserved correspondence)

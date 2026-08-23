module DGamma.R8AuthenticationProjectionPositive

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

public export
0 enrichedCapitalAuthenticatesEveryGeneratedOrigin :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  {child, parent : name} ->
  {component : Component key value world error} ->
  (occurrence : LocatedGeneratedRegistration child parent component
    (canonicalTrace (canonicalSchedule capital))) ->
  canonicalToOriginal (canonicalRegistrationTree (canonicalSchedule capital))
    occurrence =
  replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence capital)
    occurrence
enrichedCapitalAuthenticatesEveryGeneratedOrigin capital occurrence =
  canonicalOriginIsReplayOrigin (canonicalRegistrationAuthentication capital)
    occurrence

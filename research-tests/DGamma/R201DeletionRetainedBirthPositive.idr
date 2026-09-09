module DGamma.R201DeletionRetainedBirthPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20DeletionRetainedBirthSpike
import DGamma.CP5O20DeletionRetainedUnloadSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R193VestigialHistoryTransportPositive
import DGamma.R195EndpointRebaseBoundaryPositive
import DGamma.R200DiscardedCoverageBasePositive
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Apply both actual-step producers at the unchanged R193/R195 full
||| present-vestigial packet. Deletion capital and nonselection remain explicit
||| conditional inputs; this fixture does not fabricate a canonical schedule
||| or assert the still-missing birth-relative retained parent closing.
export
0 r201HistoricalNonselectedBirthAndUnloads :
  (protocol : RegistrationProtocol R45Key R45Value Unit String) ->
  (premises : CanonicalizationPremises Nat R45Key Unit String R45Value protocol
    r45NameEq r45KeyEq r193HistoricalClosedTrace) ->
  (candidate : DeletableClosingEpisode Nat R45Key Unit String R45Value
    r45NameEq r45KeyEq r193HistoricalClosedTrace) ->
  (step : DeletionChainStep Nat R45Key Unit String R45Value protocol
    r45NameEq r45KeyEq r193HistoricalClosedTrace premises candidate) ->
  Not (Elem (vestigialGeneration r195MismatchOwnsVestigialRemainder) (selectedRegistrations candidate)) ->
  (O20RetainedGenerationBirth Nat R45Key Unit String R45Value
    (deletionProducerGenerationRenaming (deletionProducerCapital step))
    (vestigialGeneration r195MismatchOwnsVestigialRemainder) (survivingTrace (deletionResult step)),
   O20DeletionRetainedUnloads Nat R45Key Unit String R45Value r45NameEq r45KeyEq
    r193HistoricalClosedTrace candidate (deletionResult step))
r201HistoricalNonselectedBirthAndUnloads protocol premises candidate step outside =
  (o20DeletionRetainedBirth r193HistoricalClosedTrace premises candidate step
     (vestigialGeneration r195MismatchOwnsVestigialRemainder) r200HistoricalDiscardedBirthClassified outside,
   o20DeletionRetainedUnloads Nat R45Key Unit String R45Value protocol r45NameEq r45KeyEq
     r193HistoricalClosedTrace premises candidate (deletionResult step))

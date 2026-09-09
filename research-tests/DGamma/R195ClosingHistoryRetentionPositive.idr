module DGamma.R195ClosingHistoryRetentionPositive

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O20GenerationOnlyHistorySpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R178GeneratedOrchestrationFixtures
import DGamma.R193VestigialHistoryTransportPositive

%default total
%unbound_implicits off

||| The generation event of R193's physically present, genuinely closing
||| original child. Its birth ordinal2 and parent opening ordinal1 are kept.
public export
r195ClosingEvent : RegistrationEvent Nat R45Key Unit String R45Value
r195ClosingEvent = MkRegistrationEvent 1 0 r45Child (MkRegistrationGeneration 1 2)
  (Just (MkRegistrationActivation (MkRegistrationGeneration 0 0) 1)) 0

||| The event stamp is attached to the existing ACTUAL generated occurrence,
||| with the same physical post-birth continuation containing parent Unload.
public export
0 r195ClosingScannedBirth :
  ScannedRegistrationBirth Nat R45Key Unit String R45Value 0
    r193HistoricalClosedTrace r195ClosingEvent
r195ClosingScannedBirth = MkScannedRegistrationBirth
  (generatedRegistrationActionOccurrence r193HistoricalBirth) Refl

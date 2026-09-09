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

||| The recorded parent activation actually closes in the SAME scanned
||| birth's suffix. This uses the existing checked Unload occurrence, not
||| unsupportedness or endpoint inactivity as a substitute.
public export
0 r195ActualClosingDisposition :
  DeletedClosingRegistration r195ClosingEvent
    (afterActionOccurrence (scannedLocatedBirth r195ClosingScannedBirth))
r195ActualClosingDisposition = MkDeletedClosingRegistration
  (MkRegistrationActivation (MkRegistrationGeneration 0 0) 1) Refl
  (ActionOccursLater r178ParentFinish
    (MoreTransitions r178ChildRetire (MoreTransitions r193HistoricalRetire
      (MoreTransitions r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions))))
    (ActionOccursLater r178ChildRetire
      (MoreTransitions r193HistoricalRetire (MoreTransitions r193HistoricalLeave
        (MoreTransitions r193HistoricalUnload NoTransitions)))
      (ActionOccursLater r193HistoricalRetire
        (MoreTransitions r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions))
        (ActionOccursLater r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions)
          (ActionOccursHere r193HistoricalUnload NoTransitions Refl)))))

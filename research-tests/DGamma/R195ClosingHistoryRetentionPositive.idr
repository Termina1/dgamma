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

||| Generation-only retention of the genuine PRESENT vestigial child. The
||| unchanged accepted current map sends child1 to absent2; no right raw-name
||| birth or current-name match is asserted by this closing constructor.
public export
0 r195ClosingHistoryRetained :
  O20GenerationOnlyDisposition Nat R45Key Unit String R45Value identityRegistrationGenerationBijection
    r193HistoricalClosedTrace r193HistoricalClosedTrace (MkRegistrationGeneration 1 2)
r195ClosingHistoryRetained = O20OriginalClosingBirth r195ClosingEvent
  r195ClosingScannedBirth Refl r195ActualClosingDisposition

||| The actual identity replay keeps the original closing disposition and
||| its exact physical birth stamp simultaneously. This is the R193 history
||| fixture, not a canonical pair or a nonempty operational permutation.
export
0 r195ClosingReplayRetention :
  (O20GenerationOnlyDisposition Nat R45Key Unit String R45Value identityRegistrationGenerationBijection
     r193HistoricalClosedTrace r193HistoricalClosedTrace (registrationGeneration r193HistoricalBirth),
   (generationForward (replayGenerationRenaming (identityActionRegistrationReplayCorrespondence r193HistoricalClosedTrace))
      (registrationGeneration (replayGeneratedRegistrationOrigin
        (identityActionRegistrationReplayCorrespondence r193HistoricalClosedTrace) r193HistoricalBirth)) =
      registrationGeneration r193HistoricalBirth))
r195ClosingReplayRetention = o20HistoryReplayAttachment identityRegistrationGenerationBijection
  (identityActionRegistrationReplayCorrespondence r193HistoricalClosedTrace) 1 0 r45Child
  r193HistoricalBirth r195ClosingHistoryRetained

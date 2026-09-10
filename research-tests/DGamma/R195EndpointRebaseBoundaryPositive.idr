module DGamma.R195EndpointRebaseBoundaryPositive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20AllNameSynchronizationSpike
import DGamma.CP5O20HistoryNameTransportSpike
import DGamma.CP5O20EndpointRebaseBoundarySpike
import DGamma.CP5O20PairedRemovalSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R193VestigialHistoryTransportPositive
import DGamma.R192RemovedBirthCurrentNameProbe
import DGamma.R178GeneratedOrchestrationFixtures

%default total
%unbound_implicits off

||| The authentic current map of R193's present-vestigial ORIGINAL history
||| cannot support an exact ALL-name cut. This is not a canonical endpoint
||| pair and does not refute the protected convergence theorem.
export
0 r195VestigialCurrentCutImpossible :
  O20AllNameCut Nat R45Key Unit String R45Value r45NameEq
    (expectedBridgeBijection r193HistoricalSameInputs)
    r193HistoricalClosed r193HistoricalClosed -> Void
r195VestigialCurrentCutImpossible =
  o20CutRejectsPresentAbsent r45NameEq (expectedBridgeBijection r193HistoricalSameInputs)
    r193HistoricalClosed r193HistoricalClosed 1 r45ChildRetired
    (fst r193VestigialCurrentPresence) (snd r193VestigialCurrentPresence)

||| A FULL internal history cut exists at the actual two final scanner
||| environments and the SAME concrete endpoint. The runtime and stamp fields
||| are produced, not assumed; its internal map is identity, not the current map.
public export
0 r195VestigialInternalHistoryCut :
  O20HistoryCut Nat R45Key Unit String R45Value r45NameEq identityRegistrationGenerationBijection
    (leftFinalGenerations r193HistoricalTree) (rightFinalGenerations r193HistoricalTree)
    r193HistoricalClosed r193HistoricalClosed
r195VestigialInternalHistoryCut =
  o20IdentityHistoryCut r45NameEq r193HistoricalClosedTrace r193HistoricalTree

||| Complete original-endpoint rebasing obstruction: accepted same inputs,
||| an owned ALL-name internal history cut, and impossibility of the current-
||| map cut coexist. No independent canonical capital is packaged here.
export
0 r195OriginalEndpointRebaseObstruction :
  (SameOrchestrationModuloGenerated r45NameEq r45KeyEq r193HistoricalClosedTrace r193HistoricalClosedTrace,
   O20HistoryCut Nat R45Key Unit String R45Value r45NameEq identityRegistrationGenerationBijection
     (leftFinalGenerations r193HistoricalTree) (rightFinalGenerations r193HistoricalTree)
     r193HistoricalClosed r193HistoricalClosed,
   (O20AllNameCut Nat R45Key Unit String R45Value r45NameEq
     (expectedBridgeBijection r193HistoricalSameInputs) r193HistoricalClosed r193HistoricalClosed -> Void))
r195OriginalEndpointRebaseObstruction =
  (r193HistoricalSameInputs, r195VestigialInternalHistoryCut, r195VestigialCurrentCutImpossible)

||| The generic mismatch producer returns the FULL vestigial package at the
||| original endpoint of the real fixture. Its discarded/current generation,
||| present retired clean fiber, empty table, no-child and unsupported fields
||| are retained. This is deliberately not an exact canonical ALL-name cut.
export
0 r195MismatchOwnsVestigialRemainder :
  VestigialEndpointGeneration Nat R45Key Unit String R45Value r45NameEq r45KeyEq
    (leftFinalGenerations r193HistoricalTree) (leftDeletedGenerations r193HistoricalTree)
    1 r193HistoricalClosed
r195MismatchOwnsVestigialRemainder =
  o20DisagreementVestigial r45NameEq r45KeyEq r193HistoricalClosedTrace r193HistoricalClosedTrace
    identityRegistrationGenerationBijection r193HistoricalTree r193HistoricalCurrent 1 (MkRegistrationGeneration 1 2)
    (vestigialGenerationCurrent r193HistoricalVestigial) r193VestigialHistoryMismatch

||| The native six-edge REMOVED child case supplies actual lookup absence,
||| not a fabricated present vestigial packet. Its final state is the exact
||| R192 checked Remove endpoint and the finite deletion theorem owns absence.
export
0 r195RemovedRemainderActuallyAbsent :
  (lookupFiber {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String} @{r45NameEq}
    1 (registry r192RemovedBirthFinal) = Nothing)
r195RemovedRemainderActuallyAbsent =
  o20DeletedLookupAbsent r45NameEq 1 (registry r178RightFinal)

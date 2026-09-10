module DGamma.R206ChronologyPairingPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20GlobalActivationHistorySpike
import DGamma.CP5O20ChronologyPairingSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R178GeneratedOrchestrationFixtures
import DGamma.R192RemovedBirthCurrentNameProbe
import DGamma.R193VestigialHistoryTransportPositive
import Prelude.Types
import Prelude.Basics
import Prelude.EqOrd
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Concrete retained original event: later child removal does not close its
||| parent activation. These coordinates are checked against the real scan next.
public export
r206RemovedEvent : RegistrationEvent Nat R45Key Unit String R45Value
r206RemovedEvent = MkRegistrationEvent 1 0 r45Child (MkRegistrationGeneration 1 2)
  (Just (MkRegistrationActivation (MkRegistrationGeneration 0 0) 1)) 0

||| A genuine nonempty six-edge native trace pair; no independently chosen
||| event lists or pair matches enter the producer application.
public export
0 r206RemovedChronologies :
  O20PairedNativeChronologies Nat R45Key Unit String R45Value r45NameEq
    identityRegistrationGenerationBijection r192RemovedBirthTrace r192RemovedBirthTrace
    (leftFinalIndex r192RemovedBirthTree) (rightFinalIndex r192RemovedBirthTree)
r206RemovedChronologies = o20AcceptedChronologyPairing r45NameEq
  r192RemovedBirthTrace r192RemovedBirthTrace identityRegistrationGenerationBijection r192RemovedBirthTree

||| BOTH produced words are the actual retained event, not arbitrary singleton
||| placeholders. Pairing proves equal event counts; the real trace has6 edges.
export
0 r206RemovedWholeWords :
  (leftChronology r206RemovedChronologies = [r206RemovedEvent],
   rightChronology r206RemovedChronologies = [r206RemovedEvent],
   length (leftChronology r206RemovedChronologies) = length (rightChronology r206RemovedChronologies),
   transitionCount r192RemovedBirthTrace = 6)
r206RemovedWholeWords =
  (Refl, Refl, o20ChronologyPairingLength (chronologyPairing r206RemovedChronologies), Refl)

||| Both occurrence-to-occurrence matching witnesses are PRODUCED from the
||| full paired lists. No preselected event-match hypothesis is supplied.
export
0 r206RemovedBilateralCoverage :
  ((other : RegistrationEvent Nat R45Key Unit String R45Value **
     (Elem other (rightChronology r206RemovedChronologies),
      RegistrationEventMatch identityRegistrationGenerationBijection r206RemovedEvent other)),
   (other : RegistrationEvent Nat R45Key Unit String R45Value **
     (Elem other (leftChronology r206RemovedChronologies),
      RegistrationEventMatch identityRegistrationGenerationBijection other r206RemovedEvent)))
r206RemovedBilateralCoverage =
  (o20ChronologyLeftCovered (chronologyPairing r206RemovedChronologies) r206RemovedEvent Here,
   o20ChronologyRightCovered (chronologyPairing r206RemovedChronologies) r206RemovedEvent Here)

||| Apply both whole original-prefix position proofs and both actual final
||| counter equations to the SAME complete paired words produced above.
export
0 r206RemovedPositionsAndCounts :
  (o20ChronologicalPositions r45NameEq (leftChronology r206RemovedChronologies) [],
   o20ChronologicalPositions r45NameEq (rightChronology r206RemovedChronologies) [],
   indexedSurvivingChildCounts (leftFinalIndex r192RemovedBirthTree) =
     o20ReplayRetainedEventCounts r45NameEq (leftChronology r206RemovedChronologies) [],
   indexedSurvivingChildCounts (rightFinalIndex r192RemovedBirthTree) =
     o20ReplayRetainedEventCounts r45NameEq (rightChronology r206RemovedChronologies) [])
r206RemovedPositionsAndCounts = o20PairedChronologyPositionsAndCounts r45NameEq identityRegistrationGenerationBijection
  r192RemovedBirthTrace r192RemovedBirthTrace (leftFinalIndex r192RemovedBirthTree) (rightFinalIndex r192RemovedBirthTree)
  r206RemovedChronologies

||| Actual eight-edge closing history exercises BOTH deleted-birth branches.
||| The scanner keeps physical steps while excluding the closed activation's
||| registration from retained-event matching.
public export
0 r206ClosedChronologies :
  O20PairedNativeChronologies Nat R45Key Unit String R45Value r45NameEq
    identityRegistrationGenerationBijection r193HistoricalClosedTrace r193HistoricalClosedTrace
    (leftFinalIndex r193HistoricalTree) (rightFinalIndex r193HistoricalTree)
r206ClosedChronologies = o20AcceptedChronologyPairing r45NameEq
  r193HistoricalClosedTrace r193HistoricalClosedTrace identityRegistrationGenerationBijection r193HistoricalTree

||| Positive/negative native control: both retained words are empty, but the
||| ACTUAL source path has8 edges and cannot be treated as a zero physical gap.
export
0 r206DeletedSkipsArePhysical :
  (leftChronology r206ClosedChronologies = [],
   rightChronology r206ClosedChronologies = [],
   transitionCount r193HistoricalClosedTrace = 8,
   Not (transitionCount r193HistoricalClosedTrace = Z))
r206DeletedSkipsArePhysical =
  (Refl, Refl, Refl, (\zero => case zero of Refl impossible))

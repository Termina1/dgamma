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

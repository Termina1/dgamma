module DGamma.R204NativeChronologicalBirthPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5O20GlobalActivationHistorySpike
import DGamma.CP5O20ChronologicalOccurrenceHistorySpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R178GeneratedOrchestrationFixtures
import DGamma.R192RemovedBirthCurrentNameProbe
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Six actual native edges, including child Retire and Remove. The retained
||| event still yields its real birth and open parent suffix through the new
||| chronology producer. Ordinal TWO is derived from the produced stamp, not
||| supplied as an occurrence-position premise. Current endpoint absence does
||| not erase this original runtime birth or supply a canonical skip witness.
export
0 r204RemovedEventOwnsOriginalBirth :
  (birth : ScannedRegistrationBirth Nat R45Key Unit String R45Value Z r192RemovedBirthTrace
    (MkRegistrationEvent 1 0 r45Child (MkRegistrationGeneration 1 2)
      (Just (MkRegistrationActivation (MkRegistrationGeneration 0 0) 1)) 0) **
    (SurvivingRegistration
      (MkRegistrationEvent 1 0 r45Child (MkRegistrationGeneration 1 2)
        (Just (MkRegistrationActivation (MkRegistrationGeneration 0 0) 1)) 0)
      (afterActionOccurrence (scannedLocatedBirth birth)),
     locatedActionOrdinal (scannedLocatedBirth birth) = 2))
r204RemovedEventOwnsOriginalBirth =
  case o20NativeChronologicalBirth Nat R45Key Unit String R45Value r45NameEq Z emptyRegistrationIndex
    r192RemovedBirthTrace (leftFinalIndex r192RemovedBirthTree)
    (fst (o20LeftNativeActivationHistory (generationTraceCorrespondence r192RemovedBirthTree)))
    (snd (o20LeftNativeActivationHistory (generationTraceCorrespondence r192RemovedBirthTree)))
    (MkRegistrationEvent 1 0 r45Child (MkRegistrationGeneration 1 2)
      (Just (MkRegistrationActivation (MkRegistrationGeneration 0 0) 1)) 0) Here of
    (birth ** retained) =>
      (birth ** (retained, sym (cong generationBirthOrdinal (scannedBirthStampExact birth))))

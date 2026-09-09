module DGamma.R203GlobalActivationHistoryPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20GlobalActivationHistorySpike
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

||| Actual eight-edge bilateral history, with a real generated birth and a
||| later parent Unload. BOTH derived chronological words are empty, and the
||| global counter theorem contributes no surviving position for that birth.
||| This is not an empty native trace or a supplied classifier/counter equation.
export
0 r203ClosedBirthConsumesNoRetainedPosition :
  (fst (o20AcceptedActivationHistories r45NameEq r193HistoricalClosedTrace r193HistoricalClosedTrace
      identityRegistrationGenerationBijection r193HistoricalTree) = [],
   fst (snd (o20AcceptedActivationHistories r45NameEq r193HistoricalClosedTrace r193HistoricalClosedTrace
      identityRegistrationGenerationBijection r193HistoricalTree)) = [],
   indexedSurvivingChildCounts (leftFinalIndex r193HistoricalTree) = [],
   transitionCount r193HistoricalClosedTrace = 8)
r203ClosedBirthConsumesNoRetainedPosition =
  (Refl, Refl,
   o20NativeActivationCounts r45NameEq Z emptyRegistrationIndex r193HistoricalClosedTrace
     (leftFinalIndex r193HistoricalTree)
     (fst (o20LeftNativeActivationHistory (generationTraceCorrespondence r193HistoricalTree)))
     (snd (o20LeftNativeActivationHistory (generationTraceCorrespondence r193HistoricalTree))), Refl)

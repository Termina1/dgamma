module DGamma.R204NativeDiscardedOriginPositive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20GlobalActivationHistorySpike
import DGamma.CP5O20DiscardedBirthOriginSpike
import DGamma.CP5O20ChainCurrentDisappearanceSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R178GeneratedOrchestrationFixtures
import DGamma.R193VestigialHistoryTransportPositive
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Eight native edges on EACH accepted original side. Both classifications
||| are produced by traversing R203's actual chronologies backwards from the
||| native discarded membership, not by supplying the known closing birth.
||| No independent canonical capital or actual chain is fabricated here.
export
0 r204BothOriginalDiscardedBirths :
  (DeletedGenerationClassification Nat R45Key Unit String R45Value r45NameEq
     r193HistoricalClosedTrace (MkRegistrationGeneration 1 2),
   DeletedGenerationClassification Nat R45Key Unit String R45Value r45NameEq
     r193HistoricalClosedTrace (MkRegistrationGeneration 1 2))
r204BothOriginalDiscardedBirths =
  case o20AcceptedActivationHistories r45NameEq r193HistoricalClosedTrace r193HistoricalClosedTrace
    identityRegistrationGenerationBijection r193HistoricalTree of
    (leftEvents ** (rightEvents ** (leftScan, rightScan, leftPositions, rightPositions, leftCounts, rightCounts))) =>
      (o20DiscardedOriginClassified Nat R45Key Unit String R45Value r45NameEq
        r193HistoricalClosedTrace (MkRegistrationGeneration 1 2)
        (o20NativeDiscardedOrigin Nat R45Key Unit String R45Value r45NameEq Z emptyRegistrationIndex
          r193HistoricalClosedTrace (leftFinalIndex r193HistoricalTree) leftEvents leftScan (MkRegistrationGeneration 1 2) Here),
       o20DiscardedOriginClassified Nat R45Key Unit String R45Value r45NameEq
        r193HistoricalClosedTrace (MkRegistrationGeneration 1 2)
        (o20NativeDiscardedOrigin Nat R45Key Unit String R45Value r45NameEq Z emptyRegistrationIndex
          r193HistoricalClosedTrace (rightFinalIndex r193HistoricalTree) rightEvents rightScan (MkRegistrationGeneration 1 2) Here))

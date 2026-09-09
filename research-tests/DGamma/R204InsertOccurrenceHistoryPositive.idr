module DGamma.R204InsertOccurrenceHistoryPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20StampedHistoryFoldSpike
import DGamma.CP5O20OccurrenceStampedHistorySpike
import DGamma.CP5O20InsertOccurrenceHistorySpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R178GeneratedOrchestrationFixtures
import DGamma.R193VestigialHistoryTransportPositive
import DGamma.R200DiscardedCoverageBasePositive
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| A genuine native birth history inside BOTH eight-edge accepted ORIGINAL
||| traces. The actual two labelled Insert cuts produce the runtime stage;
||| neither that stage nor its action/tag laws are fixture assumptions.
||| Later parent closure does not make this birth an epsilon transition.
public export
0 r204OriginalBirthOccurrenceHistory :
  O20OccurrenceStampedHistory Nat R45Key Unit String R45Value r45NameEq r45KeyEq
    identityRegistrationGenerationBijection identityNameBijection
    r193HistoricalClosedTrace r193HistoricalClosedTrace
    [(0, MkRegistrationGeneration 0 0)] [(0, MkRegistrationGeneration 0 0)]
    [(0, MkRegistrationGeneration 0 0), (1, MkRegistrationGeneration 1 2)]
    [(0, MkRegistrationGeneration 0 0), (1, MkRegistrationGeneration 1 2)]
    r45AfterBegin r45AfterBegin r45SourcePairFinal r45SourcePairFinal
r204OriginalBirthOccurrenceHistory =
  o20LocatedInsertOccurrenceHistory r45NameEq r45KeyEq identityNameBijection
    r193HistoricalClosedTrace r193HistoricalClosedTrace r200HistoricalAligned r200HistoricalAligned
    1 r45Child (ChildOf 0) (ChildOf 0) (ChildrenRelated Refl)
    (generatedRegistrationActionOccurrence r193HistoricalBirth)
    (generatedRegistrationActionOccurrence r193HistoricalBirth) Refl
